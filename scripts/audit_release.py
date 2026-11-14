#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0-only
"""Verify packaged inputs, dependency pins, theorem types and all local axioms."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FINAL = (
    "StrongSilver.silver_rate_lower_bound",
    "StrongSilver.silver_rate_lower_bound_explicit",
    "StrongSilver.silver_rate_lower_bound_horizon",
)


def strip_comments(source):
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif not depth and source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0:
                break
            out.append(' ' * (end-i))
            i = end
        else:
            out.append(source[i] if not depth or source[i] == '\n' else ' ')
            i += 1
    if depth:
        raise RuntimeError('Unclosed Lean block comment')
    return ''.join(out)


def check_inputs():
    manifest = json.loads((ROOT/'RELEASE_INPUTS.json').read_text())
    if manifest['original_code_license'] != 'GPL-3.0-only':
        raise RuntimeError('Unexpected original-code license')
    expected = manifest['sha256']
    actual = set()
    ignored = {'.git', '.lake', 'verification', '__pycache__'}
    for directory, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = [name for name in dirs if name not in ignored]
        for name in dirs+files:
            path = Path(directory)/name
            if path.is_symlink():
                raise RuntimeError(f'Unexpected packaged symbolic link: {path.relative_to(ROOT)}')
        for name in files:
            path = Path(directory)/name
            if path.name != 'RELEASE_INPUTS.json':
                actual.add(str(path.relative_to(ROOT)))
    if actual != set(expected):
        raise RuntimeError(f'Packaged inventory mismatch: missing={sorted(set(expected)-actual)}, extra={sorted(actual-set(expected))}')
    for relative, digest in expected.items():
        if hashlib.sha256((ROOT/relative).read_bytes()).hexdigest() != digest:
            raise RuntimeError(f'Packaged input changed: {relative}')
    lean = {name for name in expected if name.endswith('.lean')}
    sources = {name: strip_comments((ROOT/name).read_text()) for name in lean}
    for name in lean:
        if not (ROOT/name).read_text().startswith('-- SPDX-License-Identifier: GPL-3.0-only\n'):
            raise RuntimeError(f'Missing source license: {name}')
    own = {name for name in lean if name == 'StrongSilver.lean' or name.startswith('StrongSilver/')}
    forbidden = re.compile(r'\b(sorry|admit|axiom|sorryAx|native_decide|unsafe|implemented_by|extern)\b|debug\.skipKernelTC')
    for name in own:
        if forbidden.search(sources[name]):
            raise RuntimeError(f'Forbidden proof shortcut in {name}')
    visited = set()
    def visit(module):
        filename = module.replace('.', '/')+'.lean'
        if filename in visited:
            return
        if filename not in own:
            raise RuntimeError(f'Missing local module: {module}')
        visited.add(filename)
        for dependency in re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', sources[filename], re.M):
            if dependency == 'StrongSilver' or dependency.startswith('StrongSilver.'):
                visit(dependency)
            elif not dependency.startswith('Mathlib.'):
                raise RuntimeError(f'Unexpected import: {dependency} in {filename}')
    visit('StrongSilver')
    if visited != own:
        raise RuntimeError(f'Unreachable local modules: {sorted(own-visited)}')
    citation = (ROOT/'CITATION.cff').read_text()
    if not re.search(r'^license:\s*GPL-3\.0-only\s*$', citation, re.M):
        raise RuntimeError('CITATION license mismatch')
    if 'GPL-3.0-only' not in (ROOT/'README.md').read_text():
        raise RuntimeError('README license mismatch')
    if (ROOT/'LICENSE').read_text().count('GNU GENERAL PUBLIC LICENSE') < 1:
        raise RuntimeError('Missing GPL text')
    return len(own), len(lean), hashlib.sha256((ROOT/'RELEASE_INPUTS.json').read_bytes()).hexdigest()


def check_dependencies():
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    pins = {}
    for package in manifest['packages']:
        directory = ROOT/manifest['packagesDir']/package['name']
        head = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
        if head != package['rev']:
            raise RuntimeError(f'Dependency revision mismatch: {package["name"]}')
        dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'], text=True)
        if dirty:
            raise RuntimeError(f'Tracked dependency source changed: {package["name"]}')
        notice = ROOT/'third_party/licenses'/package['name']/'LICENSE'
        if notice.read_bytes() != (directory/'LICENSE').read_bytes():
            raise RuntimeError(f'Dependency license notice changed: {package["name"]}')
        pins[package['name']] = head
    return pins


def run(command, log):
    with log.open('w') as output:
        result = subprocess.run(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Exit {result.returncode}: {command}; see verification/{log.name}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-inputs-only', action='store_true')
    args = parser.parse_args()
    modules, lean_files, digest = check_inputs()
    if args.check_inputs_only:
        print(f'PASS: packaged hashes, licenses and complete {modules}-module local source closure.')
        return
    logs = ROOT/'verification'
    logs.mkdir(exist_ok=True)
    status = {'passed': False}
    status_path = logs/'status.json'
    status_path.write_text(json.dumps(status)+'\n')
    try:
        pins = check_dependencies()
        run(['lake', 'env', 'lean', 'Audit.lean'], logs/'all-axioms.log')
        run(['lake', 'env', 'lean', 'MainAudit.lean'], logs/'declarations-and-axioms.log')
        output = (logs/'all-axioms.log').read_text()
        marker = re.search(r'STRONG_SILVER_AUDIT_OK declarations=(\d+) theorems=(\d+)', output)
        if not marker:
            raise RuntimeError('Missing complete declaration audit marker')
        records = re.findall(r'STRONG_SILVER_AXIOMS ([^: \n]+): \[([^\]]*)\]', output)
        dependencies = {name: [a.strip() for a in axioms.split(',') if a.strip()] for name, axioms in records}
        if len(records) != int(marker[2]) or len(dependencies) != len(records):
            raise RuntimeError('Axiom records do not cover all local theorems')
        if not set(FINAL) <= set(dependencies):
            raise RuntimeError('A final theorem is missing from the audit')
        used = {a for axioms in dependencies.values() for a in axioms}
        if used-ALLOWED:
            raise RuntimeError(f'Unexpected axioms: {sorted(used-ALLOWED)}')
        final_output = (logs/'declarations-and-axioms.log').read_text()
        for name in FINAL:
            if f"'{name}' depends on axioms:" not in final_output:
                raise RuntimeError(f'Final declaration axiom output missing: {name}')
        status = {
            'passed': True,
            'verified_at': datetime.now(timezone.utc).isoformat(),
            'original_code_license': 'GPL-3.0-only',
            'local_module_count': modules,
            'checked_lean_file_count': lean_files,
            'checked_declaration_count': int(marker[1]),
            'checked_theorem_count_including_generated': int(marker[2]),
            'axioms_used': sorted(used),
            'proof_hole_axioms': [],
            'native_computation_axioms': [],
            'other_unexpected_axioms': [],
            'final_theorem_axioms': {name: dependencies[name] for name in FINAL},
            'dependency_revisions': pins,
            'release_inputs_sha256': digest,
            'theorems': dependencies,
        }
        print(f'PASS: {modules} local modules; {marker[1]} declarations; {marker[2]} theorems.')
        print('Allowed axioms used: '+', '.join(sorted(used)))
        print('Proof-hole, native-computation and other unexpected axioms: [].')
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        status['error'] = str(error)
        raise
    finally:
        status_path.write_text(json.dumps(status, indent=2)+'\n')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
