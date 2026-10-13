"""Bounded validation for diagnostics requests; does not change proof trust."""
import re

MAX_MODULES = 384
MAX_SOURCE_CHARS = 300_000
MAX_TOTAL_BYTES = 8 * 1024 * 1024
PATH = re.compile(r'(?:[A-Za-z_][A-Za-z_0-9]*/)*[A-Za-z_][A-Za-z_0-9]*\.lean')
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')

def validate_request(request: object) -> None:
    if not isinstance(request, dict):
        raise ValueError('Request must be a JSON object')
    serial = request.get('serial')
    if type(serial) is not int or serial < 0:
        raise ValueError('Nonnegative integer serial required')
    if request.get('stop') is True:
        return
    files, modules = request.get('files', {}), request.get('modules', [])
    if not isinstance(files, dict) or not isinstance(modules, list):
        raise ValueError('files must be a dictionary and modules a list')
    if len(files) > MAX_MODULES or len(modules) > MAX_MODULES:
        raise ValueError(f'Request exceeds {MAX_MODULES} modules')
    total = 0
    for name, text in files.items():
        if not isinstance(name, str) or PATH.fullmatch(name) is None:
            raise ValueError('Unsafe Lean path')
        if not isinstance(text, str) or len(text) > MAX_SOURCE_CHARS:
            raise ValueError('Invalid or excessive source text')
        total += len(text.encode('utf-8'))
    if total > MAX_TOTAL_BYTES:
        raise ValueError('Aggregate source byte limit exceeded')
    for module in modules:
        if not isinstance(module, str) or MODULE.fullmatch(module) is None:
            raise ValueError('Invalid module name')
    if len(set(modules)) != len(modules):
        raise ValueError('Duplicate module')
