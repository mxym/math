#!/usr/bin/env python3
"""Adversarial controls for diagnostic guards; these are not mathematical proofs."""
from verify_pyramid import axiom_items, uncomment, require

valid = "'t' depends on axioms: [propext, Classical.choice, Quot.sound]"
require(set(axiom_items(valid)['t']) == {'propext', 'Classical.choice', 'Quot.sound'}, 'Valid audit rejected')
require(axiom_items("'t' does not depend on any axioms") == {'t': set()}, 'Empty axiom audit rejected')
bad = ["'t' depends on axioms: [sorryAx]", "'t' depends on axioms: [Geometry.assumption]",
       "'t' depends on axioms: [Lean.ofReduceBool]", valid + '\n' + valid,
       valid + '\nerror: proof failed', valid + '\nwarning: skipped proof']
for text in bad:
    try:
        axiom_items(text)
    except RuntimeError:
        continue
    raise RuntimeError('Invalid audit accepted: ' + text)
require(uncomment('/- outer /- inner -/ end -/theorem t -- tail\n').lstrip() == 'theorem t \n', 'Nested comment parser incorrect')
try:
    uncomment('/- unclosed')
except RuntimeError:
    pass
else:
    raise RuntimeError('Unclosed block comment accepted')
print('PYRAMID_GUARD_CONTROLS_PASS 10 cases; explicit failures remain active under Python -O')
