#!/usr/bin/env python3
"""Map every new exported proof to inspected paper statements and actual types."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]
MODULE_MAP = {
 'TruncationSimplexVolume': ('Official OpenAI/math SimplexVolume.lean', 'Exact eight upstream simplex-volume proofs; auxiliary actual Lebesgue-volume foundation.'),
 'TruncationDefinitions': ('Truncation paper (3)', 'Actual coordinate vertices and barycentric expressions; definitions only.'),
 'TruncationGeometry': ('Truncation paper (3); sharp note Sharpness section', 'Actual convex hull, compact convex body and nonempty interior.'),
 'TruncationConvexDeterminant': ('Truncation paper proof of (7)', 'Separate affinity of actual augmented determinant and convex-hull extension of vertex bounds.'),
 'TruncationMaximum': ('Truncation paper (7); sharp note Sharpness section', 'Actual global maximum inscribed simplex; bounds arbitrary inscribed point tuples, not only vertex simplices.'),
 'TruncationCentroid': ('Truncation paper (9), specialized to p=e_i; sharp note Sharpness section', 'Actual original-centroid dilation coordinates and exact literal sInf excess (d+1)t for the chosen maximum.'),
 'TruncationVolume': ('Truncation paper proof of (4)-(5); sharp note eq:truncation', 'Actual body volume (1-t^d)/d! and measure-zero shared boundary of removed cap.'),
 'TruncationFacetGeometry': ('Truncation paper proof of (4)-(5); sharp note Sharpness facet vectors', 'Actual unit normals, halfspace representation, top and bottom intrinsic facet areas.'),
 'TruncationCoordinateFacets': ('Truncation paper proof of (4)-(5); sharp note Sharpness facet vectors', 'Actual coordinate facet chart, explicit Euclidean isometry and intrinsic area (1-t^(d-1))/(d-1)!.'),
 'TruncationFacetVectors': ('Truncation paper proof of (4)-(5); sharp note Sharpness facet vectors', 'Actual area-normal and area-support products; signed bottom support retained as geometric data.'),
 'TruncationFacetTranslation': ('Sharp note paragraph after eq:truncation', 'Actual translated halfspace carriers and intrinsic facet-area translation invariance.'),
 'TruncationCenteredHalfspaces': ('Sharp note paragraph after eq:truncation', 'Explicit interior translation, proved positive heights, injective normals, true volume and entryA/defect invariance.'),
 'TruncationFacetFormula': ('Sharp note a=Ldet/(d|K|Hdet); entry005 finite pyramid mechanism', 'Actual finite-halfspace entryA equals ordered facet determinant ratio; geometric cone/pyramid/projection dependencies already proved.'),
 'TruncationFacetDeterminants': ('Sharp note Hdet and Ldet displays; truncation proof of (4)-(5)', 'Arbitrary-d determinant minor identities and complete ordered tuple sums, with factorial multiplicities derived.'),
 'TruncationScalarCancellation': ('Truncation paper (5); sharp note eq:truncation', 'Pure scalar cancellation of the proved H/L expressions; positivity and factorial cancellation proved.'),
 'TruncationActualDefect': ('Truncation paper (5); sharp note eq:truncation', 'Actual translation shear, facet reindexing and exact actual entryDefect rational formula without a geometric premise.'),
 'TruncationRationalDefect': ('Truncation paper (5)-(6); sharp note eq:truncation', 'Scalar rational coefficient positivity and exact analytic asymptotic; this module alone does not identify actual geometric defect.'),
 'TruncationPower': ('Truncation paper cor:power; sharp note Sharpness section', 'Scalar exponent obstruction. Conditional supplied-function helpers retain their explicitly displayed equality premise.'),
 'TruncationSharpnessAssembly': ('Literal Targets.truncationSharpnessGoal; sharp note Sharpness section', 'Transparent conditional assembly helper and joint genuine maximum/original-centroid excess statement.'),
 'TruncationSharpness': ('Literal Targets.truncationSharpnessGoal; truncation paper cor:power; sharp note Sharpness section', 'Full unconditional literal sharpness target, actual defect positivity and actual geometric asymptotic.'),
 'TruncationProjection': ('Truncation paper actual projection calculation; sharp note Sharpness facet mechanism', 'Actual projection body and every-unit-direction actual projection volume, not a substitute zonotope definition.'),
 'TruncationSimplexActualVolume': ('Truncation paper (7)', 'Actual selected simplex volume (1-t)/d!, independent of the maximum comparison theorem.'),
 'TruncationFormalization': ('Release import closure', 'All delivered mathematical mechanisms; imports only.'),
}

def main():
    verification = json.loads((ROOT / 'logs/truncation-verification.json').read_text())
    output = (ROOT / 'logs/truncation-all-statements-axioms.log').read_text()
    inventory = json.loads((ROOT / 'sources/truncation-public-by-module.json').read_text())
    rows = []
    for source, names in inventory.items():
        path = ROOT / source
        text = path.read_text()
        module = path.stem
        paper, statement = MODULE_MAP[module]
        for name in names:
            shortname = name.rsplit('.', 1)[1]
            match = re.search(r'^(?:@\[[^\n]+\]\s*)?(?:theorem|lemma)\s+' + re.escape(shortname) + r'\b', text, re.M)
            declaration = text[match.start():].split(':=', 1)[0].strip()
            marker = "'" + name + "' depends on axioms:"
            end = output.index(marker)
            checkstart = output.rfind('\n' + name, 0, end)
            if checkstart < 0 and output.startswith(name):
                checkstart = -1
            compiled = output[checkstart + 1:end].strip()
            if not compiled.startswith(name):
                raise RuntimeError('Missing literal compiled type for ' + name)
            conditional = ('conditional_' in shortname or
                           shortname == 'truncation_sharpness_from_actual_defect_formula')
            rows.append({
                'lean_theorem': name,
                'source': source,
                'source_line': text[:match.start()].count('\n') + 1,
                'paper_reference': paper,
                'statement_mapping': statement,
                'all_assumptions_and_conclusion_lean_source': declaration,
                'literal_compiled_signature': compiled,
                'axioms': verification['axioms_by_new_theorem'][name],
                'direct_module_imports': re.findall(r'^import\s+(\S+)', text, re.M),
                'upstream_reuse': 'Exact unchanged OpenAI/math proof body' if module == 'TruncationSimplexVolume' else 'New public proof body in this increment',
                'conditional_helper': conditional,
                'unformalized_dependencies': [],
                'coverage_limit': ('The displayed pointwise geometric/scalar equality is a theorem premise; this helper alone is not a full geometric proof. The final truncationSharpness discharges it with truncation_entryDefect_exact.' if conditional else
                                   'Scope is exactly the displayed compiled type; module-level paper mapping does not extend its quantified domain or conclusion.'),
            })
    result = {
        'paper_provenance': json.loads((ROOT / 'sources/provenance.json').read_text()),
        'actual_literal_target': 'Entry005.truncationSharpness : Entry005.truncationSharpnessGoal',
        'unchanged_target_sha256': '8bc873bff65384b67b05d3d4fd405bdf9c728e0befb0e6ac355373fa3ded7c94',
        'new_public_proof_count': len(rows),
        'exact_upstream_public_proof_bodies': 8,
        'new_public_proof_bodies': len(rows) - 8,
        'unformalized_dependencies_for_literal_sharpness': [],
        'outside_release_scope': [
            'Full prescribed maximum-simplex upper-bound stability Main and its explicit global constants',
            'Classification of every maximum S_p, formula (9) for arbitrary p and infimum over all maxima in (10)',
            'Banach-Mazur distance estimates (11), best-maximum sharp constant and Rogers-Shephard obstruction proposition',
            'Geometric equality classification for the complete entry005 paper',
        ],
        'theorems': rows,
    }
    (ROOT / 'coverage.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Coverage maps {len(rows)} theorem names to paper statements, literal types and actual axiom closures')

if __name__ == '__main__':
    main()
