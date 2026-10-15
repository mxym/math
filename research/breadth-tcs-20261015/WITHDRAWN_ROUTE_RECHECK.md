# Rechecking two withdrawn routes against explicit controls

15 October 2026. Yongxian Zhang (张永贤), South China University of
Technology. No external funding. OpenAI AI assistants assisted. Original
material all rights reserved; third-party rights retained.

**Status:** author-only route controls. Both source claims were already
withdrawn; no new major result, novelty priority or original-target
counterexample is asserted.

## The frequency-one deletion premise

[2603.23561v1, Lemma 2](https://arxiv.org/html/2603.23561v1) requires a
size-d restriction uniquely identifying some concept at each deletion
stage. The known Warmuth VC-two class has no such size-two restriction:
every concept has teaching dimension three. The process already stalls
at its first stage. The [current metadata](https://arxiv.org/abs/2603.23561)
explicitly withdraws the claim for a wrong Lemma 2 proof. Reading its
construction does not supply a positive compression theorem.

## Testing an improper repair of the sample-dependent recursion

[2201.04131v1, Proposition 3.2](https://arxiv.org/html/2201.04131v1)
uses an ambiguity subclass H*_S depending on the whole sample; its decoder
instead sees only the compressed T. The [current metadata](https://arxiv.org/abs/2201.04131)
already marks that proposition invalid.

Allowing improper output does not repair this prescribed compressor.
Take C={3,6,11,12,13,17,21,22,24,26} and increasing coordinate order.
In (domain mask,label mask) notation, use S1=(15,3) and S2=(23,18).
Both compress to T=((1,1),(2,0)). Their coordinate-zero labels are
respectively one and zero, so NO single total hypothesis can cover both.

The first coordinate is entailed by the tail in both samples and is
dropped. The next recursive ambiguity classes are respectively
{3,6,11,22,26} and {6,22,26}; after retaining (2,0), they become {3}
and {26}. The remaining tail then has dimension zero. These steps give
the identical T explicitly. Both S1 and S2 are C-realizable, by 3 and
26. The complete table control is WITHDRAWN_COMPRESSOR_REPAIR_CONTROL.json.

This only excludes the prescribed recursion, including its improper
repair. C itself has a checked general size-two scheme. SC0 remains open.
