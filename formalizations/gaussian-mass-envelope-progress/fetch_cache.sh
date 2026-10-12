#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake exe cache get   Mathlib.Probability.Distributions.Gaussian.Multivariate   Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence   Mathlib.Probability.Independence.Integration   Mathlib.MeasureTheory.Integral.IntegralEqImproper   Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap   Mathlib.Analysis.Calculus.Deriv.MeanValue   Mathlib.Analysis.SpecialFunctions.Log.Deriv   Mathlib.Topology.Order.IntermediateValue   Mathlib.Tactic
