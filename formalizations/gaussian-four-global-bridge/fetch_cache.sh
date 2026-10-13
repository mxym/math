#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake exe cache get \
  Mathlib.Analysis.Calculus.LocalExtr.Basic \
  Mathlib.Analysis.Calculus.ParametricIntegral \
  Mathlib.Analysis.SpecialFunctions.Integrals.Basic \
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan \
  Mathlib.Data.Fintype.Lattice \
  Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap \
  Mathlib.MeasureTheory.Integral.Bochner.Set \
  Mathlib.MeasureTheory.Integral.DominatedConvergence \
  Mathlib.MeasureTheory.Measure.OpenPos \
  Mathlib.Probability.Distributions.Gaussian.Multivariate \
  Mathlib.Tactic.FieldSimp \
  Mathlib.Tactic.Linarith \
  Mathlib.Tactic.Positivity \
  Mathlib.Topology.Connected.TotallyDisconnected \
  Mathlib.Topology.Order.Compact \
  Mathlib.Topology.Order.Lattice
