/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Basic
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Cylinder
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.CylinderContent
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.FiniteProjection
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integrable
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.InverseLimit
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Probability
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerCylinder
public import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerIntegral
public import ArakelovGeometry.AdelicCurve.Extension.Automorphism
public import ArakelovGeometry.AdelicCurve.Extension.BoundedEvaluationGenerators
public import ArakelovGeometry.AdelicCurve.Extension.FibreMaximum
public import ArakelovGeometry.AdelicCurve.Extension.Finite.BaseChange
public import ArakelovGeometry.AdelicCurve.Extension.Finite.Construction
public import ArakelovGeometry.AdelicCurve.Extension.Finite.Probability
public import ArakelovGeometry.AdelicCurve.Extension.Finite.Tower
public import ArakelovGeometry.AdelicCurve.Extension.FiniteIntermediateField
public import ArakelovGeometry.AdelicCurve.Extension.InvariantMaximum
public import ArakelovGeometry.AdelicCurve.Extension.ParameterSpace
public import ArakelovGeometry.AdelicCurve.Extension.PowerSums
public import ArakelovGeometry.AdelicCurve.Extension.RootBounds
public import ArakelovGeometry.AdelicCurve.Extension.Separable.Construction
public import ArakelovGeometry.AdelicCurve.Extension.Separable.Embeddings
public import ArakelovGeometry.AdelicCurve.Extension.Separable.FibreIntegral
public import ArakelovGeometry.AdelicCurve.Extension.Separable.Measurability
public import ArakelovGeometry.AdelicCurve.Extension.Separable.Measure

/-!
# Scalar extensions of adelic structures

Import entry point for Chen–Moriwaki, §§3.3–3.4 and §3.6. The implementation is organized
under `Extension/`: shared parameter spaces and analytic tools, finite separable
extensions, arbitrary finite extensions, general algebraic extensions, and measurable
automorphism pullbacks and fibre maxima.

Internal modules import their specific dependencies rather than this entry point.
-/

@[expose] public section
