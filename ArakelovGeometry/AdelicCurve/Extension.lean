/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Basic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Construction
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Cylinder
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.CylinderContent
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.FiniteProjection
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integrable
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Integral
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.InverseLimit
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Measure
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Probability
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.Tower
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerBasic
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerCylinder
import ArakelovGeometry.AdelicCurve.Extension.Algebraic.TowerIntegral
import ArakelovGeometry.AdelicCurve.Extension.Automorphism
import ArakelovGeometry.AdelicCurve.Extension.BoundedEvaluationGenerators
import ArakelovGeometry.AdelicCurve.Extension.FibreMaximum
import ArakelovGeometry.AdelicCurve.Extension.Finite.BaseChange
import ArakelovGeometry.AdelicCurve.Extension.Finite.Construction
import ArakelovGeometry.AdelicCurve.Extension.Finite.Probability
import ArakelovGeometry.AdelicCurve.Extension.Finite.Tower
import ArakelovGeometry.AdelicCurve.Extension.FiniteIntermediateField
import ArakelovGeometry.AdelicCurve.Extension.ParameterSpace
import ArakelovGeometry.AdelicCurve.Extension.PowerSums
import ArakelovGeometry.AdelicCurve.Extension.RootBounds
import ArakelovGeometry.AdelicCurve.Extension.Separable.Construction
import ArakelovGeometry.AdelicCurve.Extension.Separable.Embeddings
import ArakelovGeometry.AdelicCurve.Extension.Separable.FibreIntegral
import ArakelovGeometry.AdelicCurve.Extension.Separable.Measurability
import ArakelovGeometry.AdelicCurve.Extension.Separable.Measure

/-!
# Scalar extensions of adelic structures

Import entry point for Chen–Moriwaki, §§3.3–3.4 and §3.6. The implementation is organized
under `Extension/`: shared parameter spaces and analytic tools, finite separable
extensions, arbitrary finite extensions, general algebraic extensions, and measurable
automorphism pullbacks.

Internal modules import their specific dependencies rather than this entry point.
-/
