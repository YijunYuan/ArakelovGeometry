/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import ArakelovGeometry.ExternalResults.AbsoluteValue
import ArakelovGeometry.ExternalResults.AbsoluteValueExtension
import ArakelovGeometry.ExternalResults.AbsoluteValueRootBounds
import ArakelovGeometry.ExternalResults.AbsoluteValueLocal
import ArakelovGeometry.ExternalResults.AbsoluteValueTensor
import ArakelovGeometry.ExternalResults.BoundedFunctionalMonotoneClass
import ArakelovGeometry.ExternalResults.Place
import ArakelovGeometry.ExternalResults.Measure
import ArakelovGeometry.ExternalResults.Ostrowski
import ArakelovGeometry.AdelicCurve.Defs
import ArakelovGeometry.AdelicCurve.Basic
import ArakelovGeometry.AdelicCurve.Amalgamation
import ArakelovGeometry.AdelicCurve.Restriction
import ArakelovGeometry.AdelicCurve.Equiv
import ArakelovGeometry.AdelicCurve.Extension
import ArakelovGeometry.AdelicCurve.Height
import ArakelovGeometry.ExternalResults.AlgebraicTowerSupport
import ArakelovGeometry.AdelicCurve.Examples.Trivial
import ArakelovGeometry.AdelicCurve.Examples.NumberFields
import ArakelovGeometry.AdelicCurve.Examples.FunctionFields

/-!
# Arakelov geometry over adelic curves

Library root. Aggregates every module so that a plain `lake build` compiles the
whole development. Follows Chen–Moriwaki, *Arakelov Geometry over Adelic Curves*
(Springer LNM 2258), Chapter 3.
-/
