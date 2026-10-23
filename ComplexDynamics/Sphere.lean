/-
Copyright (c) 2026 Filip Moruś. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filip Moruś
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Data.Set.Restrict
public import Mathlib.Topology.Continuous
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.PFun
public import Mathlib.Algebra.Group.DivInvMonoid

/-!
## Riemann Sphere
-/

set_option linter.style.setOption false
set_option linter.flexible false

@[expose] public section

open Set OnePoint Filter Topology Function

noncomputable section

namespace SphereComplex

abbrev RiemannSphere := OnePoint ℂ


/-The finite chart `z ↦ z`, its source and target-/
def ZeroSource : Set RiemannSphere := range ((↑) : ℂ → RiemannSphere)

def ZeroTarget : Set ℂ := Set.univ

def ZeroChart : RiemannSphere → ℂ :=
  invFun ((↑) : ℂ → RiemannSphere)

def ZeroChartInv : ℂ → RiemannSphere :=
  ((↑) : ℂ → RiemannSphere)

theorem ZeroChart_right_inv : ZeroChart ∘ ZeroChartInv = id := by
  exact invFun_comp coe_injective

/-Inverse function on the Riemann sphere-/
def invFun_Sphere : RiemannSphere → RiemannSphere := fun z =>
  match z with
  | OnePoint.some z =>
      if z = 0 then infty
      else ↑(z)⁻¹
  | none => ↑(0 : ℂ)

/-The infinite chart `z ↦ 1/z`, its source and target-/
def InftySource : Set RiemannSphere := {OnePoint.some 0}ᶜ

def InftyTarget : Set ℂ := Set.univ

def InftyChart : RiemannSphere → ℂ := invFun (↑) ∘ invFun_Sphere

def InftyChartInv : ℂ → RiemannSphere := invFun_Sphere ∘ (↑)

/-other results-/
theorem coe_leftInv : LeftInverse (invFun ((↑) : ℂ → RiemannSphere)) (↑) := by
  exact leftInverse_invFun coe_injective

theorem InftySource_mem_notZero {z : ℂ} (hz : OnePoint.some z ∈ InftySource) : z ≠ 0 := by
  intro h
  exact hz (congrArg OnePoint.some h)

theorem InftyChart_infty_eq_zero : InftyChart none = 0 := by
  simp [InftyChart, comp, invFun_Sphere, invFun]

/-Finite chart is an open partial homeomorphism-/
def ZeroChartIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := ZeroChart
      invFun := ZeroChartInv
      source := ZeroSource
      target := ZeroTarget
      map_source' := by simp [ZeroTarget]
      map_target' z hz := by simp [ZeroChartInv, ZeroSource]
      left_inv' z hz := by
        rcases hz with ⟨w, rfl⟩
        congr
        simp [ZeroChart]
        exact leftInverse_invFun coe_injective w
      right_inv' z _ := by exact leftInverse_invFun coe_injective z
    }
    continuousOn_toFun := by
      rw [ZeroSource, ZeroChart]
      exact isOpenMap_coe.continuousOn_range_of_leftInverse (leftInverse_invFun coe_injective)
    continuousOn_invFun := by
      simp [ZeroTarget]
      exact continuous_coe
  }
  open_source := by
    change IsOpen ZeroSource
    rw [ZeroSource]
    exact isOpen_range_coe
  open_target := by
    change IsOpen ZeroTarget
    exact isOpen_univ

/-Proving that the infinite chart is an open partial homeomorphism-/
def InftyChartIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := InftyChart
      invFun := InftyChartInv
      source := InftySource
      target := InftyTarget
      map_source' := by simp [InftyTarget]
      map_target' z hz := by
        simp [InftyChartInv, invFun_Sphere]
        split <;> simp [InftySource]
        trivial
      left_inv' z hz := by
        cases z with
        | none =>
          rw [InftyChart_infty_eq_zero]
          simp [InftyChartInv, invFun_Sphere]
          rfl
        | some z =>
          simp [InftyChart, InftyChartInv, invFun_Sphere,
          InftySource_mem_notZero hz, comp, invFun]
          rfl
      right_inv' z hz := by
        simp [InftyChartInv, invFun_Sphere]
        split
        . simp [InftyChart, invFun_Sphere, invFun]
          symm
          assumption
        . rename_i h1
          simp [InftyChart, invFun_Sphere, h1, invFun]
    }
    continuousOn_toFun := by
      rw [InftyChart]
      suffices h1 : ContinuousOn invFun_Sphere InftySource by
        suffices h2 : ContinuousOn (invFun OnePoint.some) (range OnePoint.some) by
          suffices h3 : MapsTo invFun_Sphere InftySource (range OnePoint.some) by
            exact ContinuousOn.comp h2 h1 h3
          simp [InftySource, compl]
          intro x hx
          rcases x with _ | z
          · simp [invFun_Sphere]
          · exact ⟨z⁻¹, by simp [invFun_Sphere, InftySource_mem_notZero hx]⟩
        exact IsOpenMap.continuousOn_range_of_leftInverse (isOpenMap_coe) (coe_leftInv)
      intro z hz
      have h4 : ContinuousAt invFun_Sphere z := by
        sorry
      have h5 : InftySource ∈ 𝓝 z := by
        simp [mem_nhds_iff]
        use InftySource
        constructor
        · trivial
        · constructor
          · simp? [InftySource]
          · exact hz
      exact (continuousWithinAt_iff_continuousAt h5).mpr h4
    continuousOn_invFun := by
      sorry
  }


end SphereComplex
