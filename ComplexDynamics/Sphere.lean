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

/-The infinite chart `z ↦ 1/z`, its source and target-/
def InftySource : Set RiemannSphere := {OnePoint.some 0}ᶜ

def InftyTarget : Set ℂ := Set.univ

theorem InftySource_mem_notZero {z : ℂ} (hz : OnePoint.some z ∈ InftySource) : z ≠ 0 := by
  intro h
  exact hz (congrArg OnePoint.some h)

def InftyChart : RiemannSphere → ℂ
  | OnePoint.infty => 0
  | OnePoint.some z => z⁻¹

def InftyChartInv : ℂ → RiemannSphere := fun z => if z = 0 then OnePoint.infty else (z⁻¹ : ℂ)

/-Proving that the finite chart is an open partial homeomorphism-/
def ZeroChartIsOpenPartialHomeomorph : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialHomeomorph := {
    toPartialEquiv := {
      toFun := ZeroChart
      invFun := ZeroChartInv
      source := ZeroSource
      target := ZeroTarget
      map_source' _ _ := by simp [ZeroTarget]
      map_target' z hz := by simp [ZeroChartInv, ZeroSource]
      left_inv' z hz := by
        rcases hz with ⟨w, rfl⟩
        apply congr
        rfl


        change ZeroChartInv (ZeroChart ∘ OnePoint.some w) = ↑w
        simp [ZeroChart, invFun_comp (coe_injective)]


        cases z with
        | none =>
          exact absurd hz (by
            rw [ZeroSource, compl_infty]
            exact infty_notMem_range_coe)
        | some z => rfl
      right_inv' z hz := by exact invFun_comp coe_injective
    }
    continuousOn_toFun := by
      have hs : ZeroSource = range ((↑) : ℂ → RiemannSphere) := by
        rw [ZeroSource, compl_infty]
      rw [hs]
      exact isOpenMap_coe.continuousOn_range_of_leftInverse
        (fun z => by simp [ZeroChart])
    continuousOn_invFun := by
      simp [ZeroTarget]
      exact continuous_coe
  }
  open_source := by
    change IsOpen ZeroSource
    rw [ZeroSource, compl_infty]
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
      map_source' _ _ := by simp [InftyTarget]
      map_target' z _ := by
        by_cases hz : z = 0 <;> simp [InftyChartInv, hz, InftySource]
      left_inv' z hz := by
        cases z with
        | none =>
          simp [InftyChart, InftyChartInv, infty]
          rfl
        | some z =>
          rw [InftyChart, InftyChartInv]
          simp [InftySource_mem_notZero (hz)]
          rfl
      right_inv' z hz := by
        simp [InftyChartInv]
        split
        . simp [InftyChart]
          symm
          assumption
        . simp [InftyChart]
    }
    continuousOn_toFun z hz := by
      simp [InftySource]
      have hw : ContinuousAt InftyChart z := by
        change ContinuousAt (fun z : RiemannSphere =>
          match z with
          | OnePoint.infty => (0 : ℂ)
          | OnePoint.some z => z⁻¹) z
        cases z with
        | none =>
          have ht : Tendsto
            (InftyChart ∘ (↑))
            (coclosedCompact ℂ)
            (𝓝 (InftyChart OnePoint.infty)) := by
              simp [InftyChart]
              change (cocompact ℂ).map (InftyChart ∘ (↑)) ≤ 𝓝 0
              intro s hs
              simp [InftyChart, Set.preimage_comp_eq, preimage, mem_cocompact]
              obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hs



        | some z =>
  }











  open_source := by
    change IsOpen ZeroSource
    rw [ZeroSource, compl_infty]
    exact isOpen_range_coe
  open_target := by
    change IsOpen ZeroTarget
    exact isOpen_univ

end SphereComplex
