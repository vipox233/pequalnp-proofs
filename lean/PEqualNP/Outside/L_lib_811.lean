import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_811

open scoped BigOperators
open Finset

lemma allocate (q : ℕ) (c : Fin q → ℕ) (s : ℕ) (hs : s ≤ ∑ j, c j) :
    ∃ v : Fin q → ℕ, (∀ j, v j ≤ c j) ∧ (∑ j, v j) = s := by
  induction q generalizing s with
  | zero =>
    refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
    · intro j; exact Fin.elim0 j
    · simpa using (hs.antisymm (Nat.zero_le s)).symm
  | succ q ih =>
    rw [Fin.sum_univ_succ] at hs
    obtain ⟨v, hv, he⟩ := ih (fun j => c j.succ) (s - c 0) (by omega)
    refine ⟨Fin.cons (min s (c 0)) v, ?_, ?_⟩
    · intro j; refine Fin.cases ?_ (fun k => ?_) j
      · simpa using (min_le_right s (c 0))
      · simpa using hv k
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, he]
      omega

def spent {α : Type} [Fintype α] {q : ℕ} (f : α → Option (Fin q → ℕ)) (j : Fin q) : ℕ :=
  ∑ i, ((f i).getD 0) j

def stopped {α : Type} [Fintype α] {q : ℕ} (f : α → Option (Fin q → ℕ)) : ℕ :=
  ∑ i, if (f i).isSome then 1 else 0

def labels {α : Type} {q : ℕ} (E : ℕ) (f : α → Option (Fin q → ℕ)) : Prop :=
  ∀ i v, f i = some v → ∑ j, v j = E

def agrees {α : Type} {q : ℕ} (f g : α → Option (Fin q → ℕ)) : Prop :=
  ∀ i v, f i = some v → g i = some v

lemma stopped_le {α : Type} [Fintype α] {q : ℕ} (f : α → Option (Fin q → ℕ)) :
    stopped f ≤ Fintype.card α := by
  calc
    stopped f ≤ ∑ _i : α, 1 := Finset.sum_le_sum (fun i _ => by split <;> omega)
    _ = _ := by simp

lemma total_spent {α : Type} [Fintype α] {q E : ℕ} (f : α → Option (Fin q → ℕ))
    (hf : labels E f) : ∑ j, spent f j = stopped f * E := by
  unfold spent stopped
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  cases h : f i with
  | none => simp [h]
  | some v => simpa [h] using hf i v h

lemma sum_update_zero {α : Type} [Fintype α] [DecidableEq α] (f : α → ℕ)
    (i : α) (hi : f i = 0) (v : ℕ) :
    (∑ j, Function.update f i v j) = (∑ j, f j) + v := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  simpa [Finset.sdiff_singleton_eq_erase, hi, Nat.add_comm] using congrArg (fun n => v+n) h

lemma update_spent {α : Type} [Fintype α] [DecidableEq α] {q : ℕ}
    (f : α → Option (Fin q → ℕ)) (i : α) (hi : f i = none) (v : Fin q → ℕ) (j : Fin q) :
    spent (Function.update f i (some v)) j = spent f j + v j := by
  unfold spent
  have he : (fun k => ((Function.update f i (some v) k).getD 0) j) =
      Function.update (fun k => ((f k).getD 0) j) i (v j) := by
    funext k
    by_cases hk : k=i <;> simp [hk]
  rw [he]
  exact sum_update_zero _ i (by simp [hi]) _

lemma update_stopped {α : Type} [Fintype α] [DecidableEq α] {q : ℕ}
    (f : α → Option (Fin q → ℕ)) (i : α) (hi : f i = none) (v : Fin q → ℕ) :
    stopped (Function.update f i (some v)) = stopped f + 1 := by
  unfold stopped
  have he : (fun k => if (Function.update f i (some v) k).isSome then 1 else 0) =
      Function.update (fun k => if (f k).isSome then 1 else 0) i 1 := by
    funext k
    by_cases hk : k=i <;> simp [hk]
  rw [he]
  exact sum_update_zero _ i (by simp [hi]) _

lemma fill {α : Type} [Fintype α] [DecidableEq α] {q E : ℕ} (hE : 0<E)
    (c : Fin q → ℕ) (f : α → Option (Fin q → ℕ))
    (hf : labels E f) (hc : ∀ j, spent f j ≤ c j)
    (hcap : (∑ j, c j) ≤ Fintype.card α * E) :
    ∃ g : α → Option (Fin q → ℕ), labels E g ∧ agrees f g ∧
      (∀ j, spent g j ≤ c j) ∧ stopped g = (∑ j, c j) / E := by
  classical
  let S : Finset ℕ := (Finset.range (Fintype.card α+1)).filter (fun k =>
    ∃ g : α → Option (Fin q → ℕ), labels E g ∧ agrees f g ∧
      (∀ j, spent g j ≤ c j) ∧ stopped g = k)
  have hS : S.Nonempty := by
    refine ⟨stopped f, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_range]
    refine ⟨by have := stopped_le f; omega, f, hf, ?_, hc, rfl⟩
    intro i v h; exact h
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨_, g, hg, hfg, hgc, hkg⟩ := Finset.mem_filter.mp hk
  have hg_le : stopped g ≤ (∑ j, c j)/E := by
    apply (Nat.le_div_iff_mul_le hE).2
    rw [← total_spent g hg]
    exact Finset.sum_le_sum (fun j _ => hgc j)
  have hge : (∑ j, c j)/E ≤ stopped g := by
    by_contra hn
    have hlt : stopped g < (∑ j, c j)/E := by omega
    have hmul : (stopped g+1)*E ≤ ∑ j, c j :=
      (Nat.le_div_iff_mul_le hE).1 (by omega)
    have hroom : stopped g < Fintype.card α := by nlinarith
    have hnone : ∃ i, g i = none := by
      by_contra hn
      push Not at hn
      have hall : stopped g = Fintype.card α := by
        unfold stopped
        have he : ∀ i, (g i).isSome = true := by
          intro i; cases h : g i with
          | none => exact False.elim (hn i h)
          | some v => rfl
        simp [he]
      omega
    obtain ⟨i, hi⟩ := hnone
    let r : Fin q → ℕ := fun j => c j - spent g j
    have hr : ∑ j, r j = (∑ j, c j) - stopped g * E := by
      rw [show (∑ j, r j) = (∑ j, c j) - ∑ j, spent g j from
        Finset.sum_tsub_distrib _ (fun j _ => hgc j)]
      rw [total_spent g hg]
    obtain ⟨v, hv, hvE⟩ := allocate q r E (by
      rw [hr]
      have hm : stopped g * E + E ≤ ∑ j, c j := by nlinarith
      omega)
    let g' := Function.update g i (some v)
    have hg' : labels E g' := by
      intro a z hz
      by_cases ha : a=i
      · subst a
        have : z=v := by simpa [g'] using hz.symm
        simpa [this] using hvE
      · exact hg a z (by simpa [g',ha] using hz)
    have hfg' : agrees f g' := by
      intro a z hz
      have hgz := hfg a z hz
      have ha : a≠i := by intro h; subst a; rw [hi] at hgz; contradiction
      simpa [g',ha] using hgz
    have hgc' : ∀ j, spent g' j ≤ c j := by
      intro j
      rw [show g'=Function.update g i (some v) from rfl, update_spent _ _ hi]
      have := hv j
      dsimp [r] at this
      have := hgc j
      omega
    have hcount' : stopped g'=stopped g+1 := update_stopped _ _ hi _
    have hmem : stopped g' ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := stopped_le g'; omega), ?_⟩
      exact ⟨g',hg',hfg',hgc',rfl⟩
    have := hmax _ hmem
    simp only [id_eq] at this
    omega
  exact ⟨g,hg,hfg,hgc, hg_le.antisymm hge⟩


def children (b : ℕ) : (Fin (2^b) × Fin 2) ≃ Fin (2^(b+1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ 2 b).symm)

@[simp] lemma children_val (b : ℕ) (i : Fin (2^b)) (e : Fin 2) :
    (children b (i,e)).val = i.val*2+e.val := by
  change e.val+2*i.val = i.val*2+e.val
  omega

def duplicate {q b : ℕ} (f : Fin (2^b) → Option (Fin q → ℕ))
    (i : Fin (2^(b+1))) : Option (Fin q → ℕ) :=
  f ((children b).symm i).1

@[simp] lemma duplicate_child {q b : ℕ} (f : Fin (2^b) → Option (Fin q → ℕ))
    (i : Fin (2^b)) (e : Fin 2) : duplicate f (children b (i,e)) = f i := by
  simp [duplicate]

lemma duplicate_sum {q b : ℕ} (f : Fin (2^b) → Option (Fin q → ℕ))
    (a : Option (Fin q → ℕ) → ℕ) :
    (∑ i, a (duplicate f i)) = 2 * ∑ i, a (f i) := by
  rw [← (children b).sum_comp (fun i => a (duplicate f i))]
  simp only [duplicate_child, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp_rw [← two_mul]
  rw [Finset.mul_sum]

lemma duplicate_spent {q b : ℕ} (f : Fin (2^b) → Option (Fin q → ℕ)) (j : Fin q) :
    spent (duplicate f) j = 2*spent f j := duplicate_sum f (fun v => v.getD 0 j)

lemma duplicate_labels {q b E : ℕ} (f : Fin (2^b) → Option (Fin q → ℕ))
    (hf : labels E f) : labels E (duplicate f) := by
  intro i v hi
  exact hf _ v hi

lemma coherent_levels {q E : ℕ} (hE : 0<E) (c : ℕ → Fin q → ℕ)
    (hcap : ∀ b, (∑ j, c b j) ≤ 2^b * E)
    (hd : ∀ b j, 2*c b j ≤ c (b+1) j) :
    ∃ f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ),
      (∀ b, labels E (f b)) ∧ (∀ b j, spent (f b) j ≤ c b j) ∧
      (∀ b, stopped (f b) = (∑ j, c b j)/E) ∧
      ∀ b i e v, f b i = some v → f (b+1) (children b (i,e)) = some v := by
  classical
  let S := fun b : ℕ => {f : Fin (2^b) → Option (Fin q → ℕ) //
    labels E f ∧ (∀ j, spent f j ≤ c b j) ∧ stopped f = (∑ j, c b j)/E}
  obtain ⟨f0,h0,h00,h01,h02⟩ := fill hE (c 0) (fun _ : Fin (2^0) => none)
    (by intro i v h; contradiction) (by intro j; simp [spent]) (by simpa using hcap 0)
  let init : S 0 := ⟨f0,h0,h01,h02⟩
  have step : ∀ b, ∀ f : S b, ∃ g : S (b+1), agrees (duplicate f.val) g.val := by
    intro b f
    obtain ⟨g,hg,hfg,hgc,hge⟩ := fill hE (c (b+1)) (duplicate f.val)
      (duplicate_labels _ f.property.1)
      (by intro j; rw [duplicate_spent]; exact (Nat.mul_le_mul_left 2 (f.property.2.1 j)).trans (hd b j))
      (by simpa using hcap (b+1))
    exact ⟨⟨g,hg,hgc,hge⟩,hfg⟩
  let go := fun b (f : S b) => Classical.choose (step b f)
  let F : (b : ℕ) → S b := fun b => Nat.rec init go b
  refine ⟨fun b => (F b).val, (fun b => (F b).property.1),
    (fun b j => (F b).property.2.1 j), (fun b => (F b).property.2.2), ?_⟩
  intro b i e v hv
  have hs := Classical.choose_spec (step b (F b))
  apply hs (children b (i,e)) v
  simpa using hv

lemma floor_caps {q E : ℕ} (μ : Fin q → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    (hs : ∑ j, μ j = E) :
    (∀ b, (∑ j, ⌊(2 : ℝ)^b*μ j⌋₊) ≤ 2^b*E) ∧
    ∀ b j, 2*⌊(2 : ℝ)^b*μ j⌋₊ ≤ ⌊(2 : ℝ)^(b+1)*μ j⌋₊ := by
  constructor
  · intro b
    have hf : (∑ j, (⌊(2 : ℝ)^b*μ j⌋₊ : ℝ)) ≤ (2 : ℝ)^b*E := by
      calc
        _ ≤ ∑ j, (2 : ℝ)^b*μ j := Finset.sum_le_sum (fun j _ => Nat.floor_le (mul_nonneg (by positivity) (hμ j)))
        _ = _ := by rw [← Finset.mul_sum, hs]
    exact_mod_cast hf
  · intro b j
    apply Nat.le_floor
    push_cast
    have hf := Nat.floor_le (show 0 ≤ (2 : ℝ)^b*μ j from mul_nonneg (by positivity) (hμ j))
    rw [pow_succ]
    nlinarith


lemma spent_mono {α : Type} [Fintype α] {q : ℕ}
    (f g : α → Option (Fin q → ℕ)) (h : agrees f g) (j : Fin q) :
    spent f j ≤ spent g j := by
  apply Finset.sum_le_sum
  intro i _
  cases hi : f i with
  | none => simp [hi]
  | some v => simp [hi, h i v hi]

lemma levels_mono {q : ℕ} (f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ))
    (hc : ∀ b i e v, f b i = some v → f (b+1) (children b (i,e)) = some v)
    (j : Fin q) :
    Monotone (fun b => (spent (f b) j : ℝ)/(2 : ℝ)^b) := by
  apply monotone_nat_of_le_succ
  intro b
  have hstep : 2*spent (f b) j ≤ spent (f (b+1)) j := by
    rw [← duplicate_spent]
    apply spent_mono
    intro i v hi
    have h := hc b ((children b).symm i).1 ((children b).symm i).2 v hi
    simpa using h
  have hr : 2*(spent (f b) j : ℝ) ≤ (spent (f (b+1)) j : ℝ) := by exact_mod_cast hstep
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [pow_succ]
  have hp : 0 < (2 : ℝ)^b := by positivity
  nlinarith

lemma spent_le_floor {q : ℕ} (f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ))
    (hc : ∀ b i e v, f b i = some v → f (b+1) (children b (i,e)) = some v)
    (μ : Fin q → ℝ)
    (hlim : ∀ j, Filter.Tendsto (fun b => (spent (f b) j : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds (μ j))) :
    ∀ b j, spent (f b) j ≤ ⌊(2 : ℝ)^b*μ j⌋₊ := by
  intro b j
  have hm := levels_mono f hc j
  have hl : (spent (f b) j : ℝ)/(2 : ℝ)^b ≤ μ j :=
    ge_of_tendsto (hlim j) (Filter.eventually_atTop.mpr ⟨b,fun n hn => hm hn⟩)
  apply Nat.le_floor
  have := (div_le_iff₀ (show 0 < (2 : ℝ)^b by positivity)).mp hl
  nlinarith

lemma stopped_le_floor {q E : ℕ} (hE : 0<E)
    (f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ))
    (hf : ∀ b, labels E (f b))
    (hc : ∀ b i e v, f b i = some v → f (b+1) (children b (i,e)) = some v)
    (μ : Fin q → ℝ)
    (hlim : ∀ j, Filter.Tendsto (fun b => (spent (f b) j : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds (μ j))) (b : ℕ) :
    stopped (f b) ≤ (∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)/E := by
  apply (Nat.le_div_iff_mul_le hE).2
  rw [← total_spent _ (hf b)]
  exact Finset.sum_le_sum (fun j _ => spent_le_floor f hc μ hlim b j)

lemma packed_gap {α : Type} [Fintype α] {q E : ℕ} (hE : 0<E)
    (f : α → Option (Fin q → ℕ)) (c : Fin q → ℕ)
    (hf : labels E f) (hc : ∀ j, spent f j ≤ c j)
    (hcount : stopped f = (∑ j, c j)/E) (j : Fin q) :
    c j < spent f j + E := by
  have he : ∑ j, (c j-spent f j) = (∑ j, c j) % E := by
    rw [Finset.sum_tsub_distrib _ (fun j _ => hc j), total_spent _ hf, hcount]
    have hd := Nat.mod_add_div (∑ j, c j) E
    have hm := Nat.mod_lt (∑ j, c j) hE
    rw [Nat.mul_comm E] at hd
    omega
  have hs : c j-spent f j ≤ ∑ i, (c i-spent f i) :=
    Finset.single_le_sum (f := fun i => c i-spent f i) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [he] at hs
  have hm := Nat.mod_lt (∑ j, c j) hE
  omega

lemma inverse_pow_limit (C : ℝ) :
    Filter.Tendsto (fun b : ℕ => C/(2 : ℝ)^b) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1 : ℝ)/2 < 1 by norm_num)).const_mul C
  simpa [div_eq_mul_inv, inv_pow] using h

lemma packed_means {q E : ℕ} (hE : 0<E) (μ : Fin q → ℝ) (hμ : ∀ j, 0≤μ j)
    (f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ))
    (hf : ∀ b, labels E (f b))
    (hc : ∀ b j, spent (f b) j ≤ ⌊(2 : ℝ)^b*μ j⌋₊)
    (hcount : ∀ b, stopped (f b) = (∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)/E) :
    ∀ j, Filter.Tendsto (fun b => (spent (f b) j : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds (μ j)) := by
  intro j
  have hb : ∀ b, 0 ≤ μ j - (spent (f b) j : ℝ)/(2 : ℝ)^b ∧
      μ j - (spent (f b) j : ℝ)/(2 : ℝ)^b ≤ (E+1 : ℝ)/(2 : ℝ)^b := by
    intro b
    have hp : 0 < (2 : ℝ)^b := by positivity
    have hfloor := Nat.floor_le (mul_nonneg (le_of_lt hp) (hμ j))
    have hus : (spent (f b) j : ℝ) ≤ (⌊(2 : ℝ)^b*μ j⌋₊ : ℝ) := by exact_mod_cast hc b j
    have hgap := packed_gap hE (f b) (fun j => ⌊(2 : ℝ)^b*μ j⌋₊) (hf b) (hc b) (hcount b) j
    have hg : (⌊(2 : ℝ)^b*μ j⌋₊ : ℝ) < (spent (f b) j : ℝ)+E := by exact_mod_cast hgap
    have hx := Nat.lt_floor_add_one ((2 : ℝ)^b*μ j)
    constructor
    · apply sub_nonneg.mpr
      apply (div_le_iff₀ hp).mpr
      nlinarith
    · apply (le_div_iff₀ hp).mpr
      have he : (μ j - (spent (f b) j : ℝ)/(2 : ℝ)^b)*(2 : ℝ)^b =
          μ j*(2 : ℝ)^b-(spent (f b) j : ℝ) := by field_simp
      rw [he]
      nlinarith
  have hz : Filter.Tendsto (fun b => μ j-(spent (f b) j : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun b => (hb b).1) (fun b => (hb b).2) (inverse_pow_limit (E+1))
  have h := (tendsto_const_nhds (x := μ j)).sub hz
  simpa only [sub_sub_cancel, sub_zero] using h

lemma floor_missing {q E : ℕ} (μ : Fin q → ℝ) (hs : ∑ j, μ j = E) (b : ℕ) :
    2^b*E ≤ (∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)+q := by
  have hr : (2 : ℝ)^b*E ≤ (∑ j, (⌊(2 : ℝ)^b*μ j⌋₊ : ℝ))+q := by
    calc
      _ = ∑ j, (2 : ℝ)^b*μ j := by rw [← Finset.mul_sum,hs]
      _ ≤ ∑ j, ((⌊(2 : ℝ)^b*μ j⌋₊ : ℝ)+1) :=
        Finset.sum_le_sum (fun j _ => le_of_lt (Nat.lt_floor_add_one _))
      _ = _ := by simp [Finset.sum_add_distrib]
  exact_mod_cast hr

lemma pending_bound {q E : ℕ} (hE : 0<E) (μ : Fin q → ℝ)
    (hμ : ∀ j, 0≤μ j) (hs : ∑ j, μ j = E) (b : ℕ) :
    2^b - (∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)/E ≤ q+E := by
  let C := ∑ j, ⌊(2 : ℝ)^b*μ j⌋₊
  have hcap : C ≤ 2^b*E := (floor_caps μ hμ hs).1 b
  have hmiss : 2^b*E ≤ C+q := floor_missing μ hs b
  have hd := Nat.mod_add_div C E
  have hr := Nat.mod_lt C hE
  have hm := Nat.div_mul_le_self C E
  have hle : C/E ≤ 2^b := by nlinarith
  have he : 2^b - C/E + C/E = 2^b := by omega
  have hprod : (2^b-C/E)*E ≤ q+E := by nlinarith
  nlinarith

lemma tails_summable {q E : ℕ} (hE : 0<E) (μ : Fin q → ℝ)
    (hμ : ∀ j, 0≤μ j) (hs : ∑ j, μ j = E) :
    Summable (fun b : ℕ => ((2^b-(∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)/E : ℕ) : ℝ)/(2 : ℝ)^b) := by
  have hg : Summable (fun b : ℕ => ((q+E : ℕ) : ℝ)/(2 : ℝ)^b) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (summable_geometric_two.mul_left ((q+E : ℕ) : ℝ))
  apply Summable.of_nonneg_of_le (fun b => by positivity) _ hg
  intro b
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast pending_bound hE μ hμ hs b


lemma pending_fin {α : Type} [Fintype α] {q : ℕ} (f : α → Option (Fin q → ℕ)) :
    ((Finset.univ : Finset α).filter (fun i => (f i).isNone)).card =
      Fintype.card α - stopped f := by
  classical
  have he : ((Finset.univ : Finset α).filter (fun i => (f i).isNone)).card + stopped f =
      Fintype.card α := by
    rw [Finset.card_filter, stopped, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : α, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        cases h : f i <;> simp [h]
      _ = _ := by simp
  omega

lemma pending_range {q : ℕ} (T : ℕ → Option (Fin q → ℕ)) (N : ℕ) :
    ((Finset.range N).filter (fun i => (T i).isNone)).card =
      N - stopped (fun i : Fin N => T i.val) := by
  have h := pending_fin (fun i : Fin N => T i.val)
  simpa only [Finset.card_filter, Finset.sum_range, Fintype.card_fin] using h

lemma range_spent {q : ℕ} (T : ℕ → Option (Fin q → ℕ)) (N : ℕ) (j : Fin q) :
    (∑ i ∈ Finset.range N, (T i).getD 0 j) =
      spent (fun i : Fin N => T i.val) j := by
  exact (Fin.sum_univ_eq_sum_range (fun i => (T i).getD 0 j) N).symm

end PEqualNP.Outside.L_lib_811
theorem PEqualNP.Outside.L_lib_811 :
∀ (q E : ℕ), 0 < q → 0 < E → ∀ μ : Fin q → ℝ, (∀ j, 0 ≤ μ j) → (∑ j, μ j) = E →
  let A := Fin q → ℕ
  let Tree := ℕ → ℕ → Option A
  let pending := fun (T : Tree) (b : ℕ) =>
    ((Finset.range (2^b)).filter (fun i => (T b i).isNone)).card
  let valid := fun T : Tree =>
    (∀ b i v, i < 2^b → T b i = some v →
      (∑ j : Fin q, v j) = E ∧ T (b+1) (2*i) = some v ∧ T (b+1) (2*i+1) = some v) ∧
    Filter.Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) Filter.atTop (nhds 0) ∧
    ∀ j : Fin q, Filter.Tendsto
      (fun b => ((∑ i ∈ Finset.range (2^b), ((T b i).getD 0) j : ℕ) : ℝ)/(2 : ℝ)^b)
      Filter.atTop (nhds (μ j))
  let bound := fun b : ℕ => 2^b-(∑ j : Fin q, ⌊(2 : ℝ)^b*μ j⌋₊)/E
  (∀ T : Tree, valid T → ∀ b : ℕ, bound b ≤ pending T b) ∧
  (∃ T : Tree, valid T ∧ ∀ b : ℕ, pending T b = bound b) ∧
  Summable (fun b : ℕ => (bound b : ℝ)/(2 : ℝ)^b) := by
  classical
  intro q E hq hE μ hμ hsum
  dsimp only
  refine ⟨?_, ?_, PEqualNP.Outside.L_lib_811.tails_summable hE μ hμ hsum⟩
  · intro T hT b
    let f : (b : ℕ) → Fin (2^b) → Option (Fin q → ℕ) := fun b i => T b i.val
    have hf : ∀ b, PEqualNP.Outside.L_lib_811.labels E (f b) := by
      intro b i v hi
      exact (hT.1 b i.val v i.isLt hi).1
    have hc : ∀ b i e v, f b i = some v →
        f (b+1) (PEqualNP.Outside.L_lib_811.children b (i,e)) = some v := by
      intro b i e v hi
      have hs := hT.1 b i.val v i.isLt hi
      fin_cases e
      · simpa [f, PEqualNP.Outside.L_lib_811.children_val, Nat.mul_comm] using hs.2.1
      · simpa [f, PEqualNP.Outside.L_lib_811.children_val, Nat.mul_comm] using hs.2.2
    have hm : ∀ j, Filter.Tendsto
        (fun b => (PEqualNP.Outside.L_lib_811.spent (f b) j : ℝ)/(2 : ℝ)^b)
        Filter.atTop (nhds (μ j)) := by
      intro j
      simpa only [PEqualNP.Outside.L_lib_811.range_spent] using hT.2.2 j
    rw [PEqualNP.Outside.L_lib_811.pending_range]
    exact Nat.sub_le_sub_left (PEqualNP.Outside.L_lib_811.stopped_le_floor hE f hf hc μ hm b) _
  · obtain ⟨f,hf,hcap,hcount,hcopy⟩ := PEqualNP.Outside.L_lib_811.coherent_levels hE
      (fun b j => ⌊(2 : ℝ)^b*μ j⌋₊)
      (PEqualNP.Outside.L_lib_811.floor_caps μ hμ hsum).1
      (PEqualNP.Outside.L_lib_811.floor_caps μ hμ hsum).2
    let T : ℕ → ℕ → Option (Fin q → ℕ) :=
      fun b i => if hi : i<2^b then f b ⟨i,hi⟩ else none
    have hTf : ∀ b (i : Fin (2^b)), T b i.val = f b i := by
      intro b i
      simp [T,i.isLt]
    have hp : ∀ b, ((Finset.range (2^b)).filter (fun i => (T b i).isNone)).card =
        2^b-(∑ j, ⌊(2 : ℝ)^b*μ j⌋₊)/E := by
      intro b
      rw [PEqualNP.Outside.L_lib_811.pending_range]
      simp only [hTf,hcount]
    refine ⟨T, ⟨?_, ?_, ?_⟩, hp⟩
    · intro b i v hi hv
      let a : Fin (2^b) := ⟨i,hi⟩
      have hfa : f b a = some v := by
        rw [← hTf b a]
        exact hv
      refine ⟨hf b a v hfa, ?_, ?_⟩
      · have hx : (PEqualNP.Outside.L_lib_811.children b (a,0)).val = 2*i := by
          simp [PEqualNP.Outside.L_lib_811.children_val,a,Nat.mul_comm]
        rw [←hx,hTf]
        exact hcopy b a 0 v hfa
      · have hx : (PEqualNP.Outside.L_lib_811.children b (a,1)).val = 2*i+1 := by
          simp [PEqualNP.Outside.L_lib_811.children_val,a,Nat.mul_comm]
        rw [←hx,hTf]
        exact hcopy b a 1 v hfa
    · apply squeeze_zero (fun b => by positivity)
        (g := fun b => ((q+E : ℕ) : ℝ)/(2 : ℝ)^b)
      · intro b
        rw [hp]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast PEqualNP.Outside.L_lib_811.pending_bound hE μ hμ hsum b
      · exact PEqualNP.Outside.L_lib_811.inverse_pow_limit _
    · intro j
      have hm := PEqualNP.Outside.L_lib_811.packed_means hE μ hμ f hf hcap hcount j
      simpa only [PEqualNP.Outside.L_lib_811.range_spent,hTf] using hm


