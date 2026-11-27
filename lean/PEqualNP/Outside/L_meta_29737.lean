import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29737.Loss

open Finset

def edits {α : Type*} [Fintype α] (B H : α → Bool) : Finset α :=
  univ.filter (fun x => H x ≠ B x)

theorem loss_as_sdiff {α : Type*} [Fintype α] [DecidableEq α]
    (B H : α → Bool) (S : Finset α) :
    univ.filter (fun x => H x ≠ xor (B x) (decide (x ∈ S))) =
      (edits B H \ S) ∪ (S \ edits B H) := by
  ext x
  by_cases hs : x ∈ S <;>
    cases hb : B x <;> cases hh : H x <;>
    simp [edits, hs, hb, hh]

theorem loss_identity {α : Type*} [Fintype α] [DecidableEq α]
    (B H : α → Bool) (S : Finset α) :
    (univ.filter (fun x => H x ≠ xor (B x) (decide (x ∈ S)))).card +
      2 * (edits B H ∩ S).card = (edits B H).card + S.card := by
  rw [loss_as_sdiff, card_union_of_disjoint]
  · have h1 := card_sdiff_add_card_inter (edits B H) S
    have h2 := card_sdiff_add_card_inter S (edits B H)
    rw [inter_comm S (edits B H)] at h2
    omega
  · exact disjoint_sdiff_sdiff

def matching {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (j : Fin q) :
    Finset (Fin N × Fin N) := univ.image (fun x => (x, f j x))

theorem matching_card {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N)) (j : Fin q) :
    (matching f j).card = N := by
  rw [matching, card_image_of_injective]
  · simp
  · intro x y h
    exact congrArg Prod.fst h

theorem matching_disjoint {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x)) {i j : Fin q} (hij : i ≠ j) :
    Disjoint (matching f i) (matching f j) := by
  apply disjoint_left.mpr
  intro z hi hj
  obtain ⟨x, _, hx⟩ := mem_image.mp hi
  obtain ⟨y, _, hy⟩ := mem_image.mp hj
  have hxy : x = y := congrArg Prod.fst (hx.trans hy.symm)
  subst y
  exact hij (hf x (congrArg Prod.snd (hx.trans hy.symm)))

theorem selected_card {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x)) (D : Finset (Fin q)) :
    (D.biUnion (matching f)).card = N * D.card := by
  rw [card_biUnion]
  · simp [matching_card, Nat.mul_comm]
  · intro i hi j hj hij
    exact matching_disjoint f hf hij

theorem selected_mem {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (D : Finset (Fin q)) (x y : Fin N) :
    (x,y) ∈ D.biUnion (matching f) ↔ y ∈ D.image (fun j => f j x) := by
  simp only [mem_biUnion, matching, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,u,hux,huy⟩
    subst u
    exact ⟨j,hj,huy⟩
  · rintro ⟨j,hj,h⟩
    exact ⟨j,hj,x,rfl,h⟩

theorem selected_inter_card {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x)) (D : Finset (Fin q))
    (B : Finset (Fin N × Fin N)) :
    (B ∩ D.biUnion (matching f)).card = ∑ j ∈ D, (B ∩ matching f j).card := by
  rw [inter_biUnion, card_biUnion]
  intro i hi j hj hij
  exact (matching_disjoint f hf hij).mono inter_subset_right inter_subset_right

theorem subset_sum {q t : ℕ} (ht : 0 < t) (c : Fin q → ℕ) :
    ∑ D ∈ (univ : Finset (Fin q)).powersetCard t, ∑ j ∈ D, c j =
      (q - 1).choose (t - 1) * ∑ j, c j := by
  have hc (j : Fin q) :
      (((univ : Finset (Fin q)).powersetCard t).filter (fun D => j ∈ D)).card =
        (q - 1).choose (t - 1) := by
    simpa only [singleton_subset_iff, card_univ, Fintype.card_fin, card_singleton] using
      card_filter_powersetCard_subset ({j} : Finset (Fin q)) univ t
        (subset_univ _) (by simp only [card_singleton]; omega)
  calc
    _ = ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        ∑ j : Fin q, if j ∈ D then c j else 0 := by simp
    _ = ∑ j : Fin q, ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        if j ∈ D then c j else 0 := sum_comm
    _ = ∑ j : Fin q, (q - 1).choose (t - 1) * c j := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      simp [hc]
    _ = _ := by rw [mul_sum]

theorem sum_selected_inter {N q t : ℕ} (ht : 0 < t)
    (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (B : Finset (Fin N × Fin N)) :
    ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        (B ∩ D.biUnion (matching f)).card =
      (q - 1).choose (t - 1) * (B ∩ univ.biUnion (matching f)).card := by
  simp_rw [selected_inter_card f hf]
  exact subset_sum ht _

theorem sum_loss_identity {N q t : ℕ} (ht : 0 < t)
    (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (base H : (Fin N × Fin N) → Bool) :
    (∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
      (univ.filter (fun z => H z ≠ xor (base z)
        (decide (z ∈ D.biUnion (matching f))))).card) +
      2 * (q - 1).choose (t - 1) *
        (edits base H ∩ univ.biUnion (matching f)).card =
      q.choose t * ((edits base H).card + N * t) := by
  have hid := sum_congr (s₁ := (univ : Finset (Fin q)).powersetCard t) rfl
    (fun D _ => loss_identity base H (D.biUnion (matching f)))
  rw [sum_add_distrib] at hid
  simp_rw [selected_card f hf] at hid
  have hr : (∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
      ((edits base H).card + N * D.card)) =
      q.choose t * ((edits base H).card + N * t) := by
    calc
      _ = ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
          ((edits base H).card + N * t) := by
        apply sum_congr rfl
        intro D hD
        rw [(mem_powersetCard.mp hD).2]
      _ = _ := by simp
  rw [hr, ← mul_sum, sum_selected_inter ht f hf] at hid
  simpa only [mul_assoc] using hid

theorem average_budget {q t E K J B C S Z : ℕ}
    (hqt : q ≤ 2*t) (hB : B ≤ E) (hC : C ≤ B)
    (hrel : q*J = t*K) (hid : S+2*J*C = K*(B+Z)) :
    K*(q*Z) ≤ q*S+(2*t-q)*E*K := by
  have h1 := congrArg (fun x : ℕ => q*x) hid
  have h2 := congrArg (fun x : ℕ => 2*C*x) hrel
  have h3 := Nat.mul_le_mul_right ((2*t-q)*K) hB
  have h4 := Nat.mul_le_mul_right (2*t*K) hC
  have h5 := congrArg (fun x : ℕ => x*K*B) (Nat.sub_add_cancel hqt)
  nlinarith

theorem choose_ratio {q t : ℕ} (hq : 0 < q) (ht : 0 < t) :
    q * (q-1).choose (t-1) = t * q.choose t := by
  have h := Nat.add_one_mul_choose_eq (q-1) (t-1)
  have hq1 : q-1+1=q := by omega
  have ht1 : t-1+1=t := by omega
  rw [hq1,ht1] at h
  simpa only [Nat.mul_comm] using h

theorem sum_loss_lower_bound {N q E t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hqt : q ≤ 2*t) (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (base H : (Fin N × Fin N) → Bool) (hE : (edits base H).card ≤ E) :
    q.choose t * (q*(N*t)) ≤
      q * (∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        (univ.filter (fun z => H z ≠ xor (base z)
          (decide (z ∈ D.biUnion (matching f))))).card) +
      (2*t-q)*E*q.choose t := by
  exact average_budget hqt hE (card_le_card inter_subset_left)
    (choose_ratio hq ht) (sum_loss_identity ht f hf base H)

theorem average_gap_identity {q t E K J B C S Z : ℕ}
    (hqt : q ≤ 2*t) (hB : B ≤ E) (hC : C ≤ B)
    (hrel : q*J = t*K) (hid : S+2*J*C = K*(B+Z)) :
    q*S+(2*t-q)*E*K = K*(q*Z) +
      K*((2*t-q)*(E-B)+2*t*(B-C)) := by
  have h1 := congrArg (fun x : ℕ => q*x) hid
  have h2 := congrArg (fun x : ℕ => 2*C*x) hrel
  have h3 := congrArg (fun x : ℕ => x*(2*t-q)*K) (Nat.sub_add_cancel hB)
  have h4 := congrArg (fun x : ℕ => x*2*t*K) (Nat.sub_add_cancel hC)
  have h5 := congrArg (fun x : ℕ => x*K*B) (Nat.sub_add_cancel hqt)
  nlinarith

theorem average_gap_zero {q t E K B C : ℕ}
    (hqt : q < 2*t) (hK : 0 < K) (hB : B ≤ E) (hC : C ≤ B)
    (hgap : K*((2*t-q)*(E-B)+2*t*(B-C))=0) : B=E ∧ C=B := by
  have hq : 0 < 2*t-q := Nat.sub_pos_of_lt hqt
  have ht : 0 < 2*t := by omega
  have hz : (2*t-q)*(E-B)+2*t*(B-C)=0 :=
    (Nat.mul_eq_zero.mp hgap).resolve_left (ne_of_gt hK)
  have hzb : E-B=0 := by nlinarith
  have hzc : B-C=0 := by nlinarith
  omega

end PEqualNP.Outside.L_meta_29737.Loss

namespace PEqualNP.Outside.L_meta_29737.Tree

open Finset Filter

def Stable {A : Type*} (T : ℕ → ℕ → Option A) : Prop :=
  ∀ b i v, i < 2^b → T b i = some v →
    T (b+1) (2*i) = some v ∧ T (b+1) (2*i+1) = some v

def raw {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (b : ℕ) : ℕ :=
  ∑ i ∈ range (2^b), ((T b i).map g).getD 0

noncomputable def part {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (b : ℕ) : ℝ :=
  (raw T g b : ℝ)/(2 : ℝ)^b

theorem sum_range_double {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2*n), f i = ∑ i ∈ range n, (f (2*i)+f (2*i+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    simp only [add_assoc]

theorem raw_double_le {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ)
    (hT : Stable T) (b : ℕ) : 2 * raw T g b ≤ raw T g (b+1) := by
  unfold raw
  rw [show 2^(b+1)=2*2^b by rw [pow_succ, Nat.mul_comm], sum_range_double, mul_sum]
  apply sum_le_sum
  intro i hi
  cases h : T b i with
  | none => simp [h]
  | some v =>
    obtain ⟨h0,h1⟩ := hT b i v (mem_range.mp hi) h
    rw [h0,h1]
    simp [two_mul]

theorem part_monotone {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ)
    (hT : Stable T) : Monotone (part T g) := by
  apply monotone_nat_of_le_succ
  intro b
  have hraw : (2 : ℝ) * raw T g b ≤ raw T g (b+1) := by
    exact_mod_cast raw_double_le T g hT b
  unfold part
  rw [pow_succ]
  calc
    (raw T g b : ℝ) / 2^b = (2 * raw T g b) / (2^b * 2) := by ring
    _ ≤ (raw T g (b+1) : ℝ) / (2^b * 2) :=
      div_le_div_of_nonneg_right hraw (by positivity)

theorem part_le {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (M : ℕ)
    (hg : ∀ b i v, i < 2^b → T b i = some v → g v ≤ M) (b : ℕ) :
    part T g b ≤ M := by
  have hr : raw T g b ≤ 2^b * M := by
    unfold raw
    calc
      _ ≤ ∑ i ∈ range (2^b), M := by
        apply sum_le_sum
        intro i hi
        cases h : T b i with
        | none => simp [h]
        | some v => simpa [h] using hg b i v (mem_range.mp hi) h
      _ = _ := by simp
  have hr' : (raw T g b : ℝ) ≤ (2 : ℝ)^b * M := by exact_mod_cast hr
  unfold part
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^b)).2
  nlinarith

theorem part_converges {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (M : ℕ)
    (hT : Stable T)
    (hg : ∀ b i v, i < 2^b → T b i = some v → g v ≤ M) :
    ∃ z : ℝ, Tendsto (part T g) atTop (nhds z) := by
  refine ⟨⨆ b, part T g b, tendsto_atTop_ciSup (part_monotone T g hT) ?_⟩
  refine ⟨(M : ℝ), ?_⟩
  rintro y ⟨b,rfl⟩
  exact part_le T g M hg b

def pending {A : Type*} (T : ℕ → ℕ → Option A) (b : ℕ) : ℕ :=
  ((range (2^b)).filter (fun i => (T b i).isNone)).card

noncomputable def realpart {A : Type*} (T : ℕ → ℕ → Option A)
    (g : A → ℝ) (b : ℕ) : ℝ :=
  (∑ i ∈ range (2^b), ((T b i).map g).getD 0)/(2 : ℝ)^b

theorem realpart_nat {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (b : ℕ) :
    realpart T (fun a => (g a : ℝ)) b = part T g b := by
  unfold realpart part raw
  rw [Nat.cast_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem realpart_const {A : Type*} (T : ℕ → ℕ → Option A) (c : ℝ) (b : ℕ) :
    realpart T (fun _ => c) b = c * part T (fun _ => 1) b := by
  unfold realpart part raw
  rw [← mul_div_assoc, Nat.cast_sum, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem realpart_sum {A D : Type*} (T : ℕ → ℕ → Option A) (s : Finset D)
    (g : D → A → ℝ) (b : ℕ) :
    realpart T (fun a => ∑ d ∈ s, g d a) b = ∑ d ∈ s, realpart T (g d) b := by
  unfold realpart
  rw [← sum_div]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem realpart_mono {A : Type*} (T : ℕ → ℕ → Option A) (g h : A → ℝ)
    (hgh : ∀ b i v, i < 2^b → T b i = some v → g v ≤ h v) (b : ℕ) :
    realpart T g b ≤ realpart T h b := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro i hi
  cases hTi : T b i with
  | none => simp
  | some v => exact hgh b i v (mem_range.mp hi) hTi

theorem raw_one_add_pending {A : Type*} (T : ℕ → ℕ → Option A) (b : ℕ) :
    raw T (fun _ => 1) b + pending T b = 2^b := by
  unfold raw pending
  rw [card_eq_sum_ones, sum_filter, ← sum_add_distrib]
  calc
    _ = ∑ i ∈ range (2^b), 1 := by
      apply sum_congr rfl
      intro i hi
      cases T b i <;> simp
    _ = _ := by simp

theorem onepart_add_pending {A : Type*} (T : ℕ → ℕ → Option A) (b : ℕ) :
    part T (fun _ => 1) b + (pending T b : ℝ)/(2 : ℝ)^b = 1 := by
  have h : (raw T (fun _ => 1) b : ℝ) + pending T b = (2 : ℝ)^b := by
    exact_mod_cast raw_one_add_pending T b
  unfold part
  rw [← add_div,h]
  exact div_self (by positivity)

theorem onepart_tendsto {A : Type*} (T : ℕ → ℕ → Option A)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0)) :
    Tendsto (part T (fun _ => 1)) atTop (nhds 1) := by
  have heq : part T (fun _ => 1) = fun b => 1 - (pending T b : ℝ)/(2 : ℝ)^b := by
    funext b
    linarith [onepart_add_pending T b]
  rw [heq]
  simpa using tendsto_const_nhds.sub hp

theorem exists_large_limit {A D : Type*} (T : ℕ → ℕ → Option A) (s : Finset D)
    (g : D → A → ℕ) (M : ℕ) (ideal : ℝ) (hs : s.Nonempty) (hT : Stable T)
    (hg : ∀ d b i v, i < 2^b → T b i = some v → g d v ≤ M)
    (hbudget : ∀ b i v, i < 2^b → T b i = some v →
      (s.card : ℝ)*ideal ≤ ∑ d ∈ s, (g d v : ℝ))
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0)) :
    ∃ d ∈ s, ∃ z : ℝ, ideal ≤ z ∧ Tendsto (part T (g d)) atTop (nhds z) := by
  choose z hz using (fun d => part_converges T (g d) M hT (hg d))
  have hi (b : ℕ) : (s.card : ℝ)*ideal*part T (fun _ => 1) b ≤
      ∑ d ∈ s, part T (g d) b := by
    have h := realpart_mono T (fun _ => (s.card : ℝ)*ideal)
      (fun v => ∑ d ∈ s, (g d v : ℝ)) hbudget b
    simpa only [realpart_const,realpart_sum,realpart_nat] using h
  have hleft := (onepart_tendsto T hp).const_mul ((s.card : ℝ)*ideal)
  have hright : Tendsto (fun b => ∑ d ∈ s, part T (g d) b)
      atTop (nhds (∑ d ∈ s, z d)) := by
    classical
    clear hs hbudget hi hleft
    induction s using Finset.induction_on with
    | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    | @insert a s ha ih => simpa [Finset.sum_insert ha] using (hz a).add ih
  have hsum := le_of_tendsto_of_tendsto' hleft hright hi
  have hsum' : (∑ d ∈ s, ideal) ≤ ∑ d ∈ s, z d := by
    simpa using hsum
  obtain ⟨d,hd,hzlarge⟩ := exists_le_of_sum_le hs hsum'
  exact ⟨d,hd,z d,hzlarge,hz d⟩

end PEqualNP.Outside.L_meta_29737.Tree

namespace PEqualNP.Outside.L_meta_29737.Minimax

open Finset Filter PEqualNP.Outside.L_meta_29737.Loss

def loss {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (base H : (Fin N × Fin N) → Bool) (D : Finset (Fin q)) : ℕ :=
  (univ.filter (fun z => H z ≠ xor (base z)
    (decide (z ∈ D.biUnion (matching f))))).card

theorem real_budget {N q E t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hqt : q ≤ 2*t) (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (base H : (Fin N × Fin N) → Bool) (hE : (edits base H).card ≤ E) :
    ((univ : Finset (Fin q)).powersetCard t).card *
        (((N*t : ℕ) : ℝ) - (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) ≤
      ∑ D ∈ (univ : Finset (Fin q)).powersetCard t, (loss f base H D : ℝ) := by
  have h := sum_loss_lower_bound hq ht hqt f hf base H hE
  have hr : (q.choose t : ℝ) * ((q : ℝ)*((N*t : ℕ) : ℝ)) ≤
      (q : ℝ) * (∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        (loss f base H D : ℝ)) + (((2*t-q)*E : ℕ) : ℝ)*(q.choose t : ℝ) := by
    exact_mod_cast h
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [card_powersetCard, card_univ, Fintype.card_fin]
  apply (mul_le_mul_iff_right₀ hqr).mp
  have hd : (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)*(q : ℝ) =
      (((2*t-q)*E : ℕ) : ℝ) := div_mul_cancel₀ _ (ne_of_gt hqr)
  nlinarith

theorem minimax {N q E t : ℕ} (hq : 0 < q) (ht : 0 < t)
    (hqt : q ≤ 2*t) (htq : t ≤ q) (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool)
    (T : ℕ → ℕ → Option ((Fin N × Fin N) → Bool))
    (hT : PEqualNP.Outside.L_meta_29737.Tree.Stable T)
    (hE : ∀ b i H, i < 2^b → T b i = some H → (edits base H).card ≤ E)
    (hp : Tendsto (fun b => (PEqualNP.Outside.L_meta_29737.Tree.pending T b : ℝ)/(2 : ℝ)^b)
      atTop (nhds 0)) :
    ∃ (D : Finset (Fin q)) (z : ℝ), D.card = t ∧
      (((N*t : ℕ) : ℝ) - (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) ≤ z ∧
      Tendsto (PEqualNP.Outside.L_meta_29737.Tree.part T (fun H => loss f base H D)) atTop (nhds z) := by
  have hs : ((univ : Finset (Fin q)).powersetCard t).Nonempty := by
    apply powersetCard_nonempty.mpr
    simpa using htq
  have hg : ∀ (D : Finset (Fin q)) b i H, i < 2^b → T b i = some H →
      loss f base H D ≤ N*N := by
    intro D b i H hi hH
    simpa [loss] using (card_filter_le (s := (univ : Finset (Fin N × Fin N)))
      (p := fun z => H z ≠ xor (base z) (decide (z ∈ D.biUnion (matching f)))))
  have hb : ∀ b i H, i < 2^b → T b i = some H →
      ((univ : Finset (Fin q)).powersetCard t).card *
        (((N*t : ℕ) : ℝ) - (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) ≤
      ∑ D ∈ (univ : Finset (Fin q)).powersetCard t, (loss f base H D : ℝ) := by
    intro b i H hi hH
    exact real_budget hq ht hqt f hf base H (hE b i H hi hH)
  obtain ⟨D,hD,z,hz,hlim⟩ := PEqualNP.Outside.L_meta_29737.Tree.exists_large_limit T
    ((univ : Finset (Fin q)).powersetCard t) (fun D H => loss f base H D)
    (N*N) _ hs hT hg hb hp
  exact ⟨D,z,(mem_powersetCard.mp hD).2,hz,hlim⟩

end PEqualNP.Outside.L_meta_29737.Minimax

namespace PEqualNP.Outside.L_meta_29737.Rigidity

open Finset Filter PEqualNP.Outside.L_meta_29737.Tree

theorem leaf_zero {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ)
    (hT : Stable T) (hlim : Tendsto (part T g) atTop (nhds 0))
    (b i : ℕ) (v : A) (hi : i < 2^b) (hv : T b i = some v) : g v = 0 := by
  have hp := (part_monotone T g hT).ge_of_tendsto hlim b
  have hr : raw T g b = 0 := by
    have hraw : (raw T g b : ℝ) ≤ 0 := by
      simpa using (div_le_iff₀ (by positivity : (0 : ℝ) < 2^b)).mp hp
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast hraw)
  have hg : g v ≤ raw T g b := by
    have h := single_le_sum (f := fun j => ((T b j).map g).getD 0)
      (fun j _ => Nat.zero_le _) (mem_range.mpr hi)
    simpa [raw,hv] using h
  omega

theorem integer_tail {q E b p : ℕ} (hq : 0 < q) (hE : 0 < E)
    (c : Fin q → ℕ)
    (hc : ∀ j, q*c j ≤ 2^b*E)
    (htotal : (∑ j, c j) + E*p = 2^b*E) :
    (((2^b*E)%q)+E-1)/E ≤ p := by
  have hcap : ∑ j, c j ≤ q*((2^b*E)/q) := by
    calc
      _ ≤ ∑ _ : Fin q, (2^b*E)/q := by
        apply sum_le_sum
        intro j _
        apply (Nat.le_div_iff_mul_le hq).mpr
        simpa [Nat.mul_comm] using hc j
      _ = _ := by simp
  have hrem : (2^b*E)%q ≤ E*p := by
    have hd := Nat.mod_add_div (2^b*E) q
    omega
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hE).mpr
  have hpos : 0 < (2^b*E)%q+E := by omega
  have hsub := Nat.sub_add_cancel (by omega : 1 ≤ (2^b*E)%q+E)
  nlinarith

theorem leaf_at_budget {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ)
    (c : ℕ) (z : ℝ) (hT : Stable T)
    (hbudget : ∀ b i v, i < 2^b → T b i = some v → c ≤ g v)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0))
    (hg : Tendsto (part T g) atTop (nhds z)) (hz : z ≤ c)
    (b i : ℕ) (v : A) (hi : i < 2^b) (hv : T b i = some v) : g v = c := by
  have hid (b : ℕ) : part T g b - (c : ℝ)*part T (fun _ => 1) b =
      part T (fun v => g v-c) b := by
    have hraw : raw T g b = c*raw T (fun _ => 1) b + raw T (fun v => g v-c) b := by
      unfold raw
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      cases h : T b i with
      | none => simp
      | some v =>
        have hb := hbudget b i v (mem_range.mp hi) h
        simpa using (Nat.add_sub_of_le hb).symm
    unfold part
    rw [hraw, Nat.cast_add, Nat.cast_mul]
    ring
  have hgap : Tendsto (part T (fun v => g v-c)) atTop (nhds (z-c)) := by
    have h := hg.sub ((onepart_tendsto T hp).const_mul (c : ℝ))
    simpa only [mul_one,hid] using h
  have hz' : (0 : ℝ) ≤ z-c := ge_of_tendsto' hgap (fun n => by
    unfold part
    positivity)
  have hzc : z-(c : ℝ)=0 := by linarith
  rw [hzc] at hgap
  have hzero := leaf_zero T (fun v => g v-c) hT hgap b i v hi hv
  have hle := hbudget b i v hi hv
  omega

end PEqualNP.Outside.L_meta_29737.Rigidity

namespace PEqualNP.Outside.L_meta_29737.Exchange

open Finset PEqualNP.Outside.L_meta_29737.Loss

theorem equal_of_subset_sums {q t : ℕ} (ht : 0 < t) (htq : t < q)
    (c : Fin q → ℝ) (target : ℝ)
    (h : ∀ D : Finset (Fin q), D.card=t → ∑ j ∈ D, c j = target)
    (i j : Fin q) : c i = c j := by
  by_cases hij : i=j
  · simpa [hij]
  have hj : j ∈ (univ : Finset (Fin q)).erase i := by simp [hij,Ne.symm hij]
  have hcard : t-1 ≤ (((univ : Finset (Fin q)).erase i).erase j).card := by
    rw [card_erase_of_mem hj, card_erase_of_mem (mem_univ i)]
    simp only [card_univ, Fintype.card_fin]
    omega
  obtain ⟨U,hU,hUc⟩ := exists_subset_card_eq hcard
  have hiU : i ∉ U := by
    intro hi
    have hmem := hU hi
    simp only [mem_erase] at hmem
    exact hmem.2.1 rfl
  have hjU : j ∉ U := by
    intro hj
    have hmem := hU hj
    simp only [mem_erase] at hmem
    exact hmem.1 rfl
  have hiC : (insert i U).card=t := by rw [card_insert_of_notMem hiU,hUc]; omega
  have hjC : (insert j U).card=t := by rw [card_insert_of_notMem hjU,hUc]; omega
  have hiS := h (insert i U) hiC
  have hjS := h (insert j U) hjC
  rw [sum_insert hiU] at hiS
  rw [sum_insert hjU] at hjS
  linarith

theorem subset_sum_real {q t : ℕ} (ht : 0 < t) (c : Fin q → ℝ) :
    ∑ D ∈ (univ : Finset (Fin q)).powersetCard t, ∑ j ∈ D, c j =
      ((q-1).choose (t-1) : ℝ) * ∑ j, c j := by
  have hc (j : Fin q) :
      (((univ : Finset (Fin q)).powersetCard t).filter (fun D => j ∈ D)).card =
        (q-1).choose (t-1) := by
    simpa only [singleton_subset_iff, card_univ, Fintype.card_fin, card_singleton] using
      card_filter_powersetCard_subset ({j} : Finset (Fin q)) univ t
        (subset_univ _) (by simp only [card_singleton]; omega)
  calc
    _ = ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        ∑ j : Fin q, if j ∈ D then c j else 0 := by simp
    _ = ∑ j : Fin q, ∑ D ∈ (univ : Finset (Fin q)).powersetCard t,
        if j ∈ D then c j else 0 := sum_comm
    _ = ∑ j : Fin q, ((q-1).choose (t-1) : ℝ) * c j := by
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      simp [hc]
    _ = _ := by rw [mul_sum]

theorem equal_of_subset_bounds {q t : ℕ} (ht : 0 < t) (htq : t < q)
    (c : Fin q → ℝ) (mu : ℝ) (hsum : ∑ j, c j = q*mu)
    (h : ∀ D : Finset (Fin q), D.card=t → ∑ j ∈ D, c j ≤ t*mu) :
    ∀ j, c j = mu := by
  have hq : 0 < q := by omega
  have hrel : (q : ℝ)*((q-1).choose (t-1) : ℝ) = (t : ℝ)*(q.choose t : ℝ) := by
    exact_mod_cast choose_ratio hq ht
  have havg : (∑ D ∈ (univ : Finset (Fin q)).powersetCard t, ∑ j ∈ D, c j) =
      ∑ _ ∈ (univ : Finset (Fin q)).powersetCard t, (t : ℝ)*mu := by
    rw [subset_sum_real ht,hsum]
    simp only [sum_const, nsmul_eq_mul, card_powersetCard, card_univ, Fintype.card_fin]
    nlinarith [congrArg (fun x : ℝ => x*mu) hrel]
  have hconst : ∀ D : Finset (Fin q), D.card=t → ∑ j ∈ D, c j = t*mu := by
    intro D hD
    have hle : ∀ d ∈ (univ : Finset (Fin q)).powersetCard t,
        (∑ j ∈ d, c j) ≤ (t : ℝ)*mu := by
      intro d hd
      exact h d (mem_powersetCard.mp hd).2
    exact (sum_eq_sum_iff_of_le hle).mp havg D (mem_powersetCard.mpr ⟨subset_univ _,hD⟩)
  intro j
  have hall : ∀ i, c i=c j := fun i => equal_of_subset_sums ht htq c (t*mu) hconst i j
  have hj : ∑ i, c i = (q : ℝ)*c j := by simp_rw [hall]; simp
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  exact (mul_left_cancel₀ hqr) (hj.symm.trans hsum)

end PEqualNP.Outside.L_meta_29737.Exchange

namespace PEqualNP.Outside.L_meta_29737.Tree

open Finset Filter

theorem realpart_add {A : Type*} (T : ℕ → ℕ → Option A) (g h : A → ℝ) (b : ℕ) :
    realpart T (fun v => g v+h v) b = realpart T g b+realpart T h b := by
  unfold realpart
  rw [← add_div, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem realpart_mul {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℝ) (c : ℝ) (b : ℕ) :
    realpart T (fun v => c*g v) b = c*realpart T g b := by
  unfold realpart
  rw [← mul_div_assoc,mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem part_add {A : Type*} (T : ℕ → ℕ → Option A) (g h : A → ℕ) (b : ℕ) :
    part T (fun v => g v+h v) b = part T g b+part T h b := by
  rw [← realpart_nat, ← realpart_nat, ← realpart_nat]
  simp only [Nat.cast_add,realpart_add]

theorem part_mul {A : Type*} (T : ℕ → ℕ → Option A) (g : A → ℕ) (c : ℕ) (b : ℕ) :
    part T (fun v => c*g v) b = (c : ℝ)*part T g b := by
  rw [← realpart_nat, ← realpart_nat]
  simp only [Nat.cast_mul,realpart_mul]

theorem part_const {A : Type*} (T : ℕ → ℕ → Option A) (c b : ℕ) :
    part T (fun _ => c) b = (c : ℝ)*part T (fun _ => 1) b := by
  rw [← realpart_nat,realpart_const]

theorem part_sum {A D : Type*} (T : ℕ → ℕ → Option A) (s : Finset D)
    (g : D → A → ℕ) (b : ℕ) :
    part T (fun v => ∑ d ∈ s, g d v) b = ∑ d ∈ s, part T (g d) b := by
  rw [← realpart_nat]
  simp only [Nat.cast_sum,realpart_sum,realpart_nat]

theorem finite_sum_tendsto {D : Type*} (s : Finset D) (f : D → ℕ → ℝ) (z : D → ℝ)
    (hf : ∀ d ∈ s, Tendsto (f d) atTop (nhds (z d))) :
    Tendsto (fun b => ∑ d ∈ s, f d b) atTop (nhds (∑ d ∈ s,z d)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (mem_insert_self _ _)
    have hfs : ∀ d ∈ s, Tendsto (f d) atTop (nhds (z d)) :=
      fun d hd => hf d (mem_insert_of_mem hd)
    simpa [sum_insert ha] using hfa.add (ih hfs)

theorem raw_congr_leaf {A : Type*} (T : ℕ → ℕ → Option A) (g h : A → ℕ)
    (heq : ∀ b i v, i<2^b → T b i=some v → g v=h v) (b : ℕ) :
    raw T g b=raw T h b := by
  unfold raw
  apply sum_congr rfl
  intro i hi
  cases hTi : T b i with
  | none => simp
  | some v => exact heq b i v (mem_range.mp hi) hTi

theorem part_congr_leaf {A : Type*} (T : ℕ → ℕ → Option A) (g h : A → ℕ)
    (heq : ∀ b i v, i<2^b → T b i=some v → g v=h v) (b : ℕ) :
    part T g b=part T h b := by
  unfold part
  rw [raw_congr_leaf T g h heq b]

theorem raw_sum {A D : Type*} (T : ℕ → ℕ → Option A) (s : Finset D)
    (g : D → A → ℕ) (b : ℕ) :
    raw T (fun v => ∑ d ∈ s, g d v) b = ∑ d ∈ s, raw T (g d) b := by
  unfold raw
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

theorem raw_const {A : Type*} (T : ℕ → ℕ → Option A) (c b : ℕ) :
    raw T (fun _ => c) b = c*raw T (fun _ => 1) b := by
  unfold raw
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  cases T b i <;> simp

end PEqualNP.Outside.L_meta_29737.Tree

namespace PEqualNP.Outside.L_meta_29737.Equality

open Finset Filter PEqualNP.Outside.L_meta_29737.Loss PEqualNP.Outside.L_meta_29737.Tree PEqualNP.Outside.L_meta_29737.Minimax PEqualNP.Outside.L_meta_29737.Rigidity

theorem leaves_full {N q E t : ℕ} (hq : 0 < q) (hqt : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool)
    (T : ℕ → ℕ → Option ((Fin N × Fin N) → Bool)) (hT : Stable T)
    (hE : ∀ b i H, i < 2^b → T b i = some H → (edits base H).card ≤ E)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0))
    (hopt : ∀ D : Finset (Fin q), D.card=t → ∃ z : ℝ,
      Tendsto (part T (fun H => loss f base H D)) atTop (nhds z) ∧
      z ≤ (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))) :
    ∀ b i H, i < 2^b → T b i=some H →
      (edits base H).card=E ∧ (edits base H ∩ univ.biUnion (matching f)).card=E := by
  have ht : 0 < t := by omega
  let s := (univ : Finset (Fin q)).powersetCard t
  let K := q.choose t
  let coeff := (2*t-q)*E*K
  let target := K*(q*(N*t))
  let g := fun H => q*(∑ D ∈ s, loss f base H D)+coeff
  have hbounded (D : Finset (Fin q)) : ∀ b i H, i<2^b → T b i=some H →
      loss f base H D ≤ N*N := by
    intro b i H hi hH
    simpa [loss] using (card_filter_le (s := (univ : Finset (Fin N × Fin N)))
      (p := fun z => H z ≠ xor (base z) (decide (z ∈ D.biUnion (matching f)))))
  choose z hz using (fun D => part_converges T (fun H => loss f base H D)
    (N*N) hT (hbounded D))
  have hzbound (D) (hD : D∈s) : z D ≤
      (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) := by
    obtain ⟨w,hw,hwi⟩ := hopt D (mem_powersetCard.mp hD).2
    have heq := tendsto_nhds_unique (hz D) hw
    simpa only [heq] using hwi
  have hsumlim := finite_sum_tendsto s (fun D => part T (fun H => loss f base H D))
    z (fun D _ => hz D)
  have hglim : Tendsto (part T g) atTop
      (nhds ((q : ℝ)*(∑ D ∈ s,z D)+(coeff : ℝ))) := by
    have h := (hsumlim.const_mul (q : ℝ)).add
      ((onepart_tendsto T hp).const_mul (coeff : ℝ))
    have heq : part T g = fun b => (q : ℝ)*(∑ D ∈ s,
        part T (fun H => loss f base H D) b)+(coeff : ℝ)*part T (fun _ => 1) b := by
      funext b
      rw [show g=(fun H => q*(∑ D ∈ s,loss f base H D)+coeff) from rfl]
      rw [part_add,part_mul,part_sum,part_const]
    rw [heq]
    simpa only [mul_one] using h
  have hgle : (q : ℝ)*(∑ D ∈ s,z D)+(coeff : ℝ) ≤ (target : ℝ) := by
    have hsum : (∑ D ∈ s,z D) ≤ (K : ℝ)*
        (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) := by
      calc
        _ ≤ ∑ _ ∈ s, (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) :=
          sum_le_sum hzbound
        _ = _ := by simp only [sum_const,nsmul_eq_mul,s,card_powersetCard,
          card_univ,Fintype.card_fin,K]
    have hqr : (0 : ℝ)<q := by exact_mod_cast hq
    have hmul := mul_le_mul_of_nonneg_left hsum (le_of_lt hqr)
    have hdiv : (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)*(q : ℝ) =
      (((2*t-q)*E : ℕ) : ℝ) := div_mul_cancel₀ _ (ne_of_gt hqr)
    dsimp [coeff,target]
    push_cast
    push_cast at hmul hdiv
    nlinarith
  have hbudget : ∀ b i H, i<2^b → T b i=some H → target ≤ g H := by
    intro b i H hi hH
    exact sum_loss_lower_bound hq ht (le_of_lt hqt) f hf base H (hE b i H hi hH)
  intro b i H hi hH
  have hfull := leaf_at_budget T g target _ hT hbudget hp hglim hgle b i H hi hH
  have hB := hE b i H hi hH
  have hC : (edits base H ∩ univ.biUnion (matching f)).card ≤ (edits base H).card :=
    card_le_card inter_subset_left
  have hident := average_gap_identity (le_of_lt hqt) hB hC (choose_ratio hq ht)
    (sum_loss_identity ht f hf base H)
  have hgap : K*((2*t-q)*(E-(edits base H).card)+
      2*t*((edits base H).card-(edits base H ∩ univ.biUnion (matching f)).card))=0 := by
    change g H = target + _ at hident
    rw [hfull] at hident
    exact Nat.add_left_cancel (hident.symm.trans (Nat.add_zero target).symm)
  have hK : 0 < K := Nat.choose_pos (le_of_lt htq)
  obtain ⟨hBE,hCB⟩ := average_gap_zero hqt hK hB hC hgap
  exact ⟨hBE,hCB.trans hBE⟩

end PEqualNP.Outside.L_meta_29737.Equality

namespace PEqualNP.Outside.L_meta_29737.Means

open Finset Filter PEqualNP.Outside.L_meta_29737.Loss PEqualNP.Outside.L_meta_29737.Tree PEqualNP.Outside.L_meta_29737.Minimax PEqualNP.Outside.L_meta_29737.Exchange

def count {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (base : (Fin N × Fin N) → Bool) (j : Fin q) (H : (Fin N × Fin N) → Bool) :=
  (edits base H ∩ matching f j).card

theorem sum_count {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x, Function.Injective (fun j => f j x)) (base H : (Fin N × Fin N) → Bool) :
    (∑ j, count f base j H)=(edits base H ∩ univ.biUnion (matching f)).card := by
  simpa [count] using (selected_inter_card f hf univ (edits base H)).symm

theorem means {N q E t : ℕ} (hq : 0 < q) (hqt : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool)
    (T : ℕ → ℕ → Option ((Fin N × Fin N) → Bool)) (hT : Stable T)
    (hfull : ∀ b i H, i<2^b → T b i=some H →
      (edits base H).card=E ∧ (edits base H ∩ univ.biUnion (matching f)).card=E)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0))
    (hopt : ∀ D : Finset (Fin q), D.card=t → ∃ z : ℝ,
      Tendsto (part T (fun H => loss f base H D)) atTop (nhds z) ∧
      z ≤ (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))) :
    ∀ j, Tendsto (part T (count f base j)) atTop (nhds ((E : ℝ)/(q : ℝ))) := by
  have ht : 0 < t := by omega
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hbound (j) : ∀ b i H, i<2^b → T b i=some H → count f base j H ≤ E := by
    intro b i H hi hH
    rw [← (hfull b i H hi hH).1]
    exact card_le_card inter_subset_left
  choose c hc using (fun j => part_converges T (count f base j) E hT (hbound j))
  have htotal (b : ℕ) : (∑ j,part T (count f base j) b)=(E : ℝ)*part T (fun _ => 1) b := by
    rw [← part_sum]
    rw [part_congr_leaf T (fun H => ∑ j,count f base j H) (fun _ => E)
      (fun b i H hi hH => (sum_count f hf base H).trans (hfull b i H hi hH).2)]
    exact part_const T E b
  have hsumc : (∑ j,c j)=(E : ℝ) := by
    have h1 := finite_sum_tendsto univ (fun j => part T (count f base j)) c (fun j _ => hc j)
    have h2 := (onepart_tendsto T hp).const_mul (E : ℝ)
    simp only [htotal] at h1
    simpa only [mul_one] using tendsto_nhds_unique h1 h2
  have hsub (D : Finset (Fin q)) (hD : D.card=t) :
      (t : ℝ)*((E : ℝ)/(q : ℝ)) ≤ ∑ j ∈ D,c j := by
    obtain ⟨z,hz,hzi⟩ := hopt D hD
    have hleaf : ∀ b i H, i<2^b → T b i=some H →
        loss f base H D+2*(∑ j ∈ D,count f base j H)=E+N*t := by
      intro b i H hi hH
      have hl := loss_identity base H (D.biUnion (matching f))
      rw [selected_inter_card f hf,selected_card f hf,hD,(hfull b i H hi hH).1] at hl
      exact hl
    have hparts (b : ℕ) : part T (fun H => loss f base H D) b+
        2*(∑ j ∈ D,part T (count f base j) b) =
        ((E+N*t : ℕ) : ℝ)*part T (fun _ => 1) b := by
      have h := part_congr_leaf T _ _ hleaf b
      rw [part_add,part_mul,part_sum,part_const] at h
      norm_num only [Nat.cast_ofNat] at h
      exact h
    have h1 := hz.add ((finite_sum_tendsto D (fun j => part T (count f base j)) c
      (fun j _ => hc j)).const_mul 2)
    have h2 := (onepart_tendsto T hp).const_mul (((E+N*t : ℕ) : ℝ))
    simp only [hparts] at h1
    have heq : z+2*(∑ j ∈ D,c j)=((E+N*t : ℕ) : ℝ) := by
      simpa only [mul_one] using tendsto_nhds_unique h1 h2
    have hmul := mul_le_mul_of_nonneg_right hzi (le_of_lt hqr)
    have hdiv := div_mul_cancel₀ (((2*t-q)*E : ℕ) : ℝ) (ne_of_gt hqr)
    have hdivE := div_mul_cancel₀ (E : ℝ) (ne_of_gt hqr)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (le_of_lt hqt),Nat.cast_ofNat] at heq hmul hdiv
    apply (mul_le_mul_iff_right₀ hqr).mp
    nlinarith
  have hsumneg : (∑ j,-c j)=(q : ℝ)*(-((E : ℝ)/(q : ℝ))) := by
    rw [sum_neg_distrib,hsumc]
    have h := div_mul_cancel₀ (E : ℝ) (ne_of_gt hqr)
    nlinarith
  have hneg := equal_of_subset_bounds ht htq (fun j => -c j) (-((E : ℝ)/(q : ℝ)))
    hsumneg (fun D hD => by simpa only [sum_neg_distrib,mul_neg,neg_le_neg_iff] using hsub D hD)
  intro j
  have heq : c j=(E : ℝ)/(q : ℝ) := by linarith [hneg j]
  simpa only [heq] using hc j

end PEqualNP.Outside.L_meta_29737.Means

namespace PEqualNP.Outside.L_meta_29737.Stopping

open Finset Filter PEqualNP.Outside.L_meta_29737.Loss PEqualNP.Outside.L_meta_29737.Tree PEqualNP.Outside.L_meta_29737.Minimax
  PEqualNP.Outside.L_meta_29737.Rigidity PEqualNP.Outside.L_meta_29737.Means

theorem stopping_bound {N q E : ℕ} (hq : 0 < q) (hE : 0 < E)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool)
    (T : ℕ → ℕ → Option ((Fin N × Fin N) → Bool)) (hT : Stable T)
    (hfull : ∀ b i H, i<2^b → T b i=some H →
      (edits base H).card=E ∧ (edits base H ∩ univ.biUnion (matching f)).card=E)
    (hmean : ∀ j, Tendsto (part T (count f base j)) atTop (nhds ((E : ℝ)/(q : ℝ)))) :
    ∀ b, (((2^b*E)%q)+E-1)/E ≤ pending T b := by
  intro b
  have hcap (j : Fin q) : q*raw T (count f base j) b ≤ 2^b*E := by
    have h := (part_monotone T (count f base j) hT).ge_of_tendsto (hmean j) b
    unfold part at h
    have hqr : (0 : ℝ)<q := by exact_mod_cast hq
    have hr := (div_le_div_iff₀ (by positivity : (0 : ℝ)<2^b) hqr).mp h
    have hr' : (q : ℝ)*(raw T (count f base j) b : ℝ) ≤ (2 : ℝ)^b*(E : ℝ) := by
      nlinarith
    exact_mod_cast hr'
  have htotal : (∑ j, raw T (count f base j) b)+E*pending T b=2^b*E := by
    have hs : (∑ j, raw T (count f base j) b)=E*raw T (fun _ => 1) b := by
      rw [← raw_sum]
      rw [raw_congr_leaf T (fun H => ∑ j,count f base j H) (fun _ => E)
        (fun b i H hi hH => (sum_count f hf base H).trans (hfull b i H hi hH).2)]
      exact raw_const T E b
    rw [hs]
    have h := raw_one_add_pending T b
    nlinarith
  exact integer_tail hq hE (fun j => raw T (count f base j) b) hcap htotal

theorem optimal_stopping_bound {N q E t : ℕ} (hq : 0 < q) (hEpos : 0 < E)
    (hqt : q < 2*t) (htq : t < q)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x, Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool)
    (T : ℕ → ℕ → Option ((Fin N × Fin N) → Bool)) (hT : Stable T)
    (hE : ∀ b i H, i<2^b → T b i=some H → (edits base H).card ≤ E)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0))
    (hopt : ∀ D : Finset (Fin q), D.card=t → ∃ z : ℝ,
      Tendsto (part T (fun H => loss f base H D)) atTop (nhds z) ∧
      z ≤ (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))) :
    ∀ b, (((2^b*E)%q)+E-1)/E ≤ pending T b := by
  have hfull := PEqualNP.Outside.L_meta_29737.Equality.leaves_full hq hqt htq f hf base T hT hE hp hopt
  have hmean := means hq hqt htq f hf base T hT hfull hp hopt
  exact stopping_bound hq hEpos f hf base T hT hfull hmean

end PEqualNP.Outside.L_meta_29737.Stopping

namespace PEqualNP.Outside.L_meta_29737.Packing

open Finset

theorem pack {R : Type*} [Fintype R] {q E : ℕ} (cap : Fin q → ℕ)
    (h : Fintype.card R*E ≤ ∑ j, cap j) :
    ∃ c : R → Fin q → ℕ, (∀ r, ∑ j,c r j=E) ∧ (∀ j, ∑ r,c r j≤cap j) := by
  classical
  have hcard : Fintype.card (R × Fin E) ≤ Fintype.card (Σ j : Fin q, Fin (cap j)) := by
    simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma] using h
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  let c := fun r j => ((univ : Finset (Fin E)).filter (fun e => (emb (r,e)).1=j)).card
  refine ⟨c,?_,?_⟩
  · intro r
    have hc := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin E)))
      (t := (univ : Finset (Fin q))) (f := fun e => (emb (r,e)).1) (fun e _ => mem_univ _)
    simpa [c] using hc.symm
  · intro j
    have hs : (∑ r,c r j)=
        ((univ : Finset (R × Fin E)).filter (fun x => (emb x).1=j)).card := by
      simp only [c,card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
    have himg : (((univ : Finset (R × Fin E)).filter (fun x => (emb x).1=j)).image emb) ⊆
        (univ.filter (fun x : (Σ k : Fin q, Fin (cap k)) => x.1=j)) := by
      intro x hx
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hy).2⟩
    have hc := card_le_card himg
    rw [card_image_of_injective _ emb.injective] at hc
    have htarget : (univ.filter (fun x : (Σ k : Fin q, Fin (cap k)) => x.1=j)).card=cap j := by
      simp only [card_eq_sum_ones,sum_filter,Fintype.sum_sigma]
      simp [apply_ite]
    rw [hs]
    simpa only [htarget] using hc

theorem pack_finset {q E : ℕ} (S : Finset ℕ) (cap : Fin q → ℕ)
    (h : S.card*E ≤ ∑ j,cap j) :
    ∃ c : ℕ → Fin q → ℕ, (∀ i∈S, ∑ j,c i j=E) ∧ (∀ j, ∑ i∈S,c i j≤cap j) := by
  classical
  obtain ⟨c,hrow,hcol⟩ := pack (R := S) cap (by simpa using h)
  let d := fun i j => if hi : i∈S then c ⟨i,hi⟩ j else 0
  refine ⟨d,?_,?_⟩
  · intro i hi
    simpa [d,hi] using hrow ⟨i,hi⟩
  · intro j
    have heq : (∑ i∈S,d i j)=∑ i : S,c i j := by
      rw [← sum_attach]
      simp [d]
    rw [heq]
    exact hcol j

end PEqualNP.Outside.L_meta_29737.Packing

namespace PEqualNP.Outside.L_meta_29737.Arithmetic

open Finset

def bound (q E n : ℕ) := (((n*E)%q)+E-1)/E

theorem ceil_le {r E p : ℕ} (hE : 0 < E) (hr : r ≤ E*p) :
    (r+E-1)/E ≤ p := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hE).mpr
  have h := Nat.sub_add_cancel (by omega : 1 ≤ r+E)
  nlinarith

theorem ceil_mul {r E : ℕ} (hE : 0 < E) : r ≤ E*((r+E-1)/E) := by
  have h1 := Nat.mod_add_div (r+E-1) E
  have h2 := Nat.mod_lt (r+E-1) hE
  have h3 := Nat.sub_add_cancel (by omega : 1 ≤ r+E)
  omega

theorem bound_le (q E n : ℕ) (hE : 0 < E) : bound q E n ≤ n := by
  apply ceil_le hE
  simpa [Nat.mul_comm] using Nat.mod_le (n*E) q

theorem double_bound (q E n : ℕ) (hE : 0 < E) : bound q E (2*n) ≤ 2*bound q E n := by
  apply ceil_le hE
  have hrem : ((2*n*E)%q) ≤ 2*((n*E)%q) := by
    rw [show 2*n*E=2*(n*E) by ring,Nat.mul_mod]
    have h1 := Nat.mod_le ((2%q)*((n*E)%q)) q
    have h2 := Nat.mod_le 2 q
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  have h := ceil_mul (r := (n*E)%q) hE
  dsimp [bound]
  nlinarith

theorem floor_double {q E n : ℕ} (hq : 0 < q) :
    2*((n*E)/q) ≤ (2*n*E)/q := by
  apply (Nat.le_div_iff_mul_le hq).mpr
  have h := Nat.div_mul_le_self (n*E) q
  nlinarith

theorem capacity {q E n : ℕ} (hq : 0 < q) (hE : 0 < E) (c : Fin q → ℕ)
    (hc : ∀ j,c j ≤ (n*E)/q)
    (htotal : (∑ j,c j)+E*bound q E n=n*E) :
    (2*bound q E n-bound q E (2*n))*E ≤
      ∑ j,((2*n*E)/q-2*c j) := by
  have hle (j) : 2*c j ≤ (2*n*E)/q := by
    exact (Nat.mul_le_mul_left 2 (hc j)).trans (floor_double hq)
  have hsum : (∑ j,((2*n*E)/q-2*c j))+2*(∑ j,c j)=q*((2*n*E)/q) := by
    rw [mul_sum,← sum_add_distrib]
    simp_rw [Nat.sub_add_cancel (hle _)]
    simp
  have hrem := ceil_mul (r := (2*n*E)%q) hE
  have hdiv := Nat.mod_add_div (2*n*E) q
  have hp := double_bound q E n hE
  have hsub := congrArg (fun x : ℕ => x*E) (Nat.sub_add_cancel hp)
  change (2*n*E)%q ≤ E*bound q E (2*n) at hrem
  nlinarith

end PEqualNP.Outside.L_meta_29737.Arithmetic

namespace PEqualNP.Outside.L_meta_29737.Levels

open Finset

abbrev Hist (q E : ℕ) := {c : Fin q → ℕ // ∑ j,c j=E}

def mass {A : Type*} (L : ℕ → Option A) (n : ℕ) (g : A → ℕ) :=
  ∑ i∈range n,((L i).map g).getD 0

def holes {A : Type*} (L : ℕ → Option A) (n : ℕ) :=
  (range n).filter (fun i => (L i).isNone)

theorem total {q E n : ℕ} (L : ℕ → Option (Hist q E)) :
    (∑ j,mass L n (fun h => h.val j))+E*(holes L n).card=n*E := by
  unfold mass holes
  rw [sum_comm,card_eq_sum_ones,sum_filter,mul_sum,← sum_add_distrib]
  calc
    _ = ∑ _∈range n,E := by
      apply sum_congr rfl
      intro i hi
      cases h : L i with
      | none => simp
      | some v => simpa using v.property
    _ = _ := by simp

theorem fill {q E n p : ℕ} (L : ℕ → Option (Hist q E)) (cap : Fin q → ℕ)
    (hp : p ≤ (holes L n).card)
    (hcapacity : ((holes L n).card-p)*E ≤ ∑ j,cap j) :
    ∃ U : ℕ → Option (Hist q E),
      (∀ i h, L i=some h → U i=some h) ∧
      (holes U n).card=p ∧
      (∀ j,mass U n (fun h => h.val j) ≤ mass L n (fun h => h.val j)+cap j) := by
  classical
  obtain ⟨S,hS,hSc⟩ := exists_subset_card_eq (Nat.sub_le (holes L n).card p)
  obtain ⟨c,hrow,hcol⟩ := PEqualNP.Outside.L_meta_29737.Packing.pack_finset S cap (by simpa only [hSc] using hcapacity)
  let U := fun i => if hi : i∈S then some (⟨c i,hrow i hi⟩ : Hist q E) else L i
  have hnone (i) (hi : i∈S) : L i=none := by
    have h := (mem_filter.mp (hS hi)).2
    exact Option.isNone_iff_eq_none.mp h
  refine ⟨U,?_,?_,?_⟩
  · intro i h hi
    have hn : i∉S := by intro hs; rw [hnone i hs] at hi; contradiction
    simp [U,hn,hi]
  · have heq : holes U n=holes L n \ S := by
      ext i
      by_cases hi : i∈S
      · simp [holes,U,hi]
      · simp [holes,U,hi]
    rw [heq,card_sdiff_of_subset hS,hSc]
    omega
  · intro j
    have hterm (i) : ((U i).map (fun h => h.val j)).getD 0 =
        ((L i).map (fun h => h.val j)).getD 0+(if i∈S then c i j else 0) := by
      by_cases hi : i∈S
      · simp [U,hi,hnone i hi]
      · simp [U,hi]
    have hfilter : (range n).filter (fun i => i∈S)=S := by
      ext i
      constructor
      · intro hi; exact (mem_filter.mp hi).2
      · intro hi; exact mem_filter.mpr ⟨(mem_filter.mp (hS hi)).1,hi⟩
    unfold mass
    simp_rw [hterm]
    rw [sum_add_distrib,← sum_filter,hfilter]
    exact Nat.add_le_add_left (hcol j) _

theorem expand_mass {A : Type*} (L : ℕ → Option A) (n : ℕ) (g : A → ℕ) :
    mass (fun i => L (i/2)) (2*n) g=2*mass L n g := by
  unfold mass
  rw [PEqualNP.Outside.L_meta_29737.Tree.sum_range_double,mul_sum]
  apply sum_congr rfl
  intro i hi
  have h0 : 2*i/2=i := by omega
  have h1 : (2*i+1)/2=i := by omega
  dsimp only
  rw [h0,h1]
  omega

theorem expand_holes {A : Type*} (L : ℕ → Option A) (n : ℕ) :
    (holes (fun i => L (i/2)) (2*n)).card=2*(holes L n).card := by
  unfold holes
  simp only [card_eq_sum_ones,sum_filter]
  rw [PEqualNP.Outside.L_meta_29737.Tree.sum_range_double,mul_sum]
  apply sum_congr rfl
  intro i hi
  have h0 : 2*i/2=i := by omega
  have h1 : (2*i+1)/2=i := by omega
  rw [h0,h1]
  omega

end PEqualNP.Outside.L_meta_29737.Levels

namespace PEqualNP.Outside.L_meta_29737.Construct

open Finset PEqualNP.Outside.L_meta_29737.Levels PEqualNP.Outside.L_meta_29737.Arithmetic

def Good {q E : ℕ} (n : ℕ) (L : ℕ → Option (Hist q E)) : Prop :=
  (holes L n).card=bound q E n ∧ ∀ j,mass L n (fun h => h.val j)≤(n*E)/q

theorem initial {q E : ℕ} (hE : 0 < E) : ∃ L : ℕ → Option (Hist q E),Good 1 L := by
  let p := bound q E 1
  have hp : p ≤ 1 := bound_le q E 1 hE
  have hc : (1-p)*E ≤ ∑ _ : Fin q,E/q := by
    simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
    have h1 := ceil_mul (r := E%q) hE
    have h2 := Nat.mod_add_div E q
    have h3 := congrArg (fun x : ℕ => x*E) (Nat.sub_add_cancel hp)
    have h1' : E%q ≤ E*p := by simpa [p,bound] using h1
    nlinarith
  obtain ⟨L,_,hL,hcount⟩ := fill (n := 1) (p := p) (fun _ => none) (fun _ : Fin q => E/q)
    (by simpa [holes] using hp) (by simpa [holes] using hc)
  refine ⟨L,hL,?_⟩
  intro j
  simpa [mass] using hcount j

theorem next {q E n : ℕ} (hq : 0 < q) (hE : 0 < E)
    (L : ℕ → Option (Hist q E)) (hL : Good n L) :
    ∃ U : ℕ → Option (Hist q E),Good (2*n) U ∧
      ∀ i h,L i=some h → U (2*i)=some h ∧ U (2*i+1)=some h := by
  let c := fun j => mass L n (fun h => h.val j)
  let cap := fun j => (2*n*E)/q-2*c j
  have htotal : (∑ j,c j)+E*bound q E n=n*E := by
    have h := total (n := n) L
    rw [hL.1] at h
    exact h
  have hp : bound q E (2*n)≤(holes (fun i => L (i/2)) (2*n)).card := by
    rw [expand_holes,hL.1]
    exact double_bound q E n hE
  have hcap : ((holes (fun i => L (i/2)) (2*n)).card-bound q E (2*n))*E ≤ ∑ j,cap j := by
    rw [expand_holes,hL.1]
    exact capacity hq hE c hL.2 htotal
  obtain ⟨U,hkeep,hholes,hcounts⟩ := fill (n := 2*n) (p := bound q E (2*n))
    (fun i => L (i/2)) cap hp hcap
  refine ⟨U,⟨hholes,?_⟩,?_⟩
  · intro j
    have h := hcounts j
    rw [expand_mass] at h
    have hle : 2*c j≤(2*n*E)/q :=
      (Nat.mul_le_mul_left 2 (hL.2 j)).trans (floor_double hq)
    simpa only [cap,c,Nat.add_sub_of_le hle] using h
  · intro i h hi
    constructor
    · apply hkeep
      simpa using hi
    · apply hkeep
      simpa only [show (2*i+1)/2=i by omega] using hi

noncomputable def build {q E : ℕ} (hq : 0 < q) (hE : 0 < E) :
    (b : ℕ) → {L : ℕ → Option (Hist q E) // Good (2^b) L}
  | 0 => ⟨Classical.choose (initial hE),Classical.choose_spec (initial hE)⟩
  | b+1 =>
    let prev := build hq hE b
    let hn := next hq hE prev.val prev.property
    ⟨Classical.choose hn,by
      have h := (Classical.choose_spec hn).1
      simpa only [pow_succ,Nat.mul_comm] using h⟩

theorem build_stable {q E : ℕ} (hq : 0 < q) (hE : 0 < E) :
    PEqualNP.Outside.L_meta_29737.Tree.Stable (fun b i => (build hq hE b).val i) := by
  intro b i h hi hH
  have hs := (Classical.choose_spec (next hq hE (build hq hE b).val
    (build hq hE b).property)).2 i h hH
  exact hs

theorem build_holes {q E : ℕ} (hq : 0 < q) (hE : 0 < E) (b : ℕ) :
    PEqualNP.Outside.L_meta_29737.Tree.pending (fun b i => (build hq hE b).val i) b=bound q E (2^b) :=
  (build hq hE b).property.1

theorem build_cap {q E : ℕ} (hq : 0 < q) (hE : 0 < E) (b : ℕ) (j : Fin q) :
    PEqualNP.Outside.L_meta_29737.Tree.raw (fun b i => (build hq hE b).val i) (fun h => h.val j) b≤(2^b*E)/q :=
  (build hq hE b).property.2 j

end PEqualNP.Outside.L_meta_29737.Construct

namespace PEqualNP.Outside.L_meta_29737.Tail

def bound (q E b : ℕ) : ℕ := (((2^b*E) % q)+E-1)/E

theorem bound_le (q E b : ℕ) (hq : 0 < q) (hE : 0 < E) :
    bound q E b ≤ q := by
  unfold bound
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hE).2
  have hr := Nat.mod_lt (2^b*E) hq
  have hmul : q ≤ q * E := by nlinarith
  nlinarith [Nat.sub_le (((2^b*E) % q)+E) 1]

theorem summable_tail (q E : ℕ) (hq : 0 < q) (hE : 0 < E) :
    Summable (fun b : ℕ => (bound q E b : ℝ) / (2 : ℝ)^b) := by
  have hg : Summable (fun b : ℕ => (q : ℝ) * (1 / 2 : ℝ)^b) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _
  apply Summable.of_nonneg_of_le (fun b => by positivity) _ hg
  intro b
  have hb : (bound q E b : ℝ) ≤ q := by exact_mod_cast bound_le q E b hq hE
  calc
    (bound q E b : ℝ) / (2 : ℝ)^b ≤ (q : ℝ) / (2 : ℝ)^b :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = (q : ℝ) * (1 / 2 : ℝ)^b := by rw [div_pow]; simp [div_eq_mul_inv]

end PEqualNP.Outside.L_meta_29737.Tail

namespace PEqualNP.Outside.L_meta_29737.Sampler

open Finset Filter PEqualNP.Outside.L_meta_29737.Levels PEqualNP.Outside.L_meta_29737.Tree PEqualNP.Outside.L_meta_29737.Construct

theorem sampler {q E : ℕ} (hq : 0 < q) (hE : 0 < E) :
    ∃ T : ℕ → ℕ → Option (Hist q E),Stable T ∧
      (∀ b,pending T b=(((2^b*E)%q)+E-1)/E) ∧
      Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0) ∧
      (∀ j,Tendsto (part T (fun h => h.val j)) atTop (nhds ((E : ℝ)/(q : ℝ)))) ∧
      Summable (fun b => (pending T b : ℝ)/(2 : ℝ)^b) := by
  let T := fun b i => (build hq hE b).val i
  have hT : Stable T := build_stable hq hE
  have hpend (b) : pending T b=(((2^b*E)%q)+E-1)/E := build_holes hq hE b
  have hsumm : Summable (fun b => (pending T b : ℝ)/(2 : ℝ)^b) := by
    simpa only [hpend,PEqualNP.Outside.L_meta_29737.Tail.bound] using PEqualNP.Outside.L_meta_29737.Tail.summable_tail q E hq hE
  have hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0) :=
    hsumm.tendsto_atTop_zero
  refine ⟨T,hT,hpend,hp,?_,hsumm⟩
  have hbounded (j : Fin q) : ∀ b i (h : Hist q E), i<2^b → T b i=some h → h.val j≤E := by
    intro b i h hi hH
    exact (single_le_sum (fun k _ => Nat.zero_le _) (mem_univ j)).trans_eq h.property
  choose c hc using (fun j => part_converges T (fun h => h.val j) E hT (hbounded j))
  have hqr : (0 : ℝ)<q := by exact_mod_cast hq
  have hcap (j : Fin q) : c j≤(E : ℝ)/(q : ℝ) := by
    apply le_of_tendsto' (hc j)
    intro b
    have hn := build_cap hq hE b j
    have hn' : raw T (fun h => h.val j) b*q≤2^b*E := (Nat.le_div_iff_mul_le hq).mp hn
    have hr : (raw T (fun h => h.val j) b : ℝ)*(q : ℝ)≤(2 : ℝ)^b*(E : ℝ) := by
      exact_mod_cast hn'
    unfold part
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ)<2^b) hqr).mpr
    nlinarith
  have hsum : (∑ j,c j)=(E : ℝ) := by
    have hparts (b : ℕ) : (∑ j,part T (fun h => h.val j) b)=(E : ℝ)*part T (fun _ => 1) b := by
      rw [← part_sum]
      rw [part_congr_leaf T (fun h => ∑ j,h.val j) (fun _ => E)
        (fun b i h hi hH => h.property)]
      exact part_const T E b
    have h1 := finite_sum_tendsto univ (fun j => part T (fun h => h.val j)) c (fun j _ => hc j)
    have h2 := (onepart_tendsto T hp).const_mul (E : ℝ)
    simp only [hparts] at h1
    simpa only [mul_one] using tendsto_nhds_unique h1 h2
  have hsum' : (∑ j,c j)=∑ _ : Fin q,(E : ℝ)/(q : ℝ) := by
    rw [hsum]
    simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin]
    exact (mul_div_cancel₀ (E : ℝ) (ne_of_gt hqr)).symm
  have heq (j) : c j=(E : ℝ)/(q : ℝ) :=
    (sum_eq_sum_iff_of_le (fun j _ => hcap j)).mp hsum' j (mem_univ j)
  intro j
  simpa only [heq] using hc j

end PEqualNP.Outside.L_meta_29737.Sampler

namespace PEqualNP.Outside.L_meta_29737.Circuit

open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def Legal (N : Nat) (C : Circuit) : Prop :=
  ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
       (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Table {N : Nat} (C : Circuit) (x y : Fin N) : Bool :=
  C.eval (Represents.oneEach x y)

def push (N : Nat) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], N+N+C.size⟩

theorem pushSize (N : Nat) (C : Circuit) (g : Gate) : (push N C g).size = C.size + 1 := by
  simp [push,Circuit.size]

theorem pushPrefix (N : Nat) (C : Circuit) (g : Gate) : C.gates <+: (push N C g).gates :=
  ⟨[g],rfl⟩

theorem pushLegal {N : Nat} {C : Circuit} (hc : Legal N C) (g : Gate)
    (hinputs : ∀ i ∈ g.inputs, i < N+N+C.size)
    (hop : g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) :
    Legal N (push N C g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (C.gates ++ [g]).length at hj
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hj
    by_cases hj' : j < C.gates.length
    · have hg : gateAt (push N C g) j = gateAt C j := by
        simp [gateAt, push, List.getD_eq_getElem?_getD, List.getElem?_append_left hj']
      rw [hg] at hi
      exact hc.1 j hj' i hi
    · have he : j = C.gates.length := by omega
      subst j
      have hg : gateAt (push N C g) C.gates.length = g := by
        simp [gateAt, push, List.getD_eq_getElem?_getD]
      exact hinputs i (hg ▸ hi)
  · rw [pushSize]
    change N+N+C.size < N+N+(C.size+1)
    omega
  · intro h hh
    change h ∈ C.gates ++ [g] at hh
    rcases List.mem_append.mp hh with h1|h2
    · exact hc.2.2 h h1
    · simpa using (List.mem_singleton.mp h2 ▸ hop : h.inputs.length ≤ 2 ∧ _)

def stepVals (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem valsPrefix (gs : List Gate) (w : List Bool) :
    ∃ u, gs.foldl stepVals w = w ++ u ∧ u.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons g gs ih =>
    obtain ⟨u,hu,hl⟩ := ih (stepVals w g)
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: u,
      by rw [List.foldl_cons,hu]; simp [stepVals],by simp [hl]⟩

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.size := by
  obtain ⟨u,hu,hl⟩ := valsPrefix C.gates w
  change (C.gates.foldl stepVals w).length = _
  rw [hu,List.length_append,hl]
  rfl

theorem rawWire (C : Circuit) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (C.wires w).getD i false = w.getD i false := by
  obtain ⟨u,hu,_⟩ := valsPrefix C.gates w
  change (C.gates.foldl stepVals w).getD i false = _
  rw [hu,List.getD_append _ _ _ _ hi]

theorem pushWires (N : Nat) (C : Circuit) (g : Gate) (w : List Bool) :
    (push N C g).wires w = stepVals (C.wires w) g := by
  change (C.gates ++ [g]).foldl stepVals w = stepVals (C.gates.foldl stepVals w) g
  simp [List.foldl_append]

theorem pushEval {N : Nat} (C : Circuit) (g : Gate) {w : List Bool} (hlen : w.length = N+N) :
    (push N C g).eval w = g.op.eval (g.inputs.map fun i => (C.wires w).getD i false) := by
  have hlen' := wireLength C w
  rw [hlen] at hlen'
  change ((push N C g).wires w).getD (N+N+C.size) false = _
  rw [pushWires,← hlen']
  simp [stepVals,List.getD_eq_getElem?_getD]

theorem oldWire {N : Nat} (C : Circuit) (g : Gate) {w : List Bool} (hlen : w.length = N+N)
    (i : Nat) (hi : i < N+N+C.size) :
    ((push N C g).wires w).getD i false = (C.wires w).getD i false := by
  have h := wireLength C w
  rw [hlen] at h
  rw [pushWires,stepVals,List.getD_append _ _ _ _ (h ▸ hi)]

theorem oneLen {N : Nat} (x y : Fin N) : (Represents.oneEach x y).length = N+N := by
  simp [Represents.oneEach]

theorem leftRaw {N : Nat} (C : Circuit) (x y i : Fin N) :
    (C.wires (Represents.oneEach x y)).getD i.val false = decide (i=x) := by
  rw [rawWire _ _ _ (by rw [oneLen]; omega)]
  have hi : i.val < (List.ofFn (fun p : Fin N => decide (p=x))).length := by simp
  unfold Represents.oneEach
  rw [List.getD_append _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

theorem rightRaw {N : Nat} (C : Circuit) (x y j : Fin N) :
    (C.wires (Represents.oneEach x y)).getD (N+j.val) false = decide (j=y) := by
  rw [rawWire _ _ _ (by rw [oneLen]; omega)]
  simp [Represents.oneEach, List.getD_eq_getElem?_getD]

def invert {N : Nat} (C : Circuit) : Circuit := push N C ⟨.not,[C.output]⟩

theorem invertLegal {N : Nat} {C : Circuit} (hc : Legal N C) : Legal N (invert (N:=N) C) := by
  apply pushLegal hc
  · simpa using hc.2.1
  · simp

theorem invertTable {N : Nat} (C : Circuit) (x y : Fin N) :
    Table (invert (N:=N) C) x y = !(Table C x y) := by
  unfold Table invert
  rw [pushEval _ _ (oneLen x y)]
  rfl

def mark {N : Nat} (C : Circuit) (z : Fin N × Fin N) : Circuit :=
  let g := push N C ⟨.and,[z.1.val,N+z.2.val]⟩
  push N g ⟨.or,[C.output,g.output]⟩

theorem markLegal {N : Nat} {C : Circuit} (hc : Legal N C) (z : Fin N × Fin N) :
    Legal N (mark C z) := by
  let g : Gate := ⟨.and,[z.1.val,N+z.2.val]⟩
  have hga : Legal N (push N C g) := by
    apply pushLegal hc
    · intro i hi
      change i ∈ [z.1.val,N+z.2.val] at hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl <;> have := z.1.isLt <;> have := z.2.isLt <;> omega
    · simp [g]
  apply pushLegal hga
  · intro i hi
    change i ∈ [C.output,(push N C g).output] at hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · rw [pushSize]; have := hc.2.1; omega
    · exact hga.2.1
  · simp

theorem markTable {N : Nat} {C : Circuit} (hc : Legal N C) (z : Fin N × Fin N) (x y : Fin N) :
    Table (mark C z) x y = (Table C x y || decide ((x,y)=z)) := by
  let g : Gate := ⟨.and,[z.1.val,N+z.2.val]⟩
  let w := Represents.oneEach x y
  have hl : w.length = N+N := oneLen x y
  have hPair : (push N C g).eval w = (decide (z.1=x) && decide (z.2=y)) := by
    rw [pushEval _ _ hl]
    change ((C.wires w).getD z.1.val false && ((C.wires w).getD (N+z.2.val) false && true)) = _
    rw [leftRaw,rightRaw,Bool.and_true]
  change (push N (push N C g) ⟨.or,[C.output,(push N C g).output]⟩).eval w = _
  rw [pushEval _ _ hl]
  change (((push N C g).wires w).getD C.output false || ((push N C g).eval w || false)) = _
  rw [oldWire C g hl C.output hc.2.1,hPair,Bool.or_false]
  change (Table C x y || _) = (Table C x y || _)
  congr 1
  cases z with
  | mk a b => by_cases hx : a = x <;> by_cases hy : b = y <;> simp [Prod.mk.injEq,eq_comm,hx,hy]

theorem markSet {N : Nat} (C : Circuit) (hc : Legal N C) (S : Finset (Fin N × Fin N)) :
    ∃ D : Circuit, Legal N D ∧ C.gates <+: D.gates ∧ D.size = C.size + 2*S.card ∧
      ∀ x y : Fin N, Table D x y = (Table C x y || decide ((x,y) ∈ S)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨C,hc,List.prefix_refl _,by simp,by simp⟩
  | @insert z s hzs ih =>
    obtain ⟨D,hd,hpref,hsz,ht⟩ := ih
    have hp : D.gates <+: (mark D z).gates :=
      (pushPrefix N D _).trans (pushPrefix N _ _)
    refine ⟨mark D z,markLegal hd z,hpref.trans hp,?_,?_⟩
    · unfold mark
      rw [pushSize,pushSize,hsz,Finset.card_insert_of_notMem hzs]
      omega
    · intro x y
      rw [markTable hd z x y,ht x y]
      by_cases he : (x,y)=z <;> by_cases hm : (x,y) ∈ s <;> simp [he,hm]

theorem correct {N : Nat} (base : Circuit) (hbase : Legal N base) (H : Fin N → Fin N → Bool) :
    ∃ C : Circuit, Legal N C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size + 2*((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => H z.1 z.2 ≠ Table base z.1 z.2)).card + 3 ∧ Table C = H := by
  classical
  let bad := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 ≠ Table base z.1 z.2)
  let add := bad.filter (fun z => H z.1 z.2 = true)
  let sub := bad.filter (fun z => ¬ H z.1 z.2 = true)
  have hcard : add.card + sub.card = bad.card :=
    Finset.card_filter_add_card_filter_not (s:=bad) (fun z => H z.1 z.2 = true)
  let first := invert (N:=N) base
  obtain ⟨D,hd,hpref,hsize,ht⟩ := markSet first (invertLegal hbase) sub
  let second := invert (N:=N) D
  obtain ⟨F,hf,hpref',hsize',ht'⟩ := markSet second (invertLegal hd) add
  have hp1 : base.gates <+: first.gates := pushPrefix _ _ _
  have hp2 : D.gates <+: second.gates := pushPrefix _ _ _
  refine ⟨F,hf,(List.prefix_iff_eq_take.mp ((hp1.trans hpref).trans (hp2.trans hpref'))).symm,?_,?_⟩
  · have h1 : first.size = base.size + 1 := pushSize _ _ _
    have h2 : second.size = D.size + 1 := pushSize _ _ _
    change F.size ≤ base.size + 2*bad.card + 3
    omega
  · funext x y
    rw [ht' x y]
    rw [show Table second x y = !(Table D x y) from invertTable D x y, ht x y]
    rw [show Table first x y = !(Table base x y) from invertTable base x y]
    cases h : H x y <;> cases b : Table base x y <;> simp [add,sub,bad,h,b]

end PEqualNP.Outside.L_meta_29737.Circuit

namespace PEqualNP.Outside.L_meta_29737.Realize

open Finset PEqualNP.Outside.L_meta_29737.Loss PEqualNP.Outside.L_meta_29737.Means PEqualNP.Outside.L_meta_29737.Levels PEqualNP.Outside.L_meta_29737.Circuit

theorem realize {N q E : ℕ} (hEN : E≤N)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x,Function.Injective (fun j => f j x))
    (base : (Fin N × Fin N) → Bool) (h : Hist q E) :
    ∃ H : (Fin N × Fin N) → Bool,(edits base H).card=E ∧
      ∀ j,count f base j H=h.val j := by
  classical
  have hle (j) : h.val j≤N :=
    ((single_le_sum (fun k _ => Nat.zero_le _) (mem_univ j)).trans_eq h.property).trans hEN
  let S := Σ j : Fin q,Fin (h.val j)
  let row (a : S) : Fin N := Fin.castLE (hle a.1) a.2
  let cell (a : S) := (row a,f a.1 (row a))
  have hinj : Function.Injective cell := by
    intro a b hab
    have hr : row a=row b := congrArg Prod.fst hab
    have hj : a.1=b.1 := hf (row a) (by simpa only [cell,← hr] using congrArg Prod.snd hab)
    rcases a with ⟨j,a⟩
    rcases b with ⟨k,b⟩
    dsimp only at hj
    subst k
    have hv : a.val=b.val := congrArg (fun x : Fin N => x.val) hr
    have he : a=b := Fin.ext hv
    subst b
    rfl
  let A := (univ : Finset S).image cell
  let H := fun z => xor (base z) (decide (z∈A))
  have he : edits base H=A := by
    ext z
    by_cases hz : z∈A <;> cases hb : base z <;> simp [edits,H,hz,hb]
  have hm (a : S) (j : Fin q) : cell a∈matching f j ↔ a.1=j := by
    have hmem : cell a∈matching f j ↔ f a.1 (row a)=f j (row a) := by
      simp [matching,cell,eq_comm]
    rw [hmem]
    exact ⟨fun he => hf (row a) he,fun he => by rw [he]⟩
  refine ⟨H,?_,?_⟩
  · rw [he,card_image_of_injective _ hinj]
    simpa only [card_univ,S,Fintype.card_sigma,Fintype.card_fin] using h.property
  · intro j
    have hi : A∩matching f j=((univ : Finset S).filter (fun a => a.1=j)).image cell := by
      ext z
      constructor
      · intro hz
        obtain ⟨a,_,rfl⟩ := mem_image.mp (mem_inter.mp hz).1
        exact mem_image.mpr ⟨a,mem_filter.mpr ⟨mem_univ _,(hm a j).mp (mem_inter.mp hz).2⟩,rfl⟩
      · intro hz
        obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
        exact mem_inter.mpr ⟨mem_image.mpr ⟨a,mem_univ _,rfl⟩,(hm a j).mpr (mem_filter.mp ha).2⟩
    unfold count
    rw [he,hi,card_image_of_injective _ hinj]
    simp only [S,card_eq_sum_ones,sum_filter,Fintype.sum_sigma]
    simp [apply_ite]

theorem circuit {N q E : ℕ} (hEN : E≤N)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x,Function.Injective (fun j => f j x))
    (base : PEqualNP.CircuitLowerBounds.Circuit) (hbase : Legal N base) (h : Hist q E) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,Legal N C ∧ C.gates.take base.size=base.gates ∧
      C.size≤base.size+2*E+3 ∧
      (edits (fun z : Fin N × Fin N => Table base z.1 z.2) (fun z => Table C z.1 z.2)).card=E ∧
      ∀ j,count f (fun z => Table base z.1 z.2) j (fun z => Table C z.1 z.2)=h.val j := by
  obtain ⟨H,hcard,hcounts⟩ := realize hEN f hf (fun z => Table base z.1 z.2) h
  obtain ⟨C,hC,hpref,hsize,hTable⟩ := correct base hbase (fun x y => H (x,y))
  refine ⟨C,hC,hpref,?_,?_,?_⟩
  · change C.size≤base.size+2*(edits (fun z => Table base z.1 z.2) H).card+3 at hsize
    simpa only [hcard] using hsize
  · simpa only [hTable,Prod.eta] using hcard
  · simpa only [hTable,Prod.eta] using hcounts

end PEqualNP.Outside.L_meta_29737.Realize

namespace PEqualNP.Outside.L_meta_29737.Tree

open Finset Filter

theorem stable_map {A B : Type*} (T : ℕ → ℕ → Option A) (f : A → B) (hT : Stable T) :
    Stable (fun b i => (T b i).map f) := by
  intro b i v hi hv
  obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨h0,h1⟩ := hT b i a hi ha
  simp [h0,h1]

theorem pending_map {A B : Type*} (T : ℕ → ℕ → Option A) (f : A → B) (b : ℕ) :
    pending (fun b i => (T b i).map f) b=pending T b := by
  unfold pending
  congr 1
  apply filter_congr
  intro i hi
  cases hTi : T b i <;> simp [hTi]

theorem part_map {A B : Type*} (T : ℕ → ℕ → Option A) (f : A → B) (g : B → ℕ) (b : ℕ) :
    part (fun b i => (T b i).map f) g b=part T (fun a => g (f a)) b := by
  unfold part raw
  congr 2
  apply sum_congr rfl
  intro i hi
  cases hTi : T b i <;> simp [hTi]

theorem part_map_fun {A B : Type*} (T : ℕ → ℕ → Option A) (f : A → B) (g : B → ℕ) :
    part (fun b i => (T b i).map f) g=part T (fun a => g (f a)) := by
  funext b
  exact part_map T f g b

end PEqualNP.Outside.L_meta_29737.Tree

namespace PEqualNP.Outside.L_meta_29737.Attain

open Finset Filter PEqualNP.Outside.L_meta_29737.Loss PEqualNP.Outside.L_meta_29737.Minimax PEqualNP.Outside.L_meta_29737.Means
  PEqualNP.Outside.L_meta_29737.Levels PEqualNP.Outside.L_meta_29737.Circuit PEqualNP.Outside.L_meta_29737.Tree
open PEqualNP.CircuitLowerBounds

theorem attain {N q E t : ℕ} (hq : 0 < q) (hE : 0 < E) (hEN : E≤N) (hqt : q≤2*t)
    (base : Circuit) (hbase : Legal N base)
    (f : Fin q → Equiv.Perm (Fin N)) (hf : ∀ x,Function.Injective (fun j => f j x)) :
    ∃ T : ℕ → ℕ → Option Circuit,Stable T ∧
      (∀ b i C,i<2^b → T b i=some C → Legal N C ∧ C.gates.take base.size=base.gates ∧
        C.size≤base.size+2*E+3 ∧
        loss f (fun z => Table base z.1 z.2) (fun z => Table C z.1 z.2) ∅≤E) ∧
      (∀ b,pending T b=(((2^b*E)%q)+E-1)/E) ∧
      Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0) ∧
      (∀ D : Finset (Fin q),D.card=t →
        Tendsto (part T (fun C => loss f (fun z => Table base z.1 z.2)
          (fun z => Table C z.1 z.2) D)) atTop
          (nhds (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)))) ∧
      Summable (fun b => (pending T b : ℝ)/(2 : ℝ)^b) := by
  choose C hC using (fun h : Hist q E => PEqualNP.Outside.L_meta_29737.Realize.circuit hEN f hf base hbase h)
  obtain ⟨S,hS,hpend,hp,hmeans,hsumm⟩ := PEqualNP.Outside.L_meta_29737.Sampler.sampler hq hE
  let B := fun z : Fin N × Fin N => Table base z.1 z.2
  let g := fun D h => loss f B (fun z => Table (C h) z.1 z.2) D
  have hlim (D : Finset (Fin q)) (hD : D.card=t) :
      Tendsto (part S (g D)) atTop
        (nhds (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))) := by
    have hid (h : Hist q E) : g D h+2*(∑ j∈D,h.val j)=E+N*t := by
      have hl := loss_identity B (fun z => Table (C h) z.1 z.2) (D.biUnion (matching f))
      rw [selected_inter_card f hf,selected_card f hf,hD,(hC h).2.2.2.1] at hl
      change g D h+2*(∑ j∈D,count f B j (fun z => Table (C h) z.1 z.2))=E+N*t at hl
      have hcounts (j) : count f B j (fun z => Table (C h) z.1 z.2)=h.val j :=
        (hC h).2.2.2.2 j
      simpa only [hcounts] using hl
    have hparts (b : ℕ) : part S (g D) b =
        ((E+N*t : ℕ) : ℝ)*part S (fun _ => 1) b-
          2*(∑ j∈D,part S (fun h => h.val j) b) := by
      have heq := part_congr_leaf S (fun h => g D h+2*(∑ j∈D,h.val j)) (fun _ => E+N*t)
        (fun b i h hi hH => hid h) b
      rw [part_add,part_mul,part_sum,part_const] at heq
      norm_num only [Nat.cast_ofNat] at heq
      linarith
    have hmeanSum := finite_sum_tendsto D (fun j => part S (fun h => h.val j))
      (fun _ => (E : ℝ)/(q : ℝ)) (fun j _ => hmeans j)
    have h := ((onepart_tendsto S hp).const_mul (((E+N*t : ℕ) : ℝ))).sub
      (hmeanSum.const_mul 2)
    have heq : (((E+N*t : ℕ) : ℝ))-2*(∑ _∈D,(E : ℝ)/(q : ℝ))=
        (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) := by
      have hqr : (q : ℝ)≠0 := by exact_mod_cast ne_of_gt hq
      simp only [sum_const,nsmul_eq_mul,hD,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hqt,Nat.cast_ofNat]
      field_simp
      ring
    simpa only [← hparts,mul_one,heq] using h
  let T := fun b i => (S b i).map C
  refine ⟨T,stable_map S C hS,?_,?_,?_,?_,?_⟩
  · intro b i a hi ha
    obtain ⟨h,hh,rfl⟩ := Option.map_eq_some_iff.mp ha
    refine ⟨(hC h).1,(hC h).2.1,(hC h).2.2.1,?_⟩
    have he := (hC h).2.2.2.1
    simpa [loss,edits] using le_of_eq he
  · intro b
    exact (pending_map S C b).trans (hpend b)
  · simpa only [T,pending_map] using hp
  · intro D hD
    simpa only [T,part_map_fun] using hlim D hD
  · simpa only [T,pending_map] using hsumm

end PEqualNP.Outside.L_meta_29737.Attain

namespace PEqualNP.Outside.L_meta_29737.Curried

open Finset Filter PEqualNP.Outside.L_meta_29737.Tree PEqualNP.Outside.L_meta_29737.Loss

def Loss {N q : ℕ} (B H : Fin N → Fin N → Bool)
    (f : Fin q → Equiv.Perm (Fin N)) (D : Finset (Fin q)) : ℕ :=
  (univ.filter (fun z : Fin N × Fin N => H z.1 z.2≠
    xor (B z.1 z.2) (decide (z.2∈D.image (fun j => f j z.1))))).card

theorem selected_mem_pair {N q : ℕ} (f : Fin q → Equiv.Perm (Fin N))
    (D : Finset (Fin q)) (z : Fin N × Fin N) :
    z∈D.biUnion (matching f) ↔ z.2∈D.image (fun j => f j z.1) :=
  selected_mem f D z.1 z.2

theorem loss_eq {N q : ℕ} (B H : Fin N → Fin N → Bool)
    (f : Fin q → Equiv.Perm (Fin N)) (D : Finset (Fin q)) :
    PEqualNP.Outside.L_meta_29737.Minimax.loss f (Function.uncurry B) (Function.uncurry H) D=Loss B H f D := by
  unfold PEqualNP.Outside.L_meta_29737.Minimax.loss Loss
  congr 1
  apply filter_congr
  intro z hz
  simp only [selected_mem_pair,Function.uncurry]

theorem loss_empty {N q : ℕ} (B H : Fin N → Fin N → Bool)
    (f : Fin q → Equiv.Perm (Fin N)) :
    Loss B H f ∅=(edits (Function.uncurry B) (Function.uncurry H)).card := by
  simp [Loss,edits,Function.uncurry] <;> rfl

theorem lower {N q E t : ℕ} (hq : 0 < q) (hE : 0 < E) (hqt : q < 2*t) (htq : t < q)
    (B : Fin N → Fin N → Bool) (f : Fin q → Equiv.Perm (Fin N))
    (hf : ∀ x,Function.Injective (fun j => f j x))
    (T : ℕ → ℕ → Option (Fin N → Fin N → Bool)) (hT : Stable T)
    (hbudget : ∀ b i H,i<2^b → T b i=some H → Loss B H f ∅≤E)
    (hp : Tendsto (fun b => (pending T b : ℝ)/(2 : ℝ)^b) atTop (nhds 0)) :
    (∃ D : Finset (Fin q),∃ z : ℝ,D.card=t ∧
      (((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))≤z ∧
      Tendsto (part T (fun H => Loss B H f D)) atTop (nhds z)) ∧
    ((∀ D : Finset (Fin q),D.card=t → ∃ z : ℝ,
      Tendsto (part T (fun H => Loss B H f D)) atTop (nhds z) ∧
      z≤(((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ))) →
      ∀ b,(((2^b*E)%q)+E-1)/E≤pending T b) := by
  let U := fun b i => (T b i).map Function.uncurry
  have hU : Stable U := stable_map T Function.uncurry hT
  have hpU : Tendsto (fun b => (pending U b : ℝ)/(2 : ℝ)^b) atTop (nhds 0) := by
    simpa only [U,pending_map] using hp
  have hEU : ∀ b i H,i<2^b → U b i=some H → (edits (Function.uncurry B) H).card≤E := by
    intro b i H hi hH
    obtain ⟨H',hH',rfl⟩ := Option.map_eq_some_iff.mp hH
    simpa only [loss_empty] using hbudget b i H' hi hH'
  have hpart (D : Finset (Fin q)) (b : ℕ) :
      part U (fun H => PEqualNP.Outside.L_meta_29737.Minimax.loss f (Function.uncurry B) H D) b=
        part T (fun H => Loss B H f D) b := by
    simp only [U,part_map,loss_eq]
  constructor
  · obtain ⟨D,z,hD,hz,hlim⟩ := PEqualNP.Outside.L_meta_29737.Minimax.minimax hq (by omega) (le_of_lt hqt)
      (le_of_lt htq) f hf (Function.uncurry B) U hU hEU hpU
    exact ⟨D,z,hD,hz,by simpa only [funext (hpart D)] using hlim⟩
  · intro hopt
    have hoptU : ∀ D : Finset (Fin q),D.card=t → ∃ z : ℝ,
        Tendsto (part U (fun H => PEqualNP.Outside.L_meta_29737.Minimax.loss f (Function.uncurry B) H D))
          atTop (nhds z) ∧ z≤(((N*t : ℕ) : ℝ)-(((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)) := by
      simpa only [funext (hpart _)] using hopt
    have h := PEqualNP.Outside.L_meta_29737.Stopping.optimal_stopping_bound hq hE hqt htq f hf
      (Function.uncurry B) U hU hEU hpU hoptU
    simpa only [U,pending_map] using h

end PEqualNP.Outside.L_meta_29737.Curried

theorem PEqualNP.Outside.L_meta_29737 : (∀ (N q E t : ℕ), 0 < N → 0 < q → 0 < E → E ≤ N → q < 2*t → t < q →
  let X := Fin N
  let I := Fin q
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun C : Circ =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  ∀ (base : Circ), legal base → ∀ f : I → Equiv.Perm X,
    (∀ x : X, Function.Injective (fun j => f j x)) →
    let loss := fun (H : X → X → Bool) (D : Finset I) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 ≠
        xor (table base z.1 z.2) (decide (z.2 ∈ D.image (fun j => f j z.1))))).card
    let fits := fun C : Circ => legal C ∧ C.gates.take base.size = base.gates ∧
      C.size ≤ base.size+2*E+3 ∧ loss (table C) ∅ ≤ E
    let ideal := ((N*t : ℕ) : ℝ) - (((2*t-q)*E : ℕ) : ℝ)/(q : ℝ)
    let stable := fun (A : Type) (T : ℕ → ℕ → Option A) =>
      ∀ b i v, i < 2^b → T b i = some v →
        T (b+1) (2*i) = some v ∧ T (b+1) (2*i+1) = some v
    let pending := fun (A : Type) (T : ℕ → ℕ → Option A) (b : ℕ) =>
      ((Finset.range (2^b)).filter (fun i => (T b i).isNone)).card
    let part := fun (A : Type) (T : ℕ → ℕ → Option A) (g : A → ℕ) (b : ℕ) =>
      ((∑ i ∈ Finset.range (2^b), ((T b i).map g).getD 0 : ℕ) : ℝ)/(2 : ℝ)^b
    let bound := fun b : ℕ => (((2^b*E) % q)+E-1)/E
    let Table := X → X → Bool
    (∀ T : ℕ → ℕ → Option Table, stable Table T →
      (∀ b i H, i < 2^b → T b i = some H → loss H ∅ ≤ E) →
      Filter.Tendsto (fun b => (pending Table T b : ℝ)/(2 : ℝ)^b) Filter.atTop (nhds 0) →
      (∃ (D : Finset I) (z : ℝ), D.card = t ∧ ideal ≤ z ∧
        Filter.Tendsto (part Table T (fun H => loss H D)) Filter.atTop (nhds z)) ∧
      ((∀ D : Finset I, D.card = t → ∃ z : ℝ,
        Filter.Tendsto (part Table T (fun H => loss H D)) Filter.atTop (nhds z) ∧ z ≤ ideal) →
      ∀ b : ℕ, bound b ≤ pending Table T b)) ∧
    ∃ T : ℕ → ℕ → Option Circ, stable Circ T ∧
      (∀ b i C, i < 2^b → T b i = some C → fits C) ∧
      (∀ b : ℕ, pending Circ T b = bound b) ∧
      Filter.Tendsto (fun b => (pending Circ T b : ℝ)/(2 : ℝ)^b) Filter.atTop (nhds 0) ∧
      (∀ D : Finset I, D.card = t →
        Filter.Tendsto (part Circ T (fun C => loss (table C) D)) Filter.atTop (nhds ideal)) ∧
      Summable (fun b : ℕ => (pending Circ T b : ℝ)/(2 : ℝ)^b)) := by
  intro N q E t hN hq hE hEN hqt htq
  dsimp only
  intro base hbase f hf
  constructor
  · intro T hT hbudget hp
    exact PEqualNP.Outside.L_meta_29737.Curried.lower hq hE hqt htq
      (fun x y => base.eval (PEqualNP.Represents.oneEach x y)) f hf T hT hbudget hp
  · have h := PEqualNP.Outside.L_meta_29737.Attain.attain hq hE hEN (le_of_lt hqt) base hbase f hf
    unfold PEqualNP.Outside.L_meta_29737.Tree.part PEqualNP.Outside.L_meta_29737.Tree.raw at h
    simpa only [PEqualNP.Outside.L_meta_29737.Tree.Stable,PEqualNP.Outside.L_meta_29737.Tree.pending,PEqualNP.Outside.L_meta_29737.Tree.part,
      PEqualNP.Outside.L_meta_29737.Tree.raw,PEqualNP.Outside.L_meta_29737.Circuit.Legal,PEqualNP.Outside.L_meta_29737.Circuit.Table,
      PEqualNP.Outside.L_meta_29737.Minimax.loss,PEqualNP.Outside.L_meta_29737.Curried.selected_mem_pair] using h
