import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1176.Work
abbrev Hidden (b : Nat) := Finset (Fin b × Bool)
abbrev Clause (b n : Nat) := Finset ((Fin n × Bool) × Bool) × Hidden b
def Holds {b} (D : Hidden b) (h : Fin b → Bool) := ∃ l ∈ D, h l.1 = l.2
def Feasible (s b n : Nat) := ∃ C : Finset (Clause b n),
  (∀ x : Fin n → Bool → Bool, (∃ i, x i false=true ∧ x i true=true) ↔
      ∃ h : Fin b → Bool, ∀ c ∈ C, (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ Holds c.2 h) ∧
  (∀ c ∈ C, c.1.card+c.2.card ≤ 3) ∧ C.card ≤ 2*n+s
private def clauses4 : Finset (Clause 1 4) := (Finset.univ : Finset (Bool × Bool × Bool)).image fun t =>
  let fst : Fin 4 := if t.1 then 2 else 0
  let snd : Fin 4 := if t.1 then 3 else 1
  ( {((fst,t.2.1),true), ((snd,t.2.2),true)}, {((0 : Fin 1), t.1)})
set_option maxRecDepth 8192 in
private theorem enc4 : ∀ x : Fin 4 → Bool → Bool, (∃ i, x i false=true ∧ x i true=true) ↔
    ∃ h : Fin 1 → Bool, ∀ c ∈ clauses4, (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ Holds c.2 h := by
  unfold Holds clauses4
  decide +kernel
private theorem width4 : ∀ t : Bool × Bool × Bool,
  let fst : Fin 4 := if t.1 then 2 else 0
  let snd : Fin 4 := if t.1 then 3 else 1
  let cl : Clause 1 4 := ({((fst,t.2.1),true), ((snd,t.2.2),true)}, {((0 : Fin 1), t.1)})
  cl.1.card+cl.2.card ≤ 3 := by decide +kernel
private theorem card4 : clauses4.card = 8 := by decide +kernel
theorem feasibleFour (s : Nat) : Feasible s 1 4 := by
  refine ⟨clauses4, enc4, ?_, ?_⟩
  · intro c hc
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hc
    exact width4 t
  · rw [card4]; omega
def lim (s : Nat) := let p := (3*s)*(3*s+1)/2; max 1 ((2*p)*((2*p)-1)/2+2*p)
def Result (s b n : Nat) := ∃ c d : Nat, 0<c ∧ c≤b ∧ c≤lim s ∧ Feasible s c d ∧ n+2*c≤d+2*b
theorem direct (s b n : Nat) (hb : 0 < b) (hlt : b ≤ lim s) (f : Feasible s b n) : Result s b n :=
  ⟨b,n,hb,le_rfl,hlt,f,le_rfl⟩
theorem small (s b n : Nat) (hb : 0 < b) (hsmall : n ≤ 2*b+2) : Result s b n :=
  ⟨1,4,by decide,hb, Nat.le_max_left _ _,feasibleFour s,by omega⟩
def UnsatCore {b} (K : Finset (Hidden b)) :=
  (∀ h : Fin b → Bool, ∃ D ∈ K, ¬Holds D h) ∧
  (∀ D ∈ K, ∃ h : Fin b → Bool, ∀ E ∈ K, E ≠ D → Holds E h) ∧
  (∀ D ∈ K, 1 ≤ D.card ∧ D.card ≤ 3)
def load {b} (K : Finset (Hidden b)) := (K.filter (fun D => D.card ≤ 2)).card + (K.filter (fun D => D.card = 1)).card
def triples {b} (K : Finset (Hidden b)) := (K.filter (fun D => D.card = 3)).card
theorem enoughClauses {b} {K : Finset (Hidden b)} (hu : UnsatCore K) : K.card ≤ load K + triples K := by
  classical
  have eq : K.filter (fun D => ¬D.card ≤ 2) = K.filter (fun D => D.card = 3) := by
    ext D
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hm,hh⟩; have := (hu.2.2 D hm).2; exact ⟨hm,by omega⟩
    · rintro ⟨hm,hh⟩; exact ⟨hm,by omega⟩
  have hh := Finset.card_filter_add_card_filter_not (s := K) (p := fun D => D.card ≤ 2)
  rw [eq] at hh
  unfold triples load; omega
abbrev CoreIff := ∀ (s b n : Nat), 4 ≤ n → (Feasible s b n ↔ ∃ K : Finset (Hidden b), UnsatCore K ∧ n ≤ load K ∧ triples K ≤ s ∧ K.card ≤ n+s)
abbrev Compress := ∀ (s b : Nat) (K : Finset (Hidden b)), 0 < b → lim s < b → 2*b+2 < load K → UnsatCore K → triples K ≤ s → ∃ (c : Nat) (H : Finset (Hidden c)), 0 < c ∧ c ≤ b ∧ c ≤ lim s ∧ UnsatCore H ∧ triples H ≤ s ∧ load K ≤ load H + 2*(b-c)
theorem assemble (hiff : CoreIff) (hcomp : Compress) (s b n : Nat) (hb : 0<b) (hf : Feasible s b n) : Result s b n := by
  by_cases hb' : b ≤ lim s
  · exact direct s b n hb hb' hf
  by_cases hn : n ≤ 2*b+2
  · exact small s b n hb hn
  obtain ⟨K,hK,hload,ht,_⟩ := (hiff s b n (by omega)).mp hf
  obtain ⟨c,H,hc,hcb,hcl,hH,htr,hsize⟩ := hcomp s b K hb (by omega) (by omega) hK ht
  have hwidth := enoughClauses hH
  have hd : 4 ≤ load H := by omega
  exact ⟨c,load H,hc,hcb,hcl,(hiff s c (load H) hd).mpr ⟨H,hH,le_rfl,htr,by omega⟩,by omega⟩
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Pcx277_aux

open PEqualNP.ProofComplexity
open Classical

abbrev Raw (m n : ℕ) := Fin m × Fin n
abbrev Cl (m n h : ℕ) := Clause (Sum (Raw m n) (Fin h))
abbrev Hid (h : ℕ) := Clause (Fin h)

def Consistent {h : ℕ} (U : Finset (Hid h)) : Prop :=
  ∃ z : Fin h → Bool, Satisfies z (↑U : Set _)

def RawSat {m n h : ℕ} (x : Raw m n → Bool) (C : Cl m n h) : Prop :=
  ∃ (p : Raw m n) (b : Bool), (Sum.inl p, b) ∈ C ∧ x p = b

noncomputable def hidPart {m n h : ℕ} (C : Cl m n h) : Hid h :=
  Finset.univ.filter (fun l : Fin h × Bool => (Sum.inr l.1, l.2) ∈ C)

noncomputable def posBlocks {m n h : ℕ} (C : Cl m n h) : Finset (Fin m) :=
  Finset.univ.filter (fun j : Fin m => ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C)

lemma mem_hidPart {m n h : ℕ} {C : Cl m n h} {l : Fin h × Bool} :
    l ∈ hidPart C ↔ (Sum.inr l.1, l.2) ∈ C := by
  simp [hidPart]

lemma mem_posBlocks {m n h : ℕ} {C : Cl m n h} {j : Fin m} :
    j ∈ posBlocks C ↔ ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C := by
  simp [posBlocks]

lemma sum_union_le_nat {α : Type*} [DecidableEq α]
    (s t : Finset α) (w : α → ℕ) :
    ∑ x ∈ s ∪ t, w x ≤ (∑ x ∈ s, w x) + ∑ x ∈ t, w x := by
  have h1 : s ∪ t = s ∪ (t \ s) := by
    ext x
    simp
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, w x ≤ ∑ x ∈ t, w x :=
    Finset.sum_le_sum_of_subset Finset.sdiff_subset
  omega

lemma sum_image_le_nat {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : β → ℕ) :
    ∑ y ∈ s.image f, w y ≤ ∑ x ∈ s, w (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hmem]
      omega
    · rw [Finset.sum_insert hmem]
      omega

lemma sum_biUnion_le_nat {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (w : β → ℕ) :
    ∑ y ∈ s.biUnion t, w y ≤ ∑ x ∈ s, ∑ y ∈ t x, w y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (sum_union_le_nat (t a) (s.biUnion t) w) (Nat.add_le_add_left ih _)

lemma exists_cover_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (g : α → ℕ) :
    ∀ S : Finset β, ∑ a ∈ U, g a = S.card →
      ∃ B : α → Finset β,
        (∀ a ∈ U, B a ⊆ S) ∧
        (∀ a ∈ U, (B a).card = g a) ∧
        (∀ j ∈ S, ∃ a ∈ U, j ∈ B a) := by
  induction U using Finset.induction_on with
  | empty =>
    intro S hS
    simp only [Finset.sum_empty] at hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp hS.symm
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro j hj; rw [hSe] at hj; simp at hj
  | insert a s ha ih =>
    intro S hS
    rw [Finset.sum_insert ha] at hS
    have hle : g a ≤ S.card := by omega
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hle
    have hcard_un : (S \ A).card + A.card = S.card := by
      have hdisj : Disjoint (S \ A) A := Finset.sdiff_disjoint
      have hun : (S \ A) ∪ A = S := Finset.sdiff_union_of_subset hAS
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hun] at hc
      exact hc.symm
    have hrem : ∑ x ∈ s, g x = (S \ A).card := by omega
    obtain ⟨B', hB'sub, hB'card, hB'cov⟩ := ih (S \ A) hrem
    refine ⟨fun x => if x = a then A else B' x, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAS]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact Finset.Subset.trans (hB'sub x hxs) Finset.sdiff_subset
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAcard]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact hB'card x hxs
    · intro j hj
      by_cases hjA : j ∈ A
      · exact ⟨a, Finset.mem_insert_self a s, by simp [hjA]⟩
      · have hjs : j ∈ S \ A := Finset.mem_sdiff.mpr ⟨hj, hjA⟩
        obtain ⟨x, hxs, hjx⟩ := hB'cov j hjs
        have hne : x ≠ a := fun h => ha (h ▸ hxs)
        exact ⟨x, Finset.mem_insert_of_mem hxs, by simp [hne, hjx]⟩

noncomputable def mkClause {m n h : ℕ} (H : Hid h) (B : Finset (Fin m)) (f : ↥B → Fin n) : Cl m n h :=
  H.image (fun l => (Sum.inr l.1, l.2)) ∪
  (Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true))

lemma mkClause_card {m n h : ℕ} (H : Hid h) (B : Finset (Fin m)) (f : ↥B → Fin n) :
    (mkClause H B f).card = H.card + B.card := by
  have hdisj : Disjoint (H.image (fun l : Fin h × Bool => (Sum.inr l.1, l.2)))
      ((Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨l, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨j, _, hEq⟩
    cases hEq
  rw [mkClause, Finset.card_union_of_disjoint hdisj]
  have hinj1 : Function.Injective (fun l : Fin h × Bool => ((Sum.inr l.1 : Sum (Raw m n) (Fin h)), l.2)) := by
    intro l1 l2 hEq
    rcases l1 with ⟨v1, b1⟩
    rcases l2 with ⟨v2, b2⟩
    injection hEq with hv hb
    injection hv with hv'
    subst hv'
    subst hb
    rfl
  have hinj2 : Function.Injective (fun j : ↥B => ((Sum.inl (j.1, f j) : Sum (Raw m n) (Fin h)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    have hj : j1.1 = j2.1 := congrArg Prod.fst hp
    exact Subtype.ext hj
  rw [Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2]
  simp

lemma backward_dir {n m h W K : ℕ} (price : ℕ → ℕ)
    (U : Finset (Hid h)) (g : Hid h → ℕ)
    (hunsat : ¬ Consistent U)
    (hmin : ∀ H ∈ U, Consistent (U.erase H))
    (hsum : ∑ H ∈ U, g H = m)
    (hW : ∀ H ∈ U, H.card + g H ≤ W)
    (hK : ∑ H ∈ U, n ^ (g H) * price (H.card + g H) ≤ K) :
    ∃ F : Finset (Cl m n h),
      (∀ x : Raw m n → Bool,
        (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
          ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _)) ∧
      (∀ C ∈ F, C.card ≤ W) ∧
      (∑ C ∈ F, price C.card) ≤ K := by
  have hcardU : (Finset.univ : Finset (Fin m)).card = m := Fintype.card_fin m
  obtain ⟨B, _, hBcard, hBcov⟩ :=
    exists_cover_card U g (Finset.univ : Finset (Fin m)) (by rw [hsum, hcardU])
  let F : Finset (Cl m n h) :=
    U.biUnion (fun H => (Finset.univ : Finset (↥(B H) → Fin n)).image (mkClause H (B H)))
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨j0, hj0⟩
      obtain ⟨H0, hH0U, hj0B⟩ := hBcov j0 (Finset.mem_univ j0)
      obtain ⟨z, hz⟩ := hmin H0 hH0U
      refine ⟨z, ?_⟩
      intro C hC
      have hCF : C ∈ F := Finset.mem_coe.mp hC
      rcases Finset.mem_biUnion.mp hCF with ⟨H, hHU, hCH⟩
      rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
      by_cases hEq : H = H0
      · subst hEq
        refine ⟨(Sum.inl (j0, f ⟨j0, hj0B⟩), true), ?_, ?_⟩
        · rw [mkClause]
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨⟨j0, hj0B⟩, Finset.mem_univ _, rfl⟩
        · simpa [Sum.elim] using hj0 (f ⟨j0, hj0B⟩)
      · have hHer : H ∈ (↑(U.erase H0) : Set _) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hEq, hHU⟩)
        obtain ⟨l, hlH, hlz⟩ := hz H hHer
        refine ⟨(Sum.inr l.1, l.2), ?_, ?_⟩
        · rw [mkClause]
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr ⟨l, hlH, rfl⟩
        · simpa [Sum.elim] using hlz
    · rintro ⟨z, hz⟩
      by_contra hno
      push Not at hno
      have hbad : ∃ H0 ∈ U, ¬ ClauseSat z H0 := by
        by_contra hall
        push Not at hall
        apply hunsat
        exact ⟨z, fun H hH => hall H (Finset.mem_coe.mp hH)⟩
      obtain ⟨H0, hH0U, hH0nsat⟩ := hbad
      have hpick : ∀ j : ↥(B H0), ∃ i : Fin n, x (j.1, i) = false := by
        intro j
        obtain ⟨i, hi⟩ := hno j.1
        cases hx : x (j.1, i)
        · exact ⟨i, hx⟩
        · exact False.elim (hi hx)
      let f : ↥(B H0) → Fin n := fun j => Classical.choose (hpick j)
      have hf : ∀ j : ↥(B H0), x (j.1, f j) = false :=
        fun j => Classical.choose_spec (hpick j)
      have hmem : mkClause H0 (B H0) f ∈ (↑F : Set _) := by
        rw [Finset.mem_coe]
        exact Finset.mem_biUnion.mpr ⟨H0, hH0U, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩
      obtain ⟨l, hlC, hlsat⟩ := hz (mkClause H0 (B H0) f) hmem
      rw [mkClause] at hlC
      rcases Finset.mem_union.mp hlC with hl1 | hl2
      · rcases Finset.mem_image.mp hl1 with ⟨lh, hlh, rfl⟩
        apply hH0nsat
        exact ⟨lh, hlh, by simpa [Sum.elim] using hlsat⟩
      · rcases Finset.mem_image.mp hl2 with ⟨j, _, rfl⟩
        have hxtrue : x (j.1, f j) = true := by simpa [Sum.elim] using hlsat
        rw [hf j] at hxtrue
        cases hxtrue
  · intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨H, hHU, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [mkClause_card, hBcard H hHU]
    exact hW H hHU
  · calc
      ∑ C ∈ F, price C.card
        ≤ ∑ H ∈ U, ∑ C ∈ (Finset.univ : Finset (↥(B H) → Fin n)).image (mkClause H (B H)),
            price C.card := sum_biUnion_le_nat U _ (fun C : Cl m n h => price C.card)
      _ ≤ ∑ H ∈ U, ∑ f : ↥(B H) → Fin n, price (mkClause H (B H) f).card := by
          apply Finset.sum_le_sum
          intro H _
          exact sum_image_le_nat Finset.univ (mkClause H (B H)) (fun C : Cl m n h => price C.card)
      _ = ∑ H ∈ U, n ^ (g H) * price (H.card + g H) := by
          apply Finset.sum_congr rfl
          intro H hHU
          have hconst : ∀ f : ↥(B H) → Fin n,
              price (mkClause H (B H) f).card = price (H.card + g H) := by
            intro f
            rw [mkClause_card, hBcard H hHU]
          simp_rw [hconst]
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_coe, hBcard H hHU]
      _ ≤ K := hK

lemma exists_minimal_unsat {h : ℕ} :
    ∀ k : ℕ, ∀ U0 : Finset (Hid h), U0.card ≤ k → ¬ Consistent U0 →
      ∃ U ⊆ U0, ¬ Consistent U ∧ ∀ H ∈ U, Consistent (U.erase H) := by
  intro k
  induction k with
  | zero =>
    intro U0 hcard hunsat
    have hU0 : U0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exfalso
    apply hunsat
    refine ⟨fun _ => false, ?_⟩
    intro H hH
    rw [hU0] at hH
    simp at hH
  | succ k ih =>
    intro U0 hcard hunsat
    by_cases hmin : ∀ H ∈ U0, Consistent (U0.erase H)
    · exact ⟨U0, Finset.Subset.refl _, hunsat, hmin⟩
    · push Not at hmin
      obtain ⟨H, hHU0, her⟩ := hmin
      have hlt : (U0.erase H).card < U0.card := Finset.card_erase_lt_of_mem hHU0
      have hle : (U0.erase H).card ≤ k := by omega
      obtain ⟨U, hUsub, hUunsat, hUmin⟩ := ih (U0.erase H) hle her
      exact ⟨U, Finset.Subset.trans hUsub (Finset.erase_subset H U0), hUunsat, hUmin⟩

def xAssign {m n : ℕ} (α : Fin m → Fin n) : Raw m n → Bool :=
  fun p => decide (p.2 ≠ α p.1)

def xFlip {m n : ℕ} (α : Fin m → Fin n) (j0 : Fin m) : Raw m n → Bool :=
  fun p => if p.1 = j0 then true else xAssign α p

lemma xAssign_eq_false {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = false ↔ i = α j := by
  simp [xAssign]

lemma xAssign_eq_true {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = true ↔ i ≠ α j := by
  simp [xAssign]

lemma rawSat_xFlip_of_not_xAssign {m n h : ℕ} (α : Fin m → Fin n) (j0 : Fin m)
    {C : Cl m n h} (hnot : ¬ RawSat (xAssign α) C) (hsat : RawSat (xFlip α j0) C) :
    (Sum.inl (j0, α j0), true) ∈ C := by
  obtain ⟨⟨j, i⟩, b, hmem, heq⟩ := hsat
  by_cases hj : j = j0
  · subst hj
    have hb : b = true := by
      simp [xFlip] at heq
      exact heq
    subst hb
    have hi : i = α j := by
      by_contra hne
      apply hnot
      refine ⟨(j, i), true, hmem, ?_⟩
      exact (xAssign_eq_true α j i).mpr hne
    subst hi
    exact hmem
  · exfalso
    apply hnot
    refine ⟨(j, i), b, hmem, ?_⟩
    simpa [xFlip, hj] using heq

lemma card_filter_not_rawSat_le {m n h : ℕ} (C : Cl m n h) :
    (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card ≤
      n ^ (m - (posBlocks C).card) := by
  let P := posBlocks C
  let S := Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)
  let T : Finset (↥(Pᶜ) → Fin n) := Finset.univ
  have hinj : Set.InjOn (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) (↑S : Set _) := by
    intro α1 h1 α2 h2 hfun
    have h1' : ¬ RawSat (xAssign α1) C := (Finset.mem_filter.mp h1).2
    have h2' : ¬ RawSat (xAssign α2) C := (Finset.mem_filter.mp h2).2
    funext j
    by_cases hj : j ∈ P
    · obtain ⟨i, hi⟩ := mem_posBlocks.mp hj
      have h1i : α1 j = i := by
        by_contra hne
        apply h1'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α1 j i).mpr (Ne.symm hne)⟩
      have h2i : α2 j = i := by
        by_contra hne
        apply h2'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α2 j i).mpr (Ne.symm hne)⟩
      rw [h1i, h2i]
    · have hjc : j ∈ Pᶜ := Finset.mem_compl.mpr hj
      exact congrFun hfun ⟨j, hjc⟩
  have hmaps : Set.MapsTo (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1)
      (↑S : Set _) (↑T : Set _) := by
    intro α _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  have hle := Finset.card_le_card_of_injOn
    (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) hmaps hinj
  have hTcard : T.card = n ^ (Pᶜ).card := by
    change (Finset.univ : Finset (↥(Pᶜ) → Fin n)).card = n ^ (Pᶜ).card
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hPcompl : (Pᶜ).card = m - P.card := by
    have hsum : (Pᶜ).card + P.card = m := by
      have hd : Disjoint (Pᶜ) P := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_compl.mp hx1) hx2
      have hu : Pᶜ ∪ P = Finset.univ := by
        ext x
        by_cases hx : x ∈ P
        · simp [hx]
        · simp [hx]
      have hc := Finset.card_union_of_disjoint hd
      rw [hu, Finset.card_univ, Fintype.card_fin] at hc
      exact hc.symm
    omega
  rw [hTcard, hPcompl] at hle
  exact hle

lemma card_hid_add_pos_le {m n h : ℕ}
    (α : Fin m → Fin n) (C : Cl m n h) (B : Finset (Fin m))
    (hB : ∀ j ∈ B, (Sum.inl (j, α j), true) ∈ C) :
    (hidPart C).card + B.card ≤ C.card := by
  let A1 : Cl m n h := (hidPart C).image (fun l => (Sum.inr l.1, l.2))
  let A2 : Cl m n h := B.image (fun j => (Sum.inl (j, α j), true))
  have hsub : A1 ∪ A2 ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨l, hl, rfl⟩
      exact mem_hidPart.mp hl
    · rcases Finset.mem_image.mp h2 with ⟨j, hj, rfl⟩
      exact hB j hj
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    rcases Finset.mem_image.mp h1 with ⟨l, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
    cases hEq
  have hinj1 : Function.Injective (fun l : Fin h × Bool => ((Sum.inr l.1 : Sum (Raw m n) (Fin h)), l.2)) := by
    intro l1 l2 hEq
    rcases l1 with ⟨v1, b1⟩
    rcases l2 with ⟨v2, b2⟩
    injection hEq with hv hb
    injection hv with hv'
    subst hv'
    subst hb
    rfl
  have hinj2 : Function.Injective (fun j : Fin m => ((Sum.inl (j, α j) : Sum (Raw m n) (Fin h)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    exact congrArg Prod.fst hp
  have hc1 : A1.card = (hidPart C).card := Finset.card_image_of_injective _ hinj1
  have hc2 : A2.card = B.card := Finset.card_image_of_injective _ hinj2
  have hcu : (A1 ∪ A2).card = A1.card + A2.card := Finset.card_union_of_disjoint hdisj
  have hle : (A1 ∪ A2).card ≤ C.card := Finset.card_le_card hsub
  omega

lemma exists_alpha_data {n m h W : ℕ} (hn : 0 < n) (price : ℕ → ℕ)
    (hmono : ∀ lo hi, lo ≤ hi → price lo ≤ price hi)
    (F : Finset (Cl m n h))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _))
    (hW : ∀ C ∈ F, C.card ≤ W)
    (α : Fin m → Fin n) :
    ∃ (U : Finset (Hid h)) (g : Hid h → ℕ),
      ¬ Consistent U ∧
      (∀ H ∈ U, Consistent (U.erase H)) ∧
      (∑ H ∈ U, g H) = m ∧
      (∀ H ∈ U, H.card + g H ≤ W) ∧
      (∑ H ∈ U, n ^ (g H) * price (H.card + g H)) ≤
        ∑ C ∈ F.filter (fun C => ¬ RawSat (xAssign α) C),
          n ^ (posBlocks C).card * price C.card := by
  let Fα : Finset (Cl m n h) := F.filter (fun C => ¬ RawSat (xAssign α) C)
  let Uα : Finset (Hid h) := Fα.image hidPart
  have hUα_unsat : ¬ Consistent Uα := by
    rintro ⟨z, hz⟩
    have hsatF : Satisfies (Sum.elim (xAssign α) z) (↑F : Set _) := by
      intro C hC
      have hCF : C ∈ F := Finset.mem_coe.mp hC
      by_cases hraw : RawSat (xAssign α) C
      · obtain ⟨p, b, hmem, heq⟩ := hraw
        exact ⟨(Sum.inl p, b), hmem, by simpa [Sum.elim] using heq⟩
      · have hCFα : C ∈ Fα := Finset.mem_filter.mpr ⟨hCF, hraw⟩
        have hHU : hidPart C ∈ (↑Uα : Set _) :=
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨C, hCFα, rfl⟩)
        obtain ⟨l, hl, hzl⟩ := hz (hidPart C) hHU
        exact ⟨(Sum.inr l.1, l.2), mem_hidPart.mp hl, by simpa [Sum.elim] using hzl⟩
    have hyes : ∃ j : Fin m, ∀ i : Fin n, xAssign α (j, i) = true :=
      (henc (xAssign α)).mpr ⟨z, hsatF⟩
    obtain ⟨j, hj⟩ := hyes
    have htrue := hj (α j)
    have hfalse : xAssign α (j, α j) = false := (xAssign_eq_false α j (α j)).mpr rfl
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨U, hUsub, hUunsat, hUmin⟩ :=
    exists_minimal_unsat Uα.card Uα (le_refl _) hUα_unsat
  have hphi_ex : ∀ j : Fin m, ∃ H ∈ U, ∀ C ∈ Fα, hidPart C = H → (Sum.inl (j, α j), true) ∈ C := by
    intro j
    have hyes : ∃ j' : Fin m, ∀ i : Fin n, xFlip α j (j', i) = true :=
      ⟨j, fun i => by simp [xFlip]⟩
    obtain ⟨z, hz⟩ := (henc (xFlip α j)).mp hyes
    have hbad : ∃ H ∈ U, ¬ ClauseSat z H := by
      by_contra hall
      push Not at hall
      exact hUunsat ⟨z, fun H hH => hall H (Finset.mem_coe.mp hH)⟩
    obtain ⟨H, hHU, hHnsat⟩ := hbad
    refine ⟨H, hHU, ?_⟩
    intro C hCFα hhid
    have hCF : C ∈ (↑F : Set _) := Finset.mem_coe.mpr (Finset.mem_filter.mp hCFα).1
    have hnot : ¬ RawSat (xAssign α) C := (Finset.mem_filter.mp hCFα).2
    obtain ⟨l, hlC, hlsat⟩ := hz C hCF
    rcases l with ⟨v, b⟩
    rcases v with p | hv
    · have hrawflip : RawSat (xFlip α j) C := ⟨p, b, hlC, by simpa [Sum.elim] using hlsat⟩
      exact rawSat_xFlip_of_not_xAssign α j hnot hrawflip
    · exfalso
      apply hHnsat
      have hlH : (hv, b) ∈ H := by
        rw [← hhid]
        exact mem_hidPart.mpr hlC
      exact ⟨(hv, b), hlH, by simpa [Sum.elim] using hlsat⟩
  let φ : Fin m → Hid h := fun j => Classical.choose (hphi_ex j)
  have hφU : ∀ j : Fin m, φ j ∈ U := fun j => (Classical.choose_spec (hphi_ex j)).1
  have hφC : ∀ (j : Fin m) (C : Cl m n h), C ∈ Fα → hidPart C = φ j →
      (Sum.inl (j, α j), true) ∈ C :=
    fun j => (Classical.choose_spec (hphi_ex j)).2
  let g : Hid h → ℕ := fun H => (Finset.univ.filter (fun j : Fin m => φ j = H)).card
  have hgsum : ∑ H ∈ U, g H = m := by
    have h1 : ∑ H ∈ U, (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
        (Finset.univ : Finset (Fin m)).card := by
      have hcard_eq : ∀ H : Hid h,
          (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
          ∑ j : Fin m, if φ j = H then 1 else 0 := by
        intro H
        simp [Finset.sum_boole]
      simp_rw [hcard_eq]
      rw [Finset.sum_comm]
      have hinner : ∀ j : Fin m, (∑ H ∈ U, if φ j = H then 1 else 0) = 1 := by
        intro j
        rw [Finset.sum_ite_eq U (φ j) (fun _ => 1)]
        simp [hφU j]
      simp_rw [hinner]
      simp
    rw [h1, Finset.card_univ, Fintype.card_fin]
  have hpick_ex : ∀ H ∈ U, ∃ C ∈ Fα, hidPart C = H := by
    intro H hHU
    exact Finset.mem_image.mp (hUsub hHU)
  let pickC : Hid h → Cl m n h := fun H =>
    if hHU : H ∈ U then Classical.choose (hpick_ex H hHU) else ∅
  have hpick_mem : ∀ H ∈ U, pickC H ∈ Fα := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).1
  have hpick_hid : ∀ H ∈ U, hidPart (pickC H) = H := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).2
  have hcard_le : ∀ H ∈ U, H.card + g H ≤ (pickC H).card := by
    intro H hHU
    have hB : ∀ j ∈ Finset.univ.filter (fun j : Fin m => φ j = H),
        (Sum.inl (j, α j), true) ∈ pickC H := by
      intro j hj
      have hjEq : φ j = H := (Finset.mem_filter.mp hj).2
      exact hφC j (pickC H) (hpick_mem H hHU) (by rw [hpick_hid H hHU, hjEq])
    have hle := card_hid_add_pos_le α (pickC H)
      (Finset.univ.filter (fun j : Fin m => φ j = H)) hB
    rw [hpick_hid H hHU] at hle
    exact hle
  have hg_le_pos : ∀ H ∈ U, g H ≤ (posBlocks (pickC H)).card := by
    intro H hHU
    apply Finset.card_le_card
    intro j hj
    have hjEq : φ j = H := (Finset.mem_filter.mp hj).2
    apply mem_posBlocks.mpr
    refine ⟨α j, ?_⟩
    exact hφC j (pickC H) (hpick_mem H hHU) (by rw [hpick_hid H hHU, hjEq])
  refine ⟨U, g, hUunsat, hUmin, hgsum, ?_, ?_⟩
  · intro H hHU
    exact le_trans (hcard_le H hHU) (hW (pickC H) (Finset.mem_filter.mp (hpick_mem H hHU)).1)
  · have hterm : ∀ H ∈ U,
        n ^ (g H) * price (H.card + g H) ≤
          n ^ (posBlocks (pickC H)).card * price (pickC H).card := by
      intro H hHU
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_right hn (hg_le_pos H hHU)
      · exact hmono _ _ (hcard_le H hHU)
    have h1 : ∑ H ∈ U, n ^ (g H) * price (H.card + g H) ≤
        ∑ H ∈ U, n ^ (posBlocks (pickC H)).card * price (pickC H).card :=
      Finset.sum_le_sum hterm
    have hinj : Set.InjOn pickC (↑U : Set _) := by
      intro H1 h1 H2 h2 hEq
      have h1' : H1 ∈ U := Finset.mem_coe.mp h1
      have h2' : H2 ∈ U := Finset.mem_coe.mp h2
      rw [← hpick_hid H1 h1', ← hpick_hid H2 h2', hEq]
    have h2 : ∑ H ∈ U, n ^ (posBlocks (pickC H)).card * price (pickC H).card =
        ∑ C ∈ U.image pickC, n ^ (posBlocks C).card * price C.card := by
      symm
      exact Finset.sum_image hinj
    have hsub : U.image pickC ⊆ Fα := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨H, hHU, rfl⟩
      exact hpick_mem H hHU
    have h3 : ∑ C ∈ U.image pickC, n ^ (posBlocks C).card * price C.card ≤
        ∑ C ∈ Fα, n ^ (posBlocks C).card * price C.card :=
      Finset.sum_le_sum_of_subset hsub
    exact le_trans h1 (by rw [h2]; exact h3)

lemma forward_dir {n m h W K : ℕ} (hn : 0 < n) (price : ℕ → ℕ)
    (hmono : ∀ lo hi, lo ≤ hi → price lo ≤ price hi)
    (F : Finset (Cl m n h))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _))
    (hW : ∀ C ∈ F, C.card ≤ W)
    (hK : ∑ C ∈ F, price C.card ≤ K) :
    ∃ (U : Finset (Hid h)) (g : Hid h → ℕ),
      ¬ Consistent U ∧
      (∀ H ∈ U, Consistent (U.erase H)) ∧
      (∑ H ∈ U, g H) = m ∧
      (∀ H ∈ U, H.card + g H ≤ W) ∧
      (∑ H ∈ U, n ^ (g H) * price (H.card + g H)) ≤ K := by
  let w : Cl m n h → ℕ := fun C => n ^ (posBlocks C).card * price C.card
  let score : (Fin m → Fin n) → ℕ := fun α =>
    ∑ C ∈ F.filter (fun C => ¬ RawSat (xAssign α) C), w C
  have hsum_le : ∑ α : Fin m → Fin n, score α ≤ n ^ m * K := by
    have hrewrite : ∑ α : Fin m → Fin n, score α =
        ∑ C ∈ F, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C := by
      have h1 : ∀ α : Fin m → Fin n,
          score α = ∑ C ∈ F, if ¬ RawSat (xAssign α) C then w C else 0 := by
        intro α
        simp [score, Finset.sum_filter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hrewrite]
    have hterm : ∀ C ∈ F,
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C ≤
          n ^ m * price C.card := by
      intro C _
      have hcard := card_filter_not_rawSat_le C
      have hp_le : (posBlocks C).card ≤ m := by
        calc
          (posBlocks C).card ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = m := by simp
      calc
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C
          ≤ n ^ (m - (posBlocks C).card) * (n ^ (posBlocks C).card * price C.card) :=
            Nat.mul_le_mul_right (w C) hcard
        _ = (n ^ (m - (posBlocks C).card) * n ^ (posBlocks C).card) * price C.card := by
            rw [Nat.mul_assoc]
        _ = n ^ m * price C.card := by
            rw [← Nat.pow_add, Nat.sub_add_cancel hp_le]
    calc
      ∑ C ∈ F, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C
        ≤ ∑ C ∈ F, n ^ m * price C.card := Finset.sum_le_sum hterm
      _ = n ^ m * ∑ C ∈ F, price C.card := by rw [← Finset.mul_sum]
      _ ≤ n ^ m * K := Nat.mul_le_mul_left (n ^ m) hK
  have hex : ∃ α : Fin m → Fin n, score α ≤ K := by
    by_contra hall
    push Not at hall
    have hgt : n ^ m * (K + 1) ≤ ∑ α : Fin m → Fin n, score α := by
      have h1 : ∑ _α : Fin m → Fin n, (K + 1) ≤ ∑ α : Fin m → Fin n, score α :=
        Finset.sum_le_sum (fun α _ => hall α)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin] at h1
      exact h1
    have hpos : 0 < n ^ m := Nat.pow_pos hn
    have hstrict : n ^ m * K < n ^ m * (K + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    omega
  obtain ⟨α, hα⟩ := hex
  obtain ⟨U, g, hunsat, hmin, hsum, hWU, hcost⟩ :=
    exists_alpha_data hn price hmono F henc hW α
  exact ⟨U, g, hunsat, hmin, hsum, hWU, le_trans hcost hα⟩

end PEqualNP.Outside.L_lib_1176.Pcx277_aux

namespace PEqualNP.Outside.L_lib_1176
theorem Pcx277 :
∀ (n m hiddenCount W K : ℕ), 0 < n → 0 < m → ∀ price : ℕ → ℕ, (∀ lo hi, lo ≤ hi → price lo ≤ price hi) →
  let Raw := Fin m × Fin n
  let Cl := PEqualNP.ProofComplexity.Clause (Sum Raw (Fin hiddenCount))
  let Hidden := PEqualNP.ProofComplexity.Clause (Fin hiddenCount)
  let enc := fun F : Finset Cl => ∀ x : Raw → Bool,
    (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
      ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x z) (↑F : Set _)
  let consistent := fun U : Finset Hidden =>
    ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑U : Set _)
  (∃ F : Finset Cl, enc F ∧ (∀ C ∈ F, C.card ≤ W) ∧
    (∑ C ∈ F, price C.card) ≤ K) ↔
  ∃ (U : Finset Hidden) (g : Hidden → ℕ),
    ¬ consistent U ∧ (∀ H ∈ U, consistent (U.erase H)) ∧
    (∑ H ∈ U, g H) = m ∧ (∀ H ∈ U, H.card + g H ≤ W) ∧
    (∑ H ∈ U, n^(g H) * price (H.card + g H)) ≤ K := by
  intro n m hiddenCount W K hn _hm price hmono
  dsimp only
  constructor
  · rintro ⟨F, henc, hW, hK⟩
    exact PEqualNP.Outside.L_lib_1176.Pcx277_aux.forward_dir hn price hmono F henc hW hK
  · rintro ⟨U, g, hunsat, hmin, hsum, hW, hK⟩
    exact PEqualNP.Outside.L_lib_1176.Pcx277_aux.backward_dir price U g hunsat hmin hsum hW hK
end PEqualNP.Outside.L_lib_1176

namespace PEqualNP.Outside.L_lib_1176.Work
def Oriented {b} (K : Finset (Hidden b)) := ∀ D∈K, D.card≤2 → ∃ v : Fin b, (v,false)∈D
private def actBit (toggle v : Bool) := if toggle then !v else v
private theorem act_twice (t v : Bool) : actBit t (actBit t v)=v := by cases t <;> cases v <;> rfl
private theorem act_equiv (t u v : Bool) : actBit t u=v ↔ u=actBit t v := by cases t <;> cases u <;> cases v <;> decide
private def flit {b} (a : Fin b → Bool) : (Fin b × Bool) ↪ (Fin b × Bool) where
  toFun l := (l.1,actBit (a l.1) l.2)
  inj' := by
    rintro ⟨i,s⟩ ⟨j,t⟩ he
    have hij : i=j := congrArg Prod.fst he
    subst j
    have ht : actBit (a i) s=actBit (a i) t := congrArg Prod.snd he
    have ha := congrArg (actBit (a i)) ht
    simpa only [act_twice] using congrArg (fun v => (i,v)) ha
private def fcl {b} (a : Fin b → Bool) : Hidden b ↪ Hidden b where
  toFun D := D.map (flit a)
  inj' := Finset.map_injective _
private theorem flip_card {b} (a : Fin b → Bool) (D : Hidden b) : (fcl a D).card=D.card := Finset.card_map _
private theorem flip_holds {b} (a h : Fin b → Bool) (D : Hidden b) :
    Holds (fcl a D) h ↔ Holds D (fun v => actBit (a v) (h v)) := by
  constructor
  · rintro ⟨l,hl,he⟩
    obtain ⟨⟨v,s⟩,hv,rfl⟩ := Finset.mem_map.mp hl
    exact ⟨(v,s),hv,(act_equiv ..).mpr he⟩
  · rintro ⟨⟨v,s⟩,hv,he⟩
    exact ⟨_,Finset.mem_map.mpr ⟨(v,s),hv,rfl⟩,(act_equiv ..).mp he⟩
private theorem flip_core {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (a : Fin b → Bool) : UnsatCore (K.map (fcl a)) := by
  refine ⟨?_,?_,?_⟩
  · intro h
    obtain ⟨D,hd,hn⟩ := hu.1 (fun v => actBit (a v) (h v))
    exact ⟨_,Finset.mem_map.mpr ⟨D,hd,rfl⟩,fun H => hn ((flip_holds ..).mp H)⟩
  · intro W hw; obtain ⟨D,hd,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨h,hh⟩ := hu.2.1 D hd
    refine ⟨fun v => actBit (a v) (h v),?_⟩
    intro F hf hne; obtain ⟨E,he,rfl⟩ := Finset.mem_map.mp hf
    apply (flip_holds ..).mpr
    simpa only [act_twice] using hh E he (fun he => hne (congrArg _ he))
  · intro W hw; obtain ⟨D,hd,rfl⟩ := Finset.mem_map.mp hw
    rw [flip_card]; exact hu.2.2 D hd
private theorem flip_filter {b} (K : Finset (Hidden b)) (a : Fin b → Bool) (p : Nat → Prop) [DecidablePred p] :
    ((K.map (fcl a)).filter (fun D => p D.card)).card = (K.filter (fun D => p D.card)).card := by
  have eq : (K.map (fcl a)).filter (fun D => p D.card) = (K.filter (fun D => p D.card)).map (fcl a) := by
    ext D
    simp only [Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨⟨E,he,rfl⟩,hE⟩; exact ⟨E,⟨he,by simpa [flip_card] using hE⟩,rfl⟩
    · rintro ⟨E,⟨he,hE⟩,rfl⟩; exact ⟨⟨E,he,rfl⟩,by simpa [flip_card] using hE⟩
  rw [eq,Finset.card_map]
theorem orientCore {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (hpos : 0<triples K) :
    ∃ N : Finset (Hidden b), UnsatCore N ∧ load N=load K ∧ triples N=triples K ∧ Oriented N := by
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hpos
  obtain ⟨ht,h3⟩ := Finset.mem_filter.mp hT
  obtain ⟨a,ha⟩ := hu.2.1 T ht
  refine ⟨K.map (fcl a),flip_core hu a,?_,flip_filter K a (fun n => n=3),?_⟩
  · unfold load; rw [flip_filter K a (fun n => n≤2),flip_filter K a (fun n => n=1)]
  · intro D hd hs; obtain ⟨E,he,rfl⟩ := Finset.mem_map.mp hd
    have hn : E ≠ T := by intro h; subst E; rw [flip_card] at hs; omega
    obtain ⟨⟨v,s⟩,hl,hsig⟩ := ha E he hn
    refine ⟨v,Finset.mem_map.mpr ⟨(v,s),hl,?_⟩⟩
    change (v,actBit (a v) s)=(v,false)
    change a v=s at hsig; rw [hsig]; cases s <;> rfl
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Work
private def mergeVar {b} (x y z : Fin b) := if z=x then y else z
private def mergeD {b} (x y : Fin b) (D : Hidden b) := D.image (fun l => (mergeVar x y l.1,l.2))
private def implD {b} (x y : Fin b) : Hidden b := {(y,false),(x,true)}
private def contract {b} (K : Finset (Hidden b)) (x y : Fin b) := (K.erase (implD x y)).image (mergeD x y)
private theorem holds_merge {b} (x y : Fin b) (D : Hidden b) (h : Fin b → Bool) :
    Holds (mergeD x y D) h ↔ Holds D (fun z => h (mergeVar x y z)) := by
  constructor
  · rintro ⟨l,hl,he⟩; obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hl; exact ⟨r,hr,he⟩
  · rintro ⟨r,hr,he⟩; exact ⟨_,Finset.mem_image_of_mem _ hr,he⟩
private theorem merge_witness {b} {x y : Fin b} {D : Hidden b} {h : Fin b → Bool} (hl : (x,true) ∉ D)
    (hi : Holds (implD x y) h) (hd : Holds D h) : Holds (mergeD x y D) h := by
  have hyx : h y = true → h x = true := by
    obtain ⟨l,hm,he⟩ := hi; simp only [implD,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> simp_all
  apply (holds_merge ..).mpr
  obtain ⟨⟨v,sign⟩,hv,he⟩ := hd
  refine ⟨(v,sign),hv,?_⟩
  by_cases hx : v=x
  · subst v
    cases sign with
    | true => exact False.elim (hl hv)
    | false =>
      simp only [mergeVar,ite_true] at *
      cases e : h y <;> simp_all
  · simpa [mergeVar,hx] using he
private theorem impl_always {b} (x y : Fin b) (h : Fin b → Bool) : Holds (implD x y) (fun z => h (mergeVar x y z)) := by
  have hy : mergeVar x y y = y := by simp [mergeVar]
  cases hv : h y with
  | true => exact ⟨(x,true),by simp [implD],by simpa [mergeVar] using hv⟩
  | false => exact ⟨(y,false),by simp [implD],by simpa [hy] using hv⟩
private theorem contracted_unsat {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (x y : Fin b) :
    ∀ h : Fin b → Bool, ∃ D∈contract K x y, ¬Holds D h := by
  intro h
  obtain ⟨D,hm,hd⟩ := hu.1 (fun z => h (mergeVar x y z))
  have hne : D ≠ implD x y := by rintro rfl; exact hd (impl_always ..)
  exact ⟨_,Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hne,hm⟩),fun hp => hd ((holds_merge ..).mp hp)⟩
private theorem merged_witnesses {b} {K : Finset (Hidden b)} (hu : UnsatCore K) {x y : Fin b}
    (hI : implD x y ∈ K) (hs : ∀ D∈K, D ≠ implD x y → (x,true) ∉ D) {D : Hidden b} (hm : D∈K.erase (implD x y)) :
    ∃ h : Fin b → Bool, ¬Holds (mergeD x y D) h ∧ ∀ E∈K.erase (implD x y), E≠D → Holds (mergeD x y E) h := by
  obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hm
  obtain ⟨h,hw⟩ := hu.2.1 D hmem
  have hi := hw (implD x y) hI (Ne.symm hne)
  have hh : ∀ E∈K.erase (implD x y), E≠D → Holds (mergeD x y E) h := by
    intro E he hE; obtain ⟨h1,h2⟩ := Finset.mem_erase.mp he; exact merge_witness (hs _ h2 h1) hi (hw _ h2 hE)
  refine ⟨h,?_,hh⟩
  intro hp; obtain ⟨F,hF,hbad⟩ := contracted_unsat hu x y h
  obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hF
  by_cases de : E=D
  · exact hbad (de ▸ hp)
  · exact hbad (hh E hE de)
private theorem merge_injective {b} {K : Finset (Hidden b)} (hu : UnsatCore K) {x y : Fin b}
    (hI : implD x y ∈ K) (hs : ∀ D∈K, D ≠ implD x y → (x,true) ∉ D) : Set.InjOn (mergeD x y) ↑(K.erase (implD x y)) := by
  intro A ha B hb eq
  by_contra ne
  obtain ⟨h,hA,hB⟩ := merged_witnesses hu hI hs ha
  exact hA (eq ▸ hB B hb (Ne.symm ne))
private theorem merge_nonempty {b} {D : Hidden b} (hd : 1 ≤ D.card) (x y : Fin b) : 1 ≤ (mergeD x y D).card := by
  obtain ⟨l,hl⟩ := Finset.card_pos.mp hd
  exact Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ hl⟩
private theorem merge_width {b} (D : Hidden b) (x y : Fin b) : (mergeD x y D).card ≤ D.card := Finset.card_image_le
private theorem contracted_core {b} {K : Finset (Hidden b)} (hu : UnsatCore K) {x y : Fin b}
    (hI : implD x y ∈ K) (hs : ∀ D∈K, D ≠ implD x y → (x,true) ∉ D) : UnsatCore (contract K x y) := by
  refine ⟨contracted_unsat hu x y,?_,?_⟩
  · intro W hW; obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨h,_,hw⟩ := merged_witnesses hu hI hs hD
    exact ⟨h,fun F hF hne => by obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hF; exact hw E hE (fun he => hne (congrArg _ he))⟩
  · intro W hW; obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hW
    have h := hu.2.2 D (Finset.mem_of_mem_erase hD)
    exact ⟨merge_nonempty h.1 x y, (merge_width ..).trans h.2⟩
private theorem lossOne {α} [DecidableEq α] (K : Finset α) (I : α) (p : α → Prop) [DecidablePred p] :
    (K.filter p).card ≤ ((K.erase I).filter p).card+1 := by
  have hsub : K.filter p ⊆ insert I ((K.erase I).filter p) := by
    intro a ha; obtain ⟨hm,hp⟩ := Finset.mem_filter.mp ha
    by_cases he : a=I
    · simp [he]
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨he,hm⟩,hp⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
private theorem filteredMerge {b} {K : Finset (Hidden b)} {x y : Fin b}
    (hinj : Set.InjOn (mergeD x y) ↑(K.erase (implD x y)))
    (p : Hidden b → Prop) [DecidablePred p]
    (hok : ∀ D∈K.erase (implD x y), p D → p (mergeD x y D)) :
    ((K.erase (implD x y)).filter p).card ≤ ((contract K x y).filter p).card := by
  let A := (K.erase (implD x y)).filter p
  have inj : Set.InjOn (mergeD x y) (↑A) := fun _ ha _ hb h => hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 h
  have hsize := Finset.card_image_of_injOn inj
  have sub : A.image (mergeD x y) ⊆ (contract K x y).filter p := by
    intro a ha; obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hm,hok _ hm hp⟩
  have H := Finset.card_le_card sub
  rw [hsize] at H; exact H
theorem suppressIncoming {b} (K : Finset (Hidden b)) (hu : UnsatCore K) {x y : Fin b} (hne : x≠y)
    (hI : {(y,false),(x,true)} ∈ K)
    (hs : ∀ D∈K, D ≠ {(y,false),(x,true)} → (x,true) ∉ D) :
    ∃ H : Finset (Hidden b), UnsatCore H ∧ load K ≤ load H+2 ∧ triples H ≤ triples K ∧
      ∀ D∈H, ∀ l∈D, l.1 ≠ x := by
  have inj := merge_injective hu hI hs
  refine ⟨contract K x y, contracted_core hu hI hs, ?_,?_,?_⟩
  · let p := fun D : Hidden b => D.card ≤ 2
    let q := fun D : Hidden b => D.card = 1
    have hp := filteredMerge inj p (fun D _ h => (merge_width D x y).trans h)
    have hq := filteredMerge inj q (fun D _ h => by
      have h1 := merge_nonempty (D:=D) (show 1 ≤ D.card by simpa [q] using h.ge) x y
      have h2 := merge_width D x y
      change D.card=1 at h; change (mergeD x y D).card=1; omega)
    have lp := lossOne K (implD x y) p
    have lq := lossOne K (implD x y) q
    change (K.filter p).card+(K.filter q).card ≤ ((contract K x y).filter p).card+((contract K x y).filter q).card+2
    omega
  · let T := K.filter (fun D => D.card=3)
    have sub : (contract K x y).filter (fun D => D.card=3) ⊆ T.image (mergeD x y) := by
      intro W hw; obtain ⟨hm,hc⟩ := Finset.mem_filter.mp hw
      obtain ⟨D,hd,rfl⟩ := Finset.mem_image.mp hm
      have hK := Finset.mem_of_mem_erase hd
      have h1 := (hu.2.2 D hK).2; have h2 := merge_width D x y
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hK,by omega⟩)
    exact (Finset.card_le_card sub).trans Finset.card_image_le
  · intro D hd l hl
    obtain ⟨E,_,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hl
    by_cases hr : r.1=x
    · simpa [mergeVar,hr] using Ne.symm hne
    · simpa [mergeVar,hr] using hr
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Work.Obstruction
open Relation
variable {V : Type*}
abbrev Reach (E : V → V → Prop) := ReflTransGen E

def Model (E N : V → V → Prop) (H : V → Prop) : Prop :=
  (∀ x y, E x y → H x → H y) ∧ ∀ x y, N x y → H x → H y → False

structure Cert (V : Type*) where
  paths : Finset (V × V)
  negs : Finset (V × V)

def Valid (E N : V → V → Prop) (c : Cert V) :=
  c.paths.card ≤ 2 ∧ c.negs.card ≤ 1 ∧ (∀ p ∈ c.paths, Reach E p.1 p.2) ∧ ∀ p ∈ c.negs, N p.1 p.2

def Respects (c : Cert V) (H : V → Prop) :=
  (∀ p ∈ c.paths, H p.1 → H p.2) ∧ ∀ p ∈ c.negs, H p.1 → H p.2 → False

def Conflict (E N : V → V → Prop) (a b : V) :=
  ∃ x y, Reach E a x ∧ Reach E b y ∧ (N x y ∨ N y x)

private theorem conflict_swap {E N : V → V → Prop} {a b} (h : Conflict E N a b) : Conflict E N b a := by
  obtain ⟨x,y,hx,hy,h⟩ := h
  exact ⟨y,x,hy,hx,h.symm⟩

private def Handles (E N : V → V → Prop) (c : Cert V) (a b : V) :=
  ∀ H, Respects c H → (Reach E a b → H a → H b) ∧
    ((a = b ∨ (¬Reach E a b ∧ ¬Reach E b a)) → Conflict E N a b → H a → H b → False)

private theorem pairCert (E N : V → V → Prop) (a b : V) :
    ∃ c : Cert V, Valid E N c ∧ Handles E N c a b ∧ Handles E N c b a := by
  classical
  by_cases ho : (a = b ∨ (¬Reach E a b ∧ ¬Reach E b a)) ∧ Conflict E N a b
  · obtain ⟨shape,x,y,hx,hy,hneg⟩ := ho
    let P : Finset (V × V) := {(a,x),(b,y)}
    let d := if N x y then (x,y) else (y,x)
    let c : Cert V := ⟨P,{d}⟩
    have va : Valid E N c := by
      refine ⟨(Finset.card_insert_le ..).trans (by simp),by simp [c],?_,?_⟩
      · intro p hp; simp only [c,P,Finset.mem_insert,Finset.mem_singleton] at hp
        rcases hp with rfl | rfl <;> assumption
      · intro p hp; simp only [c,Finset.mem_singleton] at hp; subst p
        dsimp [d]; split <;> simp_all
    have ban : ∀ H, Respects c H → H a → H b → False := by
      intro H h ha hb
      have h1 := h.1 (a,x) (by simp [c,P]) ha
      have h2 := h.1 (b,y) (by simp [c,P]) hb
      have hn := h.2 d (by simp [c]); dsimp [d] at hn; split at hn
      · exact hn h1 h2
      · exact hn h2 h1
    refine ⟨c,va,?_,?_⟩
    · intro H h; exact ⟨by rcases shape with rfl | hs <;> tauto,fun _ _ => ban H h⟩
    · intro H h; exact ⟨by rcases shape with rfl | hs <;> tauto,fun _ _ hb ha => ban H h ha hb⟩
  · let P := ({(a,b),(b,a)} : Finset (V × V)).filter (fun p => Reach E p.1 p.2)
    let c : Cert V := ⟨P,∅⟩
    have va : Valid E N c := by
      refine ⟨Finset.card_filter_le .. |>.trans ((Finset.card_insert_le ..).trans (by simp)),by simp [c],?_,by simp [c]⟩
      exact fun p hp => (Finset.mem_filter.mp hp).2
    refine ⟨c,va,?_,?_⟩
    · intro H h; refine ⟨fun hr => h.1 (a,b) (by simp [c,P,hr]),?_⟩
      exact fun hs hc => (ho ⟨hs,hc⟩).elim
    · intro H h; refine ⟨fun hr => h.1 (b,a) (by simp [c,P,hr]),?_⟩
      intro hs hc; apply False.elim; apply ho; refine ⟨?_,conflict_swap hc⟩
      rcases hs with hs | ⟨h1,h2⟩
      · exact Or.inl hs.symm
      · exact Or.inr ⟨h2,h1⟩

def Preserves (M : Finset V) (E N : V → V → Prop) (C : Finset (Cert V)) :=
  ∀ H : V → Prop, (∀ c ∈ C, Respects c H) → ∃ F : V → Prop, Model E N F ∧ ∀ a ∈ M, F a ↔ H a

theorem cover (M : Finset V) (E N : V → V → Prop) : ∃ C : Finset (Cert V),
    C.card ≤ M.card * (M.card + 1) / 2 ∧ (∀ c ∈ C, Valid E N c) ∧ Preserves M E N C := by
  classical
  have cert : ∀ z : Sym2 V, ∃ c, Valid E N c ∧ ∀ a b, s(a,b) = z → Handles E N c a b := by
    intro z; induction z using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨c,hc,h1,h2⟩ := pairCert E N x y
      refine ⟨c,hc,?_⟩; intro a b hab
      rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
  choose f vf hf using cert
  let C := M.sym2.image f
  refine ⟨C, Finset.card_image_le.trans (by simp [Finset.card_sym2,Nat.choose_two_right,Nat.mul_comm]),?_,?_⟩
  · intro c hc; obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hc; exact vf z
  intro H h
  have hand (a b) (ha : a ∈ M) (hb : b ∈ M) := hf s(a,b) a b rfl H
    (h _ (Finset.mem_image.mpr ⟨_,Finset.mk_mem_sym2_iff.mpr ⟨ha,hb⟩,rfl⟩))
  let F := fun x => ∃ a ∈ M, H a ∧ Reach E a x
  refine ⟨F,⟨?_,?_⟩,?_⟩
  · rintro x y hxy ⟨a,ha,hh,hr⟩; exact ⟨a,ha,hh,hr.tail hxy⟩
  · rintro x y hn ⟨a,ha,pa,ra⟩ ⟨b,hb,pb,rb⟩
    by_cases hab : Reach E a b
    · exact (hand a a ha ha).2 (Or.inl rfl) ⟨x,y,ra,hab.trans rb,Or.inl hn⟩ pa pa
    by_cases hba : Reach E b a
    · exact (hand b b hb hb).2 (Or.inl rfl) ⟨x,y,hba.trans ra,rb,Or.inl hn⟩ pb pb
    exact (hand a b ha hb).2 (Or.inr ⟨hab,hba⟩) ⟨x,y,ra,rb,Or.inl hn⟩ pa pb
  · intro x hx; constructor
    · rintro ⟨a,ha,pa,ra⟩; exact (hand a x ha hx).1 ra pa
    · exact fun px => ⟨x,hx,px,.refl⟩

theorem preserve {E N E' N' : V → V → Prop} {M : Finset V} {C : Finset (Cert V)}
    (keep : Preserves M E N C)
    (paths : ∀ c ∈ C, ∀ p ∈ c.paths, Reach E' p.1 p.2)
    (negs : ∀ c ∈ C, ∀ p ∈ c.negs, N' p.1 p.2) {H} (hm : Model E' N' H) :
    ∃ F, Model E N F ∧ ∀ a ∈ M, F a ↔ H a := by
  apply keep H; intro c hc; constructor
  · have closed {a b} (hr : Reach E' a b) (ha : H a) : H b := by
      induction hr with
      | refl => exact ha
      | tail _ he ih => exact hm.1 _ _ he ih
    exact fun p hp => closed (paths c hc p hp)
  · exact fun p hp => hm.2 _ _ (negs c hc p hp)

theorem forced {E N E' N' : V → V → Prop} {M : Finset V} {C : Finset (Cert V)}
    (Q : (V → Prop) → Prop)
    (localQ : ∀ H F, (∀ a ∈ M, F a ↔ H a) → Q H → Q F)
    (unsat : ∀ F, Model E N F → Q F → False)
    (minE : ∀ a b, E a b → ∃ H, Q H ∧ Model (fun x y => E x y ∧ (x,y) ≠ (a,b)) N H)
    (minN : ∀ a b, N a b → ∃ H, Q H ∧ Model E (fun x y => N x y ∧ (x,y) ≠ (a,b)) H)
    (subE : ∀ a b, E' a b → E a b) (subN : ∀ a b, N' a b → N a b)
    (keep : Preserves M E N C)
    (paths : ∀ c ∈ C, ∀ p ∈ c.paths, Reach E' p.1 p.2)
    (negs : ∀ c ∈ C, ∀ p ∈ c.negs, N' p.1 p.2) :
    (∀ a b, E a b → E' a b) ∧ ∀ a b, N a b → N' a b := by
  classical
  have bad (H) (qh : Q H) (hh : Model E' N' H) : False := by
    obtain ⟨F,hf,agree⟩ := preserve keep paths negs hh
    exact unsat F hf (localQ H F agree qh)
  constructor
  · intro a b hab; by_contra hn
    obtain ⟨H,qh,he,hN⟩ := minE a b hab
    apply bad H qh; constructor
    · intro x y exy; apply he x y; refine ⟨subE _ _ exy,?_⟩
      rintro ⟨⟩; exact hn exy
    · exact fun x y h => hN x y (subN _ _ h)
  · intro a b hab; by_contra hn
    obtain ⟨H,qh,he,hN⟩ := minN a b hab
    apply bad H qh; constructor
    · exact fun x y h => he x y (subE _ _ h)
    · intro x y nxy; apply hN x y; refine ⟨subN _ _ nxy,?_⟩
      rintro ⟨⟩; exact hn nxy

theorem requests (M : Finset V) (E N : V → V → Prop) :
    ∃ P B : Finset (V × V),
      P.card ≤ 2 * (M.card * (M.card + 1) / 2) ∧
      B.card ≤ M.card * (M.card + 1) / 2 ∧
      (∀ p ∈ P, Reach E p.1 p.2) ∧ (∀ p ∈ B, N p.1 p.2) ∧
      ∀ (E' N' : V → V → Prop), (∀ p ∈ P, Reach E' p.1 p.2) →
        (∀ p ∈ B, N' p.1 p.2) → ∀ H, Model E' N' H →
          ∃ F, Model E N F ∧ ∀ a ∈ M, F a ↔ H a := by
  classical
  obtain ⟨C,hc,hvalid,keep⟩ := cover M E N
  have bound (f : Cert V → Finset (V × V)) (n : Nat) (hh : ∀ c ∈ C, (f c).card ≤ n) :
      (C.biUnion f).card ≤ n * (M.card * (M.card + 1) / 2) := calc
    _ ≤ ∑ c ∈ C, (f c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, n := Finset.sum_le_sum hh
    _ = n * C.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left n hc
  refine ⟨C.biUnion Cert.paths,C.biUnion Cert.negs,bound _ 2 (fun c h => (hvalid c h).1),?_,?_,?_,?_⟩
  · simpa using bound Cert.negs 1 (fun c h => (hvalid c h).2.1)
  · intro p hp; obtain ⟨c,h,hp⟩ := Finset.mem_biUnion.mp hp
    exact (hvalid c h).2.2.1 p hp
  · intro p hp; obtain ⟨c,h,hp⟩ := Finset.mem_biUnion.mp hp
    exact (hvalid c h).2.2.2 p hp
  · intro E' N' he hn H hm
    exact preserve keep (fun c h p hp => he p (Finset.mem_biUnion.mpr ⟨c,h,hp⟩))
      (fun c h p hp => hn p (Finset.mem_biUnion.mpr ⟨c,h,hp⟩)) hm

end PEqualNP.Outside.L_lib_1176.Work.Obstruction

namespace PEqualNP.Outside.L_lib_1176.Work

theorem restrictEmbedding {a b : Nat} (K : Finset (Hidden b)) (hu : UnsatCore K)
    (e : Fin a ↪ Fin b) (hs : ∀ D ∈ K, ∀ l ∈ D, ∃ j, e j = l.1) :
    ∃ H : Finset (Hidden a), UnsatCore H ∧ load H = load K ∧ triples H = triples K := by
  classical
  let f := e.prodMap (Function.Embedding.refl Bool)
  let g : Hidden a ↪ Hidden b := ⟨fun C => C.map f, Finset.map_injective f⟩
  let H := Finset.univ.filter (fun C => g C ∈ K)
  have memH (C) : C ∈ H ↔ g C ∈ K := by simp [H]
  have hK : H.map g = K := by
    ext D; constructor
    · intro hm; obtain ⟨C,hC,rfl⟩ := Finset.mem_map.mp hm; exact (memH C).1 hC
    · intro hD
      let C := Finset.univ.filter (fun l => f l ∈ D)
      have he : g C = D := by
        ext l; change l ∈ C.map f ↔ l ∈ D
        constructor
        · intro hl; obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hl; exact (Finset.mem_filter.mp hk).2
        · intro hl; obtain ⟨i,hi⟩ := hs D hD l hl
          have hf : f (i,l.2) = l := Prod.ext hi rfl
          exact Finset.mem_map.mpr ⟨_,Finset.mem_filter.mpr ⟨by simp, hf ▸ hl⟩,hf⟩
      exact Finset.mem_map.mpr ⟨C,(memH _).2 (he ▸ hD),he⟩
  have sat (C) (z : Fin b → Bool) : Holds (g C) z ↔ Holds C (z ∘ e) := by
    constructor
    · rintro ⟨k,hk,hz⟩; obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hk; exact ⟨l,hl,hz⟩
    · rintro ⟨l,hl,hz⟩; exact ⟨f l,Finset.mem_map_of_mem f hl,hz⟩
  have hc (C) : (g C).card = C.card := Finset.card_map ..
  refine ⟨H, ⟨?_,?_,?_⟩,?_,?_⟩
  · intro z
    let h := Function.extend e z (fun _ => false)
    have hz : h ∘ e = z := funext (e.injective.extend_apply z (fun _ => false))
    obtain ⟨D,hD,hn⟩ := hu.1 h
    rw [← hK] at hD; obtain ⟨C,hC,rfl⟩ := Finset.mem_map.mp hD
    exact ⟨C,hC,fun hs => hn ((sat C h).2 (hz ▸ hs))⟩
  · intro C hC; obtain ⟨h,hh⟩ := hu.2.1 _ ((memH _).1 hC)
    exact ⟨h ∘ e,fun D hD hn => (sat D h).1 (hh _ ((memH _).1 hD) (fun he => hn (g.injective he)))⟩
  · intro C hC; simpa [hc] using hu.2.2 _ ((memH _).1 hC)
  · rw [← hK]; simp [load,Finset.filter_map,hc]
  · rw [← hK]; simp [triples,Finset.filter_map,hc]

theorem restrictSupport {b : Nat} (K : Finset (Hidden b)) (hu : UnsatCore K)
    (V : Finset (Fin b)) (hs : ∀ D ∈ K, ∀ l ∈ D, l.1 ∈ V) :
    ∃ H : Finset (Hidden V.card), UnsatCore H ∧ load H = load K ∧ triples H = triples K := by
  apply restrictEmbedding K hu (V.orderEmbOfFin rfl).toEmbedding
  intro D hD l hl
  have h := hs D hD l hl
  change l.1 ∈ (V : Set (Fin b)) at h
  rw [← V.range_orderEmbOfFin rfl] at h; exact h

theorem eraseUnused {b : Nat} (K : Finset (Hidden (b+1))) (hu : UnsatCore K)
    (x : Fin (b+1)) (hx : ∀ D ∈ K, ∀ l ∈ D, l.1 ≠ x) :
    ∃ H : Finset (Hidden b), UnsatCore H ∧ load H = load K ∧ triples H = triples K := by
  apply restrictEmbedding K hu ⟨x.succAbove,x.succAbove_right_injective⟩
  exact fun D hD l hl => Fin.exists_succAbove_eq (hx D hD l hl)
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Work
namespace Zero
private def weight {b} (D : Hidden b) := if D.card = 1 then 2 else 1
private def cost {b} (T : Finset (Hidden b)) := ∑ E ∈ T, weight E
private def flipAt {b} (z : Fin b → Bool) (S : Finset (Fin b)) (v : Fin b) :=
  if v ∈ S then !(z v) else z v
private def Ext {b} (z h : Fin b → Bool) (S : Finset (Fin b)) := ∀ v ∈ S, h v = !(z v)

private lemma addCost {b} (D : Hidden b) (T : Finset (Hidden b)) :
    cost (insert D T) ≤ weight D + cost T := by
  classical
  by_cases h : D ∈ T
  · simp [Finset.insert_eq_of_mem h]
  · simp [cost, Finset.sum_insert h]

private lemma unionCost {b} (T U : Finset (Hidden b)) : cost (T ∪ U) ≤ cost T + cost U := by
  classical
  have e := Finset.sum_union_inter (s₁ := T) (s₂ := U) (f := weight)
  unfold cost; omega

private lemma blockers {b m} (K : Finset (Hidden b)) (hu : UnsatCore K)
    (hw : ∀ E ∈ K, E.card ≤ 2) (hm : ∀ E ∈ K, weight E ≤ m)
    (D : Hidden b) (z : Fin b → Bool) (hz : ∀ E ∈ K, E ≠ D → Holds E z)
    (a : Fin b) (ha : (a, !(z a)) ∈ D) (S : Finset (Fin b)) (has : a ∈ S) :
    ∃ T ⊆ K, cost T ≤ b - S.card + m ∧
      ∀ h, Ext z h S → ¬(∀ E ∈ T, Holds E h) := by
  classical
  let x := flipAt z S
  obtain ⟨E,hEK,hEx⟩ := hu.1 x
  have hED : E ≠ D := by rintro rfl; exact hEx ⟨_,ha,by simp [x,flipAt,has]⟩
  by_cases can : ∃ h, Ext z h S ∧ Holds E h
  · obtain ⟨h,hh,⟨l,hl,hv⟩⟩ := can
    have hn (k) (hk : k ∈ E) : x k.1 ≠ k.2 := fun eq => hEx ⟨k,hk,eq⟩
    have hls : l.1 ∉ S := by
      intro hs; exact hn l hl (by simpa [x,flipAt,hs,hh _ hs] using hv)
    have hlz : z l.1 ≠ l.2 := by simpa [x,flipAt,hls] using hn l hl
    obtain ⟨k,hk,hkz⟩ := hz E hEK hED
    have hks : k.1 ∈ S := by
      by_contra hs; exact hn k hk (by simpa [x,flipAt,hs] using hkz)
    have hkl : k ≠ l := by rintro rfl; exact hls hks
    have hpair : ({k,l} : Hidden b) = E := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hk (Finset.singleton_subset_iff.mpr hl)
      · simpa [hkl] using hw E hEK
    have hew : weight E = 1 := by simp [← hpair, weight,hkl]
    obtain ⟨T,hTK,ht,hblock⟩ := blockers K hu hw hm D z hz a ha (insert l.1 S) (Finset.mem_insert_of_mem has)
    refine ⟨insert E T,Finset.insert_subset hEK hTK,?_,?_⟩
    · have hcard := Finset.card_le_univ (insert l.1 S)
      simp [hls] at hcard ht
      have := addCost E T; omega
    · intro y hy hall
      apply hblock y ?_ (fun F hF => hall F (Finset.mem_insert_of_mem hF))
      intro v hv'; rcases Finset.mem_insert.mp hv' with rfl | hs
      · obtain ⟨r,hr,hyv⟩ := hall E (Finset.mem_insert_self ..)
        rw [← hpair] at hr
        simp only [Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · have hbad := hy _ hks; rw [hkz, hyv] at hbad; simp at hbad
        · cases e : z r.1 <;> cases e' : r.2 <;> simp_all
      · exact hy v hs
  · refine ⟨{E},by simpa using hEK,?_,?_⟩
    · have := hm E hEK; simp [cost]; omega
    · intro h hh hall; exact can ⟨h,hh,hall E (by simp)⟩
termination_by b - S.card
decreasing_by
  have hcard := Finset.card_le_univ (insert l.1 S)
  simp [hls] at hcard ⊢; omega

private lemma cover {b} {K T : Finset (Hidden b)} (hu : UnsatCore K) (hT : T ⊆ K)
    (hbad : ∀ h, ¬(∀ E ∈ T, Holds E h)) : T = K := by
  apply Finset.Subset.antisymm hT
  intro E hE; by_contra hET
  obtain ⟨h,hh⟩ := hu.2.1 E hE
  exact hbad h (fun F hF => hh F (hT hF) (by rintro rfl; contradiction))

private lemma seedBlock {b m} {K : Finset (Hidden b)} (hu : UnsatCore K)
    (hw : ∀ E ∈ K, E.card ≤ 2) (hm : ∀ E ∈ K, weight E ≤ m)
    {D : Hidden b} (hDK : D ∈ K) (l : Fin b × Bool) (hl : l ∈ D) :
    ∃ T ⊆ K, cost T ≤ b - 1 + m ∧ ∀ h, h l.1 = l.2 → ¬(∀ E ∈ T, Holds E h) := by
  classical
  obtain ⟨z,hz⟩ := hu.2.1 D hDK
  obtain ⟨E,hEK,hE⟩ := hu.1 z
  have hED : E = D := by by_contra hn; exact hE (hz E hEK hn)
  subst E
  have he : l.2 = !(z l.1) := by
    have hn : z l.1 ≠ l.2 := fun he => hE ⟨l,hl,he⟩
    cases e : z l.1 <;> cases e' : l.2 <;> simp_all
  have hflip : (l.1,!(z l.1)) ∈ D := by simpa only [← he, Prod.mk.eta] using hl
  obtain ⟨T,hTK,ht,hb⟩ := blockers K hu hw hm D z hz l.1 hflip {l.1} (by simp)
  refine ⟨T,hTK,by simpa using ht,?_⟩
  intro h hh; apply hb h; intro v hv; rw [Finset.mem_singleton.mp hv]; exact hh.trans he

end Zero
open PEqualNP.Outside.L_lib_1176.Work.Zero

theorem zeroTriplesLoad {b} {K : Finset (Hidden b)} (hb : 0 < b) (hu : UnsatCore K)
    (ht : triples K = 0) : load K ≤ 2*b+2 := by
  classical
  have hw (E) (hE : E ∈ K) : E.card ≤ 2 := by
    have := (hu.2.2 E hE).2
    have hn : E.card ≠ 3 := by
      intro h; have hm : E ∈ K.filter (fun D => D.card = 3) := Finset.mem_filter.mpr ⟨hE,h⟩
      change (K.filter fun D => D.card = 3).card = 0 at ht
      rw [Finset.card_eq_zero.mp ht] at hm; exact Finset.notMem_empty _ hm
    omega
  have hc : load K = cost K := by
    have hf : K.filter (fun D => D.card ≤ 2) = K := Finset.filter_eq_self.mpr hw
    unfold load cost; rw [hf, Finset.card_filter, Finset.card_eq_sum_ones K, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro E _; simp only [weight]; split <;> decide
  rw [hc]
  by_cases unit : ∃ D ∈ K, D.card = 1
  · obtain ⟨D,hDK,h1⟩ := unit
    obtain ⟨l,hs⟩ := Finset.card_eq_one.mp h1
    have hl : l ∈ D := by simp [hs]
    obtain ⟨T,hTK,ht,hbad⟩ := seedBlock hu hw (m := 2) (by intros; unfold weight; split <;> decide) hDK l hl
    have eq := cover hu (Finset.insert_subset hDK hTK) (by
      intro h hh; obtain ⟨r,hr,he⟩ := hh D (Finset.mem_insert_self ..)
      have hrl : r = l := by simpa [hs] using hr
      apply hbad h (hrl ▸ he)
      exact fun E hE => hh E (Finset.mem_insert_of_mem hE))
    have hd : weight D = 2 := by simp [weight,h1]
    have := addCost D T; rw [← eq]; omega
  · have htwo D (hD : D ∈ K) : D.card = 2 := by
      have := hw D hD; have := (hu.2.2 D hD).1
      have : D.card ≠ 1 := fun hn => unit ⟨D,hD,hn⟩; omega
    have hm E (hE : E ∈ K) : weight E ≤ 1 := by simp [weight,htwo E hE]
    obtain ⟨D,hDK,_⟩ := hu.1 (fun _ => false)
    obtain ⟨l,r,_,hd⟩ := Finset.card_eq_two.mp (htwo D hDK)
    obtain ⟨T,hTK,hT,bT⟩ := seedBlock hu hw hm hDK l (by simp [hd])
    obtain ⟨U,hUK,hU,bU⟩ := seedBlock hu hw hm hDK r (by simp [hd])
    have eq := cover hu (Finset.insert_subset hDK (Finset.union_subset hTK hUK)) (by
      intro h hh; obtain ⟨q,hq,he⟩ := hh D (Finset.mem_insert_self ..)
      simp only [hd,Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact bT h he (fun E hE => hh E (Finset.mem_insert_of_mem (Finset.mem_union_left _ hE)))
      · exact bU h he (fun E hE => hh E (Finset.mem_insert_of_mem (Finset.mem_union_right _ hE))))
    have := addCost D (T ∪ U); have := unionCost T U; have := hm D hDK
    rw [← eq]; omega
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176_aux
open PEqualNP.ProofComplexity
abbrev H (b : Nat) := Finset (Fin b × Bool)
abbrev SplitCl (n b : Nat) := Finset ((Fin n × Bool) × Bool) × H b
abbrev SumCl (n b : Nat) := Clause ((Fin n × Fin 2) ⊕ Fin b)
def Feas (s b n : Nat) := ∃ C : Finset (SplitCl n b),
  (∀ x : Fin n → Bool → Bool, (∃ i, x i false=true ∧ x i true=true) ↔
    ∃ h : Fin b → Bool, ∀ c ∈ C,
      (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ ∃ l ∈ c.2, h l.1=l.2) ∧
  (∀ c ∈ C, c.1.card+c.2.card ≤ 3) ∧ C.card ≤ 2*n+s
private def litE (n b : Nat) : (((Fin n × Fin 2) ⊕ Fin b) × Bool) ≃
    (((Fin n × Bool) × Bool) ⊕ (Fin b × Bool)) :=
  (Equiv.sumProdDistrib _ _ _).trans <| Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv).prodCongr (Equiv.refl _)) (Equiv.refl _)
private def splitE (n b : Nat) : SumCl n b ≃ SplitCl n b :=
  (litE n b).finsetCongr.trans Finset.sumEquiv.toEquiv
private lemma split_card {n b} (D : SumCl n b) :
    ((splitE n b D).1).card + ((splitE n b D).2).card = D.card := by
  change (D.map _).toLeft.card + (D.map _).toRight.card = _
  rw [Finset.card_toLeft_add_card_toRight, Finset.card_map]
private lemma split_sat {n b} (D : SumCl n b) (x : Fin n → Bool → Bool) (z : Fin b → Bool) :
    ClauseSat (Sum.elim (fun p => x p.1 (finTwoEquiv p.2)) z) D ↔
    (∃ l ∈ (splitE n b D).1, x l.1.1 l.1.2 = l.2) ∨ ∃ l ∈ (splitE n b D).2, z l.1=l.2 := by
  change _ ↔ (∃ l ∈ (D.map (litE n b).toEmbedding).toLeft, _) ∨ ∃ l ∈ (D.map (litE n b).toEmbedding).toRight, _
  simp only [ClauseSat, Finset.mem_toLeft, Finset.mem_toRight, Finset.mem_map,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨⟨p|p,v⟩,hm,hs⟩
    · exact Or.inl ⟨((p.1,finTwoEquiv p.2),v), ⟨_,hm,rfl⟩, hs⟩
    · exact Or.inr ⟨(p,v), ⟨_,hm,rfl⟩, hs⟩
  · rintro (⟨l,⟨⟨p|p,v⟩,hm,he⟩,hs⟩ | ⟨l,⟨⟨p|p,v⟩,hm,he⟩,hs⟩)
    · change Sum.inl ((p.1,finTwoEquiv p.2),v) = Sum.inl l at he
      cases Sum.inl.inj he; exact ⟨_, hm, hs⟩
    · contradiction
    · contradiction
    · change Sum.inr (p,v) = Sum.inr l at he
      cases Sum.inr.inj he; exact ⟨_, hm, hs⟩
private def Cons {b} (U : Finset (H b)) := ∃ z : Fin b → Bool, Satisfies z (↑U : Set _)
private def Loaded (s b n : Nat) := ∃ (U : Finset (H b)) (g : H b → Nat),
  ¬ Cons U ∧ (∀ D ∈ U, Cons (U.erase D)) ∧ (∑ D ∈ U, g D) = n ∧
  (∀ D ∈ U, D.card + g D ≤ 3) ∧ (∑ D ∈ U, 2^(g D)) ≤ 2*n+s
private lemma equiv_loaded {s b n : Nat} (hn : 0<n) : Feas s b n ↔ Loaded s b n := by
  classical
  have T := PEqualNP.Outside.L_lib_1176.Pcx277 2 n b 3 (2*n+s) (by decide) hn (fun _ => 1) (fun _ _ _ => le_rfl)
  dsimp only at T
  simp only [Nat.mul_one] at T
  apply Iff.trans _ T
  let e := splitE n b
  have pair (x : Fin n → Bool → Bool) (j : Fin n) :
      (∀ i : Fin 2, x j (finTwoEquiv i) = true) ↔ x j false = true ∧ x j true = true := by
    constructor
    · exact fun h => ⟨by simpa using h (finTwoEquiv.symm false), by simpa using h (finTwoEquiv.symm true)⟩
    · intro h i; cases h' : finTwoEquiv i <;> simp [h.1,h.2]
  have enc (F : Finset (SumCl n b)) (x : Fin n → Bool → Bool) (z : Fin b → Bool) :
      Satisfies (Sum.elim (fun p : Fin n × Fin 2 => x p.1 (finTwoEquiv p.2)) z) (↑F : Set _) ↔
      ∀ c ∈ F.map e.toEmbedding, (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ ∃ l ∈ c.2, z l.1=l.2 := by
    simp only [Satisfies, Finset.mem_coe, Finset.forall_mem_map]; exact forall_congr' fun D => imp_congr_right fun _ => split_sat _ _ _
  constructor
  · rintro ⟨C,hx,hw,hc⟩
    let F := C.map e.symm.toEmbedding
    have he : F.map e.toEmbedding = C := by ext c; simp [F]
    refine ⟨F, ?_, ?_, by simpa [F] using hc⟩
    · intro y
      let x := fun (j : Fin n) (i : Bool) => y (j,finTwoEquiv.symm i)
      have hy : (fun p : Fin n × Fin 2 => x p.1 (finTwoEquiv p.2)) = y := by funext p; simp [x]
      have h := hx x
      rw [← he] at h
      rw [← hy]
      simpa only [pair x, enc F x] using h
    · intro D hD; rw [← split_card D]; apply hw; rw [← he]; exact Finset.mem_map_of_mem _ hD
  · rintro ⟨F,hx,hw,hc⟩
    refine ⟨F.map e.toEmbedding, ?_, ?_, by simpa using hc⟩
    · intro x; simpa only [pair, enc] using hx (fun p => x p.1 (finTwoEquiv p.2))
    · intro c hc; obtain ⟨D,hD,rfl⟩ := Finset.mem_map.mp hc; exact (split_card D).le.trans (hw D hD)

def Core (s b n : Nat) := ∃ K : Finset (H b),
  (∀ h : Fin b → Bool, ∃ D ∈ K, ¬ ClauseSat h D) ∧
  (∀ D ∈ K, ∃ h : Fin b → Bool, ∀ E ∈ K, E ≠ D → ClauseSat h E) ∧
  (∀ D ∈ K, 1 ≤ D.card ∧ D.card ≤ 3) ∧
  n ≤ (K.filter (fun D => D.card ≤ 2)).card + (K.filter (fun D => D.card=1)).card ∧
  (K.filter (fun D => D.card=3)).card ≤ s ∧ K.card ≤ n+s
private lemma not_cons {b} (U : Finset (H b)) : ¬ Cons U ↔ ∀ z : Fin b → Bool, ∃ D ∈ U, ¬ ClauseSat z D := by
  classical
  simp [Cons,Satisfies]
private lemma cons_erase {b} (U : Finset (H b)) (D : H b) : Cons (U.erase D) ↔ ∃ z : Fin b → Bool, ∀ E ∈ U, E ≠ D → ClauseSat z E := by
  classical
  simp only [Cons,Satisfies,Finset.mem_coe, Finset.mem_erase]; aesop

lemma widthThreeCore {s b n : Nat} (hn : 4 ≤ n) : Feas s b n ↔ Core s b n := by
  classical
  rw [equiv_loaded (by omega)]
  constructor
  · rintro ⟨K,g,hu,hm,hs,hw,hp⟩
    have hne (D) (hD : D ∈ K) : 1 ≤ D.card := by
      by_contra! hz
      have he : D = ∅ := Finset.card_eq_zero.mp (by omega)
      have hsing : K = {D} := by
        ext E; simp only [Finset.mem_singleton]; constructor
        · intro hE; by_contra hED
          obtain ⟨z,hz⟩ := hm E hE
          obtain ⟨l,hl,_⟩ := hz D (Finset.mem_erase.mpr ⟨Ne.symm hED,hD⟩)
          simpa [he] using hl
        · rintro rfl; exact hD
      have := hw D hD; simp [hsing] at hs; omega
    have small D (hD : D ∈ K) : g D ≤ 2 := by have := hne D hD; have := hw D hD; omega
    refine ⟨K,(not_cons K).1 hu, fun D hD => (cons_erase K D).1 (hm D hD), fun D hD => ⟨hne D hD, by have := hw D hD; omega⟩, ?_, ?_, ?_⟩
    · rw [← hs, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro D hD; have := hw D hD; have := hne D hD; split_ifs <;> omega
    · have hh : (∑ D ∈ K, (2*g D + (if D.card = 3 then 1 else 0))) ≤ ∑ D ∈ K, 2^g D := by
        apply Finset.sum_le_sum; intro D hD; have := small D hD; have := hw D hD
        interval_cases h : g D <;> split_ifs <;> omega
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs, ← Finset.card_filter] at hh; omega
    · have hh : (∑ D ∈ K, (g D + 1)) ≤ ∑ D ∈ K, 2^g D := by
        apply Finset.sum_le_sum; intro D hD; have := small D hD; interval_cases g D <;> decide
      simp [Finset.sum_add_distrib, hs] at hh; omega
  · rintro ⟨K,hu,hm,hw,hcap,ht,hsize⟩
    let V := K.filter (fun D => D.card ≤ 2)
    let U := K.filter (fun D => D.card = 1)
    let a := min n V.card
    obtain ⟨A,hAV,hA⟩ := Finset.exists_subset_card_eq (s := V) (min_le_right n V.card)
    obtain ⟨B,hBU,hB⟩ := Finset.exists_subset_card_eq (s := U) (show n-a ≤ U.card by dsimp [a,U,V]; omega)
    let g := fun D : H b => (if D ∈ A then 1 else 0) + (if D ∈ B then 1 else 0)
    have hAK := hAV.trans (Finset.filter_subset _ _)
    have hBK := hBU.trans (Finset.filter_subset _ _)
    have ci (T : Finset (H b)) (ht : T ⊆ K) : (∑ D ∈ K, (if D ∈ T then 1 else 0 : Nat)) = T.card := by
      exact (Finset.card_eq_sum_ite ht).symm
    have hg : (∑ D ∈ K, g D) = n := by
      simp only [g,Finset.sum_add_distrib,ci A hAK,ci B hBK,hA,hB]; dsimp [a]; omega
    refine ⟨K,g,(not_cons K).2 hu, fun D hD => (cons_erase K D).2 (hm D hD), hg, ?_, ?_⟩
    · intro D hD; have h := hw D hD
      have hv (hh : D ∈ A) := (Finset.mem_filter.mp (hAV hh)).2
      have hu' (hh : D ∈ B) := (Finset.mem_filter.mp (hBU hh)).2
      simp only [g]; split_ifs <;> grind
    · have hcost : (∑ D ∈ K, 2^g D) ≤ ∑ D ∈ K, (2*g D + (if D ∉ A then 1 else 0)) := by
        apply Finset.sum_le_sum; intro D hD; simp only [g]; split_ifs <;> decide
      have hcompl : K.filter (fun D => D ∉ A) = K \ A := by ext; simp
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hg, Finset.sum_boole, hcompl, Finset.card_sdiff_of_subset hAK, hA] at hcost
      have he : K.card = V.card + (K.filter fun D => D.card = 3).card := by
        have he' : K.filter (fun D => ¬D.card ≤ 2) = K.filter (fun D => D.card = 3) := by
          ext D; simp only [Finset.mem_filter]; constructor <;> rintro ⟨hD,h⟩ <;> exact ⟨hD,by have := hw D hD; omega⟩
        have := Finset.card_filter_add_card_filter_not (s := K) (p := fun D => D.card ≤ 2)
        rw [he'] at this; exact this.symm
      dsimp [a] at hcost; omega

theorem coreIff : PEqualNP.Outside.L_lib_1176.Work.CoreIff := by
  intro s b n hn
  exact (widthThreeCore (s := s) (b := b) hn).trans <| by
    unfold Core PEqualNP.Outside.L_lib_1176.Work.UnsatCore PEqualNP.Outside.L_lib_1176.Work.load PEqualNP.Outside.L_lib_1176.Work.triples
    simp only [and_assoc, ClauseSat, PEqualNP.Outside.L_lib_1176.Work.Holds]
end PEqualNP.Outside.L_lib_1176_aux

namespace PEqualNP.Outside.L_lib_1176.Work
def Arr {b} (K : Finset (Hidden b)) (u v : Fin b) := {(u,false),(v,true)} ∈ K
def Ban {b} (K : Finset (Hidden b)) (u v : Fin b) := {(u,false),(v,false)} ∈ K
def Marked {b} (K : Finset (Hidden b)) := (K.filter (fun D => D.card=3)).biUnion (fun D => D.image Prod.fst)
theorem memMarked {b} {K : Finset (Hidden b)} {v : Fin b} : v∈Marked K ↔ ∃ D∈K, D.card=3 ∧ ∃ s, (v,s)∈D := by
  classical
  simp only [Marked,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨D,⟨hd,hc⟩,⟨⟨w,s⟩,hs,rfl⟩⟩; exact ⟨D,hd,hc,s,hs⟩
  · rintro ⟨D,hd,hc,s,hs⟩; exact ⟨D,⟨hd,hc⟩,⟨(v,s),hs,rfl⟩⟩
theorem marked_bound {b} (K : Finset (Hidden b)) : (Marked K).card ≤ 3*triples K := by
  classical
  let T := K.filter (fun D => D.card=3)
  calc (Marked K).card ≤ ∑ D ∈ T, (D.image Prod.fst).card := Finset.card_biUnion_le
       _ ≤ ∑ _D ∈ T, 3 := by
         apply Finset.sum_le_sum; intro D hd; exact Finset.card_image_le.trans (Finset.mem_filter.mp hd).2.le
       _ = 3*triples K := by simp [T,triples,Nat.mul_comm]
private theorem nontaut {b} {K : Finset (Hidden b)} (hu : UnsatCore K) {D : Hidden b} (hd : D∈K) {v : Fin b} (hf : (v,false)∈D) (ht : (v,true)∈D) : False := by
  obtain ⟨h,hw⟩ := hu.2.1 D hd; obtain ⟨W,hW,hn⟩ := hu.1 h
  by_cases eq : W=D
  · subst W; apply hn; cases e : h v <;> first | exact ⟨_,hf,e⟩ | exact ⟨_,ht,e⟩
  · exact hn (hw W hW eq)
theorem arr_ne {b} {K : Finset (Hidden b)} (hu : UnsatCore K) {u v} (ha : Arr K u v) : u≠v := by
  rintro rfl; exact nontaut (v:=u) hu ha (by simp) (by simp)
theorem positive_small {b} {K : Finset (Hidden b)} (ho : Oriented K) {D : Hidden b} (hd : D∈K) (h2 : D.card≤2) {x : Fin b} (hp : (x,true)∈D) :
    ∃ y, Arr K y x ∧ D={(y,false),(x,true)} := by
  obtain ⟨y,hy⟩ := ho _ hd h2
  let A : Hidden b := {(y,false),(x,true)}
  have hs : A ⊆ D := by
    intro l hl; rcases (Finset.mem_insert.mp hl) with rfl | h
    · exact hy
    · simpa only [Finset.mem_singleton.mp h] using hp
  have hc : A.card=2 := by simp [A]
  have he : A=D := Finset.eq_of_subset_of_card_le hs (by omega)
  exact ⟨y,show A∈K from he.symm ▸ hd,he.symm⟩
theorem unmarked_positive {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (ho : Oriented K) {x : Fin b} (hm : x∉Marked K) {D : Hidden b} (hd : D∈K) (hp : (x,true)∈D) :
    ∃ y, Arr K y x ∧ D={(y,false),(x,true)} := by
  have h3 := (hu.2.2 D hd).2
  have hn : D.card≠3 := fun e => hm (memMarked.mpr ⟨D,hd,e,true,hp⟩)
  exact positive_small ho hd (by omega) hp
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Work
theorem holds_arr_iff {b} {u v : Fin b} {h : Fin b → Bool} : Holds {(u,false),(v,true)} h ↔ (h u=true → h v=true) := by
  simp only [Holds,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨l,rfl|rfl,hh⟩ <;> simp_all
  · intro hf; cases hu : h u with
    | true => exact ⟨(v,true),Or.inr rfl,hf hu⟩
    | false => exact ⟨(u,false),Or.inl rfl,hu⟩
theorem holds_ban_iff {b} {u v : Fin b} {h : Fin b → Bool} : Holds {(u,false),(v,false)} h ↔ ¬(h u=true ∧ h v=true) := by
  simp only [Holds,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨l,rfl|rfl,hh⟩ <;> simp_all
  · intro hn; cases hu : h u with
    | false => exact ⟨(u,false),Or.inl rfl,hu⟩
    | true => cases hv : h v with
      | false => exact ⟨(v,false),Or.inr rfl,hv⟩
      | true => exact (hn ⟨hu,hv⟩).elim
theorem arr_clause_inj {b} {u v a z : Fin b}
    (he : ({(u,false),(v,true)} : Hidden b)={(a,false),(z,true)}) : u=a ∧ v=z := by
  have hh : (u,false) ∈ ({(a,false),(z,true)} : Hidden b) := he ▸ (by simp : (u,false)∈({(u,false),(v,true)} : Hidden b))
  have pp : (v,true) ∈ ({(a,false),(z,true)} : Hidden b) := he ▸ (by simp : (v,true)∈({(u,false),(v,true)} : Hidden b))
  exact ⟨by simpa using hh,by simpa using pp⟩
theorem arr_ne_ban {b} (u v a z : Fin b) : ({(u,false),(v,true)} : Hidden b)≠{(a,false),(z,false)} := by
  intro he; have h : (v,true) ∈ ({(a,false),(z,false)} : Hidden b) := he ▸ (by simp : (v,true)∈({(u,false),(v,true)} : Hidden b)); simpa using h
theorem smallShape {b} {K : Finset (Hidden b)} (ho : Oriented K) {D : Hidden b} (hd : D∈K) (h2 : D.card≤2) :
    (∃ u v, D={(u,false),(v,true)}) ∨ ∃ u v, D={(u,false),(v,false)} := by
  classical
  by_cases hp : ∃ v, (v,true)∈D
  · obtain ⟨v,hv⟩ := hp; obtain ⟨u,_,hx⟩ := positive_small ho hd h2 hv; exact Or.inl ⟨_,_,hx⟩
  · right
    obtain ⟨u,hu⟩ := ho _ hd h2
    by_cases hother : ∃ z, (z,false)∈D ∧ z≠u
    · obtain ⟨z,hz,hne⟩ := hother
      let A : Hidden b := {(u,false),(z,false)}
      have hs : A ⊆ D := by intro l hl; rcases Finset.mem_insert.mp hl with rfl|h; exact hu; simpa only [Finset.mem_singleton.mp h] using hz
      have hsize : A.card=2 := by simp [A,Ne.symm hne]
      exact ⟨u,z,(Finset.eq_of_subset_of_card_le hs (by omega)).symm⟩
    · refine ⟨u,u,?_⟩
      ext l; obtain ⟨z,s⟩ := l; cases s with
      | true => simp [show (z,true) ∉D from fun hz => hp ⟨_,hz⟩]
      | false =>
        simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.mem_singleton,Prod.mk.injEq,and_true]
        constructor
        · intro hm; exact Classical.byContradiction (fun hn => hother ⟨z,hm,hn⟩)
        · rintro rfl; exact hu
theorem graph_holds_all {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (ho : Oriented K) (h w : Fin b → Bool)
    (ha : ∀ u v, Arr K u v → h u=true → h v=true) (hn : ∀ u v, Ban K u v → ¬(h u=true ∧ h v=true))
    (hm : ∀ v∈Marked K, h v = w v) (ht : ∀ D∈K, D.card=3 → Holds D w) : ∀ D∈K, Holds D h := by
  intro D hd
  by_cases h3 : D.card=3
  · obtain ⟨⟨v,s⟩,hv,he⟩ := ht D hd h3
    refine ⟨(v,s),hv,?_⟩; change h v=s; rw [hm v (memMarked.mpr ⟨D,hd,h3,s,hv⟩)]; exact he
  · have hmax := (hu.2.2 D hd).2
    obtain ⟨u,v,rfl⟩|⟨u,v,rfl⟩ := smallShape ho hd (by omega)
    · exact holds_arr_iff.mpr (ha u v hd)
    · exact holds_ban_iff.mpr (hn u v hd)
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Compression

def Enters (path : Finset Nat) (u v : Nat) : Prop :=
  u ∈ path ∧ v ∈ path ∧ u < v ∧ ∀ w ∈ path, u < w → w < v → False

def Coherent {k : Nat} (paths : Fin k → Finset Nat) : Prop :=
  ∀ i j a b, a ∈ paths i → a ∈ paths j → b ∈ paths i → b ∈ paths j →
    ∀ w, a ≤ w → w ≤ b → (w ∈ paths i ↔ w ∈ paths j)

private theorem first_common {k} {paths : Fin k → Finset Nat} (hc : Coherent paths)
    {i j u z v} (hi : Enters (paths i) u v) (hj : Enters (paths j) z v)
    (hne : u ≠ z) {a} (hai : a ∈ paths i) (haj : a ∈ paths j) : v ≤ a := by
  obtain ⟨hui, hvi, huv, hgapI⟩ := hi
  obtain ⟨hzj, hvj, hzv, hgapJ⟩ := hj
  by_contra! hav
  have hau : a ≤ u := le_of_not_gt (fun h => hgapI a hai h hav)
  have haz : a ≤ z := le_of_not_gt (fun h => hgapJ a haj h hav)
  rcases lt_or_gt_of_ne hne with huz | hzu
  · exact hgapI z ((hc i j a v hai haj hvi hvj z haz hzv.le).mpr hzj) huz hzv
  · exact hgapJ u ((hc i j a v hai haj hvi hvj u hau huv.le).mp hui) hzu huv

theorem branch_card_le {k : Nat} (paths : Fin k → Finset Nat) (hc : Coherent paths)
    (branch : Finset Nat)
    (cover : ∀ v ∈ branch, ∃ i j u z, Enters (paths i) u v ∧
      Enters (paths j) z v ∧ u ≠ z) : branch.card ≤ k.choose 2 := by
  classical
  let first : Finset (Fin k) → Nat := fun T =>
    if h : ∃ v : Nat, ∀ i ∈ T, v ∈ paths i then Nat.find h else 0
  have hsub : branch ⊆ (Finset.univ.powersetCard 2).image first := by
    intro v hv
    obtain ⟨i, j, u, z, hi, hj, hn⟩ := cover v hv
    have hij : i ≠ j := by
      intro he; subst j
      rcases lt_or_gt_of_ne hn with hz | hu
      · exact hi.2.2.2 z hj.1 hz hj.2.2.1
      · exact hj.2.2.2 u hi.1 hu hi.2.2.1
    let T : Finset (Fin k) := {i,j}
    have hvT : ∀ a ∈ T, v ∈ paths a := by
      intro a ha
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hi.2.1
      · exact hj.2.1
    have hex : ∃ w, ∀ a ∈ T, w ∈ paths a := ⟨v, hvT⟩
    refine Finset.mem_image.mpr ⟨T, ?_, ?_⟩
    · simp [Finset.mem_powersetCard, T, hij]
    · change (if h : ∃ w, ∀ a ∈ T, w ∈ paths a then Nat.find h else 0) = v
      rw [dite_eq_left hex]
      apply le_antisymm (Nat.find_min' hex hvT)
      exact first_common hc hi hj hn (Nat.find_spec hex i (by simp [T]))
        (Nat.find_spec hex j (by simp [T]))
  calc branch.card ≤ _ := Finset.card_le_card hsub
       _ ≤ _ := Finset.card_image_le
       _ = _ := by simp

def IsPath (R : Nat → Nat → Prop) (x y : Nat) (P : Finset Nat) :=
  x ∈ P ∧ y ∈ P ∧ (∀ v ∈ P, x ≤ v ∧ v ≤ y) ∧ ∀ u v, Enters P u v → R u v

private def inside (P : Finset Nat) (a b : Nat) := P.filter fun v => a ≤ v ∧ v ≤ b
private def outside (P : Finset Nat) (a b : Nat) := P.filter fun v => ¬(a ≤ v ∧ v ≤ b)
private def splice (P Q : Finset Nat) (a b : Nat) := outside P a b ∪ inside Q a b

private theorem splice_path {R x y z t P Q a b} (hP : IsPath R x y P)
    (hQ : IsPath R z t Q) (ha : a ∈ P) (ha' : a ∈ Q) (hb : b ∈ P) (hb' : b ∈ Q)
    (hab : a ≤ b) : IsPath R x y (splice P Q a b) := by
  let S := splice P Q a b
  have mem (v) : v ∈ S ↔ (v ∈ P ∧ ¬(a ≤ v ∧ v ≤ b)) ∨ (v ∈ Q ∧ a ≤ v ∧ v ≤ b) := by
    simp [S,splice,inside,outside]
  have left (v) (h : v ≤ a) : v ∈ S ↔ v ∈ P := by
    rw [mem]
    by_cases he : v = a
    · subst v; simp [ha,ha',hab]
    · have hh : ¬ a ≤ v := by omega
      simp [hh]
  have right (v) (h : b ≤ v) : v ∈ S ↔ v ∈ P := by
    rw [mem]
    by_cases he : v = b
    · subst v; simp [hb,hb',hab]
    · have hh : ¬ v ≤ b := by omega
      simp [hh]
  have mid (v) (hav : a ≤ v) (hvb : v ≤ b) : v ∈ S ↔ v ∈ Q := by simp [mem,hav,hvb]
  have aux {A : Finset Nat} {u v} (hc : Enters S u v)
      (heq : ∀ w, u ≤ w → w ≤ v → (w ∈ S ↔ w ∈ A)) : Enters A u v :=
    ⟨(heq u le_rfl hc.2.2.1.le).mp hc.1, (heq v hc.2.2.1.le le_rfl).mp hc.2.1,
     hc.2.2.1, fun w hw huw hwv => hc.2.2.2 w ((heq w huw.le hwv.le).mpr hw) huw hwv⟩
  have hxa := (hP.2.2.1 a ha).1
  have hby := (hP.2.2.1 b hb).2
  refine ⟨(left x hxa).mpr hP.1, (right y hby).mpr hP.2.1, ?_, ?_⟩
  · intro v hv
    rcases (mem v).mp hv with ⟨hv,_⟩ | ⟨_,hl,hr⟩
    · exact hP.2.2.1 v hv
    · omega
  · intro u v huv
    by_cases hL : v ≤ a
    · exact hP.2.2.2 u v (aux huv (fun w _ hw => left w (hw.trans hL)))
    by_cases hR : b ≤ u
    · exact hP.2.2.2 u v (aux huv (fun w hw _ => right w (hR.trans hw)))
    have hau : a ≤ u := by
      by_contra! hua
      exact huv.2.2.2 a ((left a le_rfl).mpr ha) hua (by omega)
    have hvb : v ≤ b := by
      by_contra! hbv
      exact huv.2.2.2 b ((right b le_rfl).mpr hb) (by omega) hbv
    exact hQ.2.2.2 u v (aux huv (fun w hu hv => mid w (hau.trans hu) (hv.trans hvb)))

private def price (P : Finset Nat) : Nat := ∑ v ∈ P, 2^v

private theorem splice_price (P Q : Finset Nat) (a b : Nat) :
    price (splice P Q a b) = price (outside P a b) + price (inside Q a b) := by
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2

private theorem price_split (P : Finset Nat) (a b : Nat) :
    price P = price (outside P a b) + price (inside P a b) := by
  convert splice_price P P a b using 2
  ext v
  simp only [splice,outside,inside,Finset.mem_union,Finset.mem_filter]
  tauto

theorem choose_coherent {k : Nat} (R : Nat → Nat → Prop) (x y : Fin k → Nat)
    (hex : ∀ i, ∃ P, IsPath R (x i) (y i) P) :
    ∃ P : Fin k → Finset Nat, (∀ i, IsPath R (x i) (y i) (P i)) ∧ Coherent P := by
  classical
  have ex (i) : ∃ n, ∃ P, IsPath R (x i) (y i) P ∧ price P = n := by
    obtain ⟨T,hT⟩ := hex i
    exact ⟨_,T,hT,rfl⟩
  let P (i) := (Nat.find_spec (ex i)).choose
  have prop (i) : IsPath R (x i) (y i) (P i) ∧ price (P i) = Nat.find (ex i) :=
    (Nat.find_spec (ex i)).choose_spec
  have opt (i T) (h : IsPath R (x i) (y i) T) : price (P i) ≤ price T :=
    (prop i).2 ▸ Nat.find_min' (ex i) ⟨T,h,rfl⟩
  refine ⟨P,fun i => (prop i).1,?_⟩
  intro i j a b hai haj hbi hbj w haw hwb
  have hab := haw.trans hwb
  have le1 := opt i _ (splice_path (prop i).1 (prop j).1 hai haj hbi hbj hab)
  have le2 := opt j _ (splice_path (prop j).1 (prop i).1 haj hai hbj hbi hab)
  rw [splice_price,price_split (P i) a b] at le1
  rw [splice_price,price_split (P j) a b] at le2
  have eq : inside (P i) a b = inside (P j) a b := by
    apply Finset.geomSum_injective (n := 2) le_rfl
    change price _ = price _
    omega
  have hw := Finset.ext_iff.mp eq w
  simpa [inside,haw,hwb] using hw

inductive Rule (V : Type*) where
  | imp (u v : V)
  | neg (xs : Finset V)
  | protectedClause (pos neg : Finset V)

def Rule.Holds {V} (H : V → Prop) : Rule V → Prop
  | .imp u v => H u → H v
  | .neg xs => ∃ v ∈ xs, ¬ H v
  | .protectedClause pos bad => (∃ v ∈ pos, H v) ∨ ∃ v ∈ bad, ¬ H v

def Rule.Anchored {V} (fixVertex : V → Prop) : Rule V → Prop
  | .imp _ v => fixVertex v
  | .neg _ => True
  | .protectedClause pos bad => (∀ v ∈ pos, fixVertex v) ∧ (∀ v ∈ bad, fixVertex v)

private theorem Rule.decrease {V W} {proj : V → W} {incl : W → V} {H : V → Prop}
    (hdown : ∀ v, H (incl (proj v)) → H v) (R : Rule V)
    (ha : R.Anchored (fun v => incl (proj v) = v))
    (hh : R.Holds H) : R.Holds (fun v => H (incl (proj v))) := by
  cases R with
  | imp u v =>
    change incl (proj v) = v at ha
    intro hu
    rw [ha]
    exact hh (hdown u hu)
  | neg xs =>
    obtain ⟨v,hv,hn⟩ := hh
    exact ⟨v,hv,fun h => hn (hdown v h)⟩
  | protectedClause pos neg =>
    rcases hh with ⟨v,hv,hn⟩ | ⟨v,hv,hn⟩
    · exact Or.inl ⟨v,hv,by simpa only [ha.1 v hv] using hn⟩
    · exact Or.inr ⟨v,hv,by simpa only [ha.2 v hv] using hn⟩

theorem suppress {V W E K : Type*} (proj : V → W) (incl : W → V)
    (edges : E → V × V) (rules : K → Rule V)
    (hinternal : ∀ e, proj (edges e).1 = proj (edges e).2)
    (hpath : ∀ v, Relation.ReflTransGen (fun a b => ∃ e, edges e = (a,b))
      (incl (proj v)) v)
    (hanchor : ∀ k, (rules k).Anchored (fun v => incl (proj v) = v))
    (hbad : ¬ ∃ H : V → Prop, (∀ e, H (edges e).1 → H (edges e).2) ∧
      ∀ k, (rules k).Holds H)
    (hdrop : ∀ k, ∃ H : V → Prop, (∀ e, H (edges e).1 → H (edges e).2) ∧
      ∀ j, j ≠ k → (rules j).Holds H) :
    (¬ ∃ h : W → Prop, ∀ k, (rules k).Holds (h ∘ proj)) ∧
    (∀ k, ∃ h : W → Prop, ∀ j, j ≠ k → (rules j).Holds (h ∘ proj)) := by
  constructor
  · rintro ⟨h, hh⟩
    exact hbad ⟨h ∘ proj, fun e => by simp [hinternal e], hh⟩
  · intro k
    obtain ⟨H, he, hk⟩ := hdrop k
    refine ⟨H ∘ incl, fun j hj => Rule.decrease ?_ _ (hanchor j) (hk j hj)⟩
    have forward {a b} (hp : Relation.ReflTransGen (fun x y => ∃ e, edges e = (x,y)) a b) :
        H a → H b := by
      induction hp with
      | refl => exact id
      | tail _ hedge ih =>
        obtain ⟨e, hab⟩ := hedge
        have h := he e
        rw [hab] at h
        exact fun hx => h (ih hx)
    exact fun v => forward (hpath v)

theorem contract_scc {V W E K : Type*} (proj : V → W) (incl : W → V)
    (edges : E → V × V) (holds : K → (V → Prop) → Prop)
    (hinternal : ∀ e, proj (edges e).1 = proj (edges e).2)
    (hreach : ∀ v,
       Relation.ReflTransGen (fun x y => ∃ e, edges e = (x,y)) (incl (proj v)) v ∧
       Relation.ReflTransGen (fun x y => ∃ e, edges e = (x,y)) v (incl (proj v)))
    (hbad : ¬ ∃ H : V → Prop, (∀ e, H (edges e).1 → H (edges e).2) ∧ ∀ k, holds k H)
    (hdrop : ∀ k, ∃ H : V → Prop, (∀ e, H (edges e).1 → H (edges e).2) ∧
      ∀ j, j ≠ k → holds j H) :
    (¬ ∃ h : W → Prop, ∀ k, holds k (h ∘ proj)) ∧
    (∀ k, ∃ h : W → Prop, ∀ j, j ≠ k → holds j (h ∘ proj)) := by
  constructor
  · rintro ⟨h, hh⟩
    exact hbad ⟨h ∘ proj, fun e => by simp [hinternal e], hh⟩
  · intro k
    obtain ⟨H, he, hk⟩ := hdrop k
    have forward {a b} (hp : Relation.ReflTransGen (fun x y => ∃ e, edges e = (x,y)) a b) :
        H a → H b := by
      induction hp with
      | refl => exact id
      | tail _ h ih =>
        obtain ⟨e,hab⟩ := h
        have hh := he e
        rw [hab] at hh
        exact fun h => hh (ih h)
    have eqv : (H ∘ incl) ∘ proj = H := by
      funext v
      exact propext ⟨forward (hreach v).1, forward (hreach v).2⟩
    exact ⟨H ∘ incl, fun j hj => by rw [eqv]; exact hk j hj⟩

abbrev Reach {V : Type*} (E : Finset (V × V)) : V → V → Prop :=
  Relation.ReflTransGen (fun a b => (a,b) ∈ E)

private def Steps {V : Type*} (R : V → V → Prop) (a : V) : Nat → V → Prop
  | 0, b => a = b
  | n+1, b => ∃ v, Steps R a n v ∧ R v b

private theorem has_steps {V : Type*} {R : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen R a b) : ∃ n, Steps R a n b := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | tail _ h ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n+1,_,hn,h⟩

theorem thin_out {V : Type*} [Fintype V] (E : Finset (V × V)) (r : V)
    (hreach : ∀ v, Reach E r v) :
    ∃ T ⊆ E, T.card ≤ Fintype.card V - 1 ∧ ∀ v, Reach T r v := by
  classical
  let R : V → V → Prop := fun u v => (u,v) ∈ E
  have ex (v : V) : ∃ n, Steps R r n v := has_steps (hreach v)
  let d (v : V) := Nat.find (ex v)
  have pick (v : V) (hv : v ≠ r) : ∃ u, R u v ∧ d u < d v := by
    have hh : Steps R r (d v) v := Nat.find_spec (ex v)
    cases en : d v with
    | zero => rw [en] at hh; exact (hv (Eq.symm hh)).elim
    | succ n =>
      rw [en] at hh
      obtain ⟨u,hu,huv⟩ := hh
      have hle := Nat.find_min' (ex u) hu
      exact ⟨u,huv,Nat.lt_succ_of_le hle⟩
  let parent (v : V) := if h : v ≠ r then (pick v h).choose else r
  have hp (v) (hv : v ≠ r) : R (parent v) v ∧ d (parent v) < d v := by
    simpa only [parent,dite_eq_left hv] using (pick v hv).choose_spec
  let T := (Finset.univ.erase r).image (fun v => (parent v,v))
  have member (v) (hv : v ≠ r) : (parent v,v) ∈ T :=
    Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hv,Finset.mem_univ _⟩)
  refine ⟨T,?_,?_,?_⟩
  · intro e he
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
    exact (hp _ (Finset.mem_erase.mp hv).1).1
  · exact Finset.card_image_le.trans (by simp [Finset.card_erase_of_mem])
  · have aux (n : Nat) : ∀ v, d v = n → Reach T r v := by
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro v hv
        by_cases hroot : v = r
        · subst v; exact .refl
        · exact (ih (d (parent v)) (hv ▸ (hp v hroot).2) _ rfl).tail (member v hroot)
    exact fun v => aux _ v rfl

private theorem lift_reach {V W : Type*} {E : Finset (V × V)} {F : Finset (W × W)}
    (f : V → W) (hm : ∀ u v, (u,v) ∈ E → (f u,f v) ∈ F) {a b} (h : Reach E a b) :
    Reach F (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact ih.tail (hm _ _ he)

private theorem flip_reach {V : Type*} {E F : Finset (V × V)}
    (hm : ∀ u v, (u,v) ∈ E → (v,u) ∈ F) {a b} (h : Reach E a b) :
    Reach F b a := by
  induction h with
  | refl => exact .refl
  | tail _ he ih => exact (Relation.ReflTransGen.single (hm _ _ he)).trans ih

theorem thin_strong {V : Type*} [Fintype V] (E : Finset (V × V)) (r : V)
    (h : ∀ v, Reach E r v ∧ Reach E v r) :
    ∃ U ⊆ E, U.card ≤ 2*(Fintype.card V - 1) ∧ ∀ a b, Reach U a b := by
  classical
  let F := E.image Prod.swap
  have rev (u v) (hv : (u,v) ∈ E) : (v,u) ∈ F := Finset.mem_image_of_mem Prod.swap hv
  obtain ⟨T,hTE,hTc,hT⟩ := thin_out E r (fun v => (h v).1)
  obtain ⟨S,hSF,hSc,hS⟩ := thin_out F r (fun v => flip_reach rev (h v).2)
  let U := T ∪ S.image Prod.swap
  have hsub : U ⊆ E := by
    intro e he
    rcases Finset.mem_union.mp he with ht | hs
    · exact hTE ht
    · obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp (hSF he')
      simpa [←hxe] using hx
  refine ⟨U,hsub,?_,?_⟩
  · calc U.card ≤ T.card + (S.image Prod.swap).card := Finset.card_union_le _ _
         _ ≤ T.card + S.card := Nat.add_le_add_left Finset.card_image_le _
         _ ≤ _ := by omega
  · intro a b
    have ha : Reach U a r := flip_reach (E := S)
      (fun _ _ he => Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.swap he)) (hS a)
    have hb : Reach U r b := lift_reach id (E := T) (F := U)
      (fun _ _ he => Finset.mem_union_left _ he) (hT b)
    exact ha.trans hb

open PEqualNP.Outside.L_lib_1176.Work

def project {b c} (f : Fin b → Fin c) (D : Hidden b) : Hidden c :=
  D.image fun l => (f l.1,l.2)

theorem holds_project {b c} (f : Fin b → Fin c) (D : Hidden b) (h : Fin c → Bool) :
    Holds (project f D) h ↔ Holds D (h ∘ f) := by
  constructor
  · rintro ⟨_,hmem,hl⟩
    obtain ⟨l,hlD,rfl⟩ := Finset.mem_image.mp hmem
    exact ⟨l,hlD,hl⟩
  · rintro ⟨l,hlD,hl⟩
    exact ⟨_,Finset.mem_image_of_mem _ hlD,hl⟩

theorem project_core {b c} {K J : Finset (Hidden b)} (hK : UnsatCore K)
    (sub : J ⊆ K) (f : Fin b → Fin c)
    (taut : ∀ D ∈ K, D ∉ J → ∀ h : Fin c → Bool, Holds D (h ∘ f))
    (repair : ∀ D ∈ J, ∃ h : Fin c → Bool, ∀ E ∈ J, E ≠ D → Holds E (h ∘ f)) :
    let Q := J.image (project f)
    UnsatCore Q ∧ triples Q ≤ triples K ∧ load K ≤ load Q + load (K \ J) := by
  classical
  let g := project f
  let Q := J.image g
  have unsat : ∀ h : Fin c → Bool, ∃ D ∈ J, ¬Holds D (h ∘ f) := by
    intro h
    obtain ⟨D,hD,hnot⟩ := hK.1 (h ∘ f)
    exact ⟨D, Classical.byContradiction (fun hno => hnot (taut D hD hno h)), hnot⟩
  have inj : Set.InjOn g J := by
    intro D hD E hE hde
    by_contra hn
    obtain ⟨h,hd⟩ := repair D hD
    obtain ⟨F,hF,hbad⟩ := unsat h
    by_cases hf : F = D
    · subst F
      apply hbad
      apply (holds_project f D h).mp
      change Holds (g D) h
      rw [hde]
      exact (holds_project f E h).mpr (hd E hE (Ne.symm hn))
    · exact hbad (hd F hF hf)
  have width (D) (hD : D ∈ J) : 1 ≤ (g D).card ∧ (g D).card ≤ D.card := by
    obtain ⟨l,hl⟩ := Finset.card_pos.mp (hK.2.2 D (sub hD)).1
    exact ⟨Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ hl⟩, Finset.card_image_le⟩
  have core : UnsatCore Q := by
    refine ⟨?_,?_,?_⟩
    · intro h
      obtain ⟨D,hD,hd⟩ := unsat h
      exact ⟨g D,Finset.mem_image_of_mem _ hD,fun hp => hd ((holds_project f D h).mp hp)⟩
    · intro F hF
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨h,hd⟩ := repair D hD
      refine ⟨h,?_⟩
      intro G hG hne
      obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hG
      exact (holds_project f E h).mpr (hd E hE (fun he => hne (congrArg g he)))
    · intro F hF
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hF
      exact ⟨(width D hD).1,(width D hD).2.trans (hK.2.2 D (sub hD)).2⟩
  have tripleSub : Q.filter (fun D => D.card = 3) ⊆ (K.filter (fun D => D.card = 3)).image g := by
    intro F hF
    obtain ⟨hF,hthree⟩ := Finset.mem_filter.mp hF
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hF
    have hw := (width D hD).2
    have hw' := (hK.2.2 D (sub hD)).2
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨sub hD,by omega⟩)
  have mono (p : Hidden b → Prop) (q : Hidden c → Prop) [DecidablePred p] [DecidablePred q]
      (hm : ∀ D ∈ J, p D → q (g D)) : (J.filter p).card ≤ (Q.filter q).card := by
    have ih : Set.InjOn g (J.filter p) := fun _ hx _ hy he =>
      inj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 he
    rw [← Finset.card_image_of_injOn ih]
    apply Finset.card_le_card
    intro F hF
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨hj,hp⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hj,hm D hj hp⟩
  have small := mono (fun D => D.card ≤ 2) (fun D => D.card ≤ 2)
    (fun D hD h => (width D hD).2.trans h)
  have unit := mono (fun D => D.card = 1) (fun D => D.card = 1)
    (fun D hD h => by have := width D hD; omega)
  have split (p : Hidden b → Prop) [DecidablePred p] :
      ((K \ J).filter p).card + (J.filter p).card = (K.filter p).card := by
    have eq : (K \ J).filter p = K.filter p \ J.filter p := by
      ext D
      simp only [Finset.mem_sdiff,Finset.mem_filter]
      tauto
    rw [eq]
    apply Finset.card_sdiff_add_card_eq_card
    intro D hD
    obtain ⟨hD,hp⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr ⟨sub hD,hp⟩
  refine ⟨core, (Finset.card_le_card tripleSub).trans Finset.card_image_le, ?_⟩
  change load K ≤ load Q + load (K \ J)
  unfold load
  have s1 := split (fun D => D.card ≤ 2)
  have s2 := split (fun D => D.card = 1)
  omega

def implClause {b} (a z : Fin b) : Hidden b := {(a,false),(z,true)}

theorem holds_implClause {b} (a z : Fin b) (h : Fin b → Bool) :
    Holds (implClause a z) h ↔ (h a = true → h z = true) := by
  cases ha : h a <;> cases hz : h z <;> simp [implClause,Holds,ha,hz]

private theorem propagate {V : Type*} {T : Finset (V × V)} (H : V → Prop)
    (hh : ∀ u v, (u,v) ∈ T → H u → H v) {a b} (hr : Reach T a b) : H a → H b := by
  induction hr with
  | refl => exact id
  | tail _ he ih => exact fun ha => hh _ _ he (ih ha)

theorem shrink_strong_component {b} {K : Finset (Hidden b)} (hK : UnsatCore K)
    (S : Finset (Fin b)) (r : S) (hsize : 2 ≤ S.card)
    (E : Finset (S × S)) (hmem : ∀ u v, (u,v) ∈ E → implClause u.1 v.1 ∈ K)
    (hreach : ∀ v, Reach E r v ∧ Reach E v r) :
    ∃ c, 0 < c ∧ c < b ∧ c + (S.card - 1) = b ∧
      ∃ Q : Finset (Hidden c), UnsatCore Q ∧ triples Q ≤ triples K ∧
        load K ≤ load Q + 2*(b-c) := by
  classical
  obtain ⟨T,hTE,hcard,ht⟩ := thin_strong E r hreach
  let L : Finset (Hidden b) := T.image fun p => implClause p.1.1 p.2.1
  let J := K \ L
  have hLK : L ⊆ K := by
    intro D hD
    obtain ⟨⟨u,v⟩,ht,rfl⟩ := Finset.mem_image.mp hD
    exact hmem u v (hTE ht)
  have removed : K \ J ⊆ L := by
    intro D hd
    have h := Finset.mem_sdiff.mp hd
    exact Classical.byContradiction fun hn => h.2 (Finset.mem_sdiff.mpr ⟨h.1,hn⟩)
  let A := (Finset.univ : Finset (Fin b)) \ S.erase r.1
  let c := Fintype.card A
  have hrA : r.1 ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.notMem_erase _ _⟩
  let rr : A := ⟨r.1,hrA⟩
  let repr (v : Fin b) : A := if hv : v ∈ S then rr else
    ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun he => hv (Finset.mem_erase.mp he).2⟩⟩
  let e : A ≃ Fin c := Fintype.equivFin A
  let f (v : Fin b) : Fin c := e (repr v)
  have component (v : S) : f v.1 = e rr := by simp [f,repr,v.2]
  have count : c + (S.card - 1) = b := by
    have h := Finset.card_sdiff_add_card_eq_card (s := S.erase r.1) (Finset.subset_univ _)
    simpa [c,A,Finset.card_erase_of_mem r.2] using h
  have hc : 0 < c := by change 0 < Fintype.card A; exact Fintype.card_pos_iff.mpr ⟨rr⟩
  have hproj := project_core (J := J) hK Finset.sdiff_subset f
  have core := hproj (by
    intro D hD hn h
    obtain ⟨⟨u,v⟩,_,rfl⟩ := Finset.mem_image.mp (removed (Finset.mem_sdiff.mpr ⟨hD,hn⟩))
    exact (holds_implClause _ _ _).mpr (by simp [component])) (by
    intro D hD
    have dh := Finset.mem_sdiff.mp hD
    obtain ⟨H,hH⟩ := hK.2.1 D dh.1
    have prop (u v : S) (he : (u,v) ∈ T) : H u.1 = true → H v.1 = true := by
      have hl : implClause u.1 v.1 ∈ L := Finset.mem_image_of_mem _ he
      exact (holds_implClause _ _ _).mp (hH _ (hLK hl) (by intro h; exact dh.2 (h ▸ hl)))
    have same (v : S) : H v.1 = H r.1 := by
      have h1 := propagate (fun w : S => H w.1 = true) prop (ht v r)
      have h2 := propagate (fun w : S => H w.1 = true) prop (ht r v)
      cases hv : H v.1 <;> cases hr : H r.1 <;> simp_all
    let h (w : Fin c) := H (e.symm w).1
    have agree : h ∘ f = H := by
      funext v
      change H (e.symm (e (repr v))).1 = H v
      rw [e.symm_apply_apply]
      by_cases hv : v ∈ S
      · simpa [repr,hv,rr] using (same ⟨v,hv⟩).symm
      · simp [repr,hv]
    exact ⟨h, fun G hg hn => agree ▸ hH G (Finset.mem_sdiff.mp hg).1 hn⟩)
  have hz : (K \ J).filter (fun D => D.card = 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro D hd
    obtain ⟨hm,hw⟩ := Finset.mem_filter.mp hd
    obtain ⟨⟨u,v⟩,_,rfl⟩ := Finset.mem_image.mp (removed hm)
    simp [implClause] at hw
  have budget : load (K \ J) ≤ 2*(b-c) := by
    unfold load
    rw [hz,Finset.card_empty,Nat.add_zero]
    have ht' : T.card ≤ 2*(S.card-1) := by simpa using hcard
    have hl : L.card ≤ T.card := Finset.card_image_le
    have hm := Finset.card_le_card removed
    have hf := Finset.card_filter_le (s := K \ J) (p := fun D => D.card ≤ 2)
    omega
  exact ⟨c,hc,by omega,count,_,core.1,core.2.1,core.2.2.trans (Nat.add_le_add_left budget _)⟩

theorem shrink_cycle {b} {K : Finset (Hidden b)} (hK : UnsatCore K)
    {a : Fin b} (hcycle : Relation.TransGen (Arr K) a a) :
    ∃ c, 0 < c ∧ c < b ∧ ∃ Q : Finset (Hidden c), UnsatCore Q ∧
      triples Q ≤ triples K ∧ load K ≤ load Q + 2*(b-c) := by
  classical
  obtain ⟨z,haz,hza⟩ := Relation.TransGen.head'_iff.mp hcycle
  let R := Relation.ReflTransGen (Arr K)
  let S := Finset.univ.filter (fun v => R a v ∧ R v a)
  have mem {v} : v ∈ S ↔ R a v ∧ R v a := by simp [S]
  have ha : a ∈ S := mem.mpr ⟨.refl,.refl⟩
  have hz : z ∈ S := mem.mpr ⟨.single haz,hza⟩
  have hsize : 2 ≤ S.card := by
    have hs : ({a,z} : Finset _) ⊆ S := by
      intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ha
      · exact hz
    simpa [arr_ne hK haz] using Finset.card_le_card hs
  let E : Finset (S × S) := Finset.univ.filter fun p => Arr K p.1.1 p.2.1
  have edge {u v : S} : (u,v) ∈ E ↔ Arr K u.1 v.1 := by simp [E]
  have liftPath {u v : Fin b} (hu : u ∈ S) (h : R u v) :
      ∀ hv : v ∈ S, Reach E ⟨u,hu⟩ ⟨v,hv⟩ := by
    induction h with
    | refl => intro _; exact .refl
    | @tail w t huw hwt ih =>
      intro hS
      have hw : w ∈ S := mem.mpr ⟨(mem.mp hu).1.trans huw,
        (Relation.ReflTransGen.single hwt).trans (mem.mp hS).2⟩
      exact (ih hw).tail (edge.mpr hwt)
  obtain ⟨c,hc,hcb,_,Q,hQ,ht,hl⟩ := shrink_strong_component hK S ⟨a,ha⟩ hsize E
    (fun _ _ he => edge.mp he) (fun v => ⟨liftPath ha (mem.mp v.2).1 v.2,
      liftPath v.2 (mem.mp v.2).2 ha⟩)
  exact ⟨c,hc,hcb,Q,hQ,ht,hl⟩

end PEqualNP.Outside.L_lib_1176.Compression

namespace PEqualNP.Outside.L_lib_1176.Work
def Rich {b} (K : Finset (Hidden b)) := ∀ v, v∈Marked K ∨ ∃ u z, u≠z ∧ Arr K u v ∧ Arr K z v
def Drops {b} (K : Finset (Hidden b)) := ∃ c : Nat, 0<c ∧ c<b ∧ ∃ H : Finset (Hidden c), UnsatCore H ∧ triples H ≤ triples K ∧ load K ≤ load H + 2*(b-c)
private theorem noPos_unused {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (x : Fin b) (hn : ∀ D∈K, (x,true)∉D) : ∀ D∈K, ∀ l∈D, l.1≠x := by
  intros D hd l hl eq; obtain ⟨z,s⟩ := l; change z=x at eq; subst z
  cases s with
  | true => exact hn D hd hl
  | false =>
    obtain ⟨w,hw⟩ := hu.2.1 D hd
    let h := fun v : Fin b => if v=x then false else w v
    obtain ⟨E,he,hbad⟩ := hu.1 h
    apply hbad
    by_cases e : E=D
    · subst E; exact ⟨(x,false),hl,by simp [h]⟩
    · obtain ⟨⟨a,t⟩,ha,hv⟩ := hw E he e
      refine ⟨(a,t),ha,?_⟩; change h a=t
      by_cases e : a=x
      · subst a; cases t with
        | true => exact (hn E he ha).elim
        | false => simp [h]
      · simpa [h,e] using hv
theorem lowDrops {b} {K : Finset (Hidden (b+1))} (hb : 0 < b) (hu : UnsatCore K) (ho : Oriented K) (hr : ¬Rich K) : Drops K := by
  classical
  have hnot : ¬∀ v, v∈Marked K ∨ ∃ u z, u≠z ∧ Arr K u v ∧ Arr K z v := hr
  obtain ⟨x,hx⟩ := Classical.not_forall.mp hnot
  have hm : x∉Marked K := fun h => hx (.inl h)
  refine ⟨b,hb,by omega,?_⟩
  by_cases hp : ∃ y, Arr K y x
  · obtain ⟨y,hy⟩ := hp
    have hyx := arr_ne hu hy
    have hs : ∀ D∈K, D ≠ {(y,false),(x,true)} → (x,true) ∉ D := by
      intro D hD hne htrue
      obtain ⟨z,hz,hdef⟩ := unmarked_positive hu ho hm hD htrue
      by_cases hzy : y=z
      · exact hne (hzy ▸ hdef)
      · exact hx (.inr ⟨y,z,hzy,hy,hz⟩)
    obtain ⟨H,hH,hl,ht,hunused⟩ := suppressIncoming K hu hyx.symm hy hs
    obtain ⟨Q,hQ,hQl,hQt⟩ := eraseUnused H hH x hunused
    exact ⟨Q,hQ,by omega,by omega⟩
  · have hn : ∀ D∈K, (x,true)∉D := by
      intro D hmD hs
      obtain ⟨y,hy,_⟩ := unmarked_positive hu ho hm hmD hs
      exact hp ⟨y,hy⟩
    obtain ⟨Q,hQ,hQl,hQt⟩ := eraseUnused K hu x (noPos_unused hu x hn)
    exact ⟨Q,hQ,by omega,by omega⟩
abbrev SccDrops := ∀ {b} {K : Finset (Hidden b)}, UnsatCore K → ∀ a, Relation.TransGen (Arr K) a a → Drops K
abbrev DagBound := ∀ {s b} {K : Finset (Hidden b)}, UnsatCore K → Oriented K → triples K ≤ s → (∀ v, ¬Relation.TransGen (Arr K) v v) → Rich K → b ≤ lim s
theorem compression_of_steps (scc : SccDrops) (dag : DagBound) : Compress := by
  intro s b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro K hb hlimit hbig hu ht
    have h1 : 1 ≤ lim s := Nat.le_max_left _ _
    have hq : 0<triples K := by
      by_contra! hz
      have hzero := zeroTriplesLoad (K:=K) hb hu (show triples K=0 by omega)
      omega
    obtain ⟨N,hN,hL,hT,hO⟩ := orientCore hu hq
    have step : Drops N := by
      by_cases hm : ∀ v, ¬Relation.TransGen (Arr N) v v
      · by_cases hr : Rich N
        · have := dag hN hO (show triples N ≤ s by omega) hm hr
          omega
        cases b with
        | zero => omega
        | succ b => exact lowDrops (by omega) hN hO hr
      · obtain ⟨v,hv⟩ := Classical.not_forall.mp hm
        exact scc hN v (Classical.byContradiction hv)
    obtain ⟨c,hc,hcb,H,hH,hTH,hLH⟩ := step
    by_cases hcL : c ≤ lim s
    · exact ⟨c,H,hc,hcb.le,hcL,hH,by omega,by omega⟩
    · obtain ⟨d,T,hd,hdc,hdl,hU,htU,hLU⟩ := ih c hcb H hc (by omega) (by omega) hH (by omega)
      exact ⟨d,T,hd,by omega,hdl,hU,htU,by omega⟩
end PEqualNP.Outside.L_lib_1176.Work

namespace PEqualNP.Outside.L_lib_1176.Work.Dag
open PEqualNP.Outside.L_lib_1176.Compression Relation
private theorem path_of_reach {R : Nat → Nat → Prop} (up : ∀ ⦃u v⦄, R u v → u < v)
    {s t} (reach : ReflTransGen R s t) : ∃ P, IsPath R s t P := by
  induction reach with
  | refl =>
    refine ⟨{s}, by simp, by simp, ?_, ?_⟩
    · simp
    · rintro u v ⟨hu,hv,hlt,_⟩; simp only [Finset.mem_singleton] at hu hv; omega
  | @tail v t _ hvt ih =>
    obtain ⟨P,hs,hv,hb,ha⟩ := ih
    have hlt := up hvt
    refine ⟨insert t P, Finset.mem_insert_of_mem hs, Finset.mem_insert_self .., ?_, ?_⟩
    · intro w hw; rcases Finset.mem_insert.mp hw with rfl|hw
      · have := hb v hv; omega
      · have := hb w hw; omega
    · rintro u w ⟨hu,hw,huw,gap⟩
      rcases Finset.mem_insert.mp hu with rfl|hu0
      · rcases Finset.mem_insert.mp hw with he|hw
        · omega
        · have := hb w hw; omega
      · rcases Finset.mem_insert.mp hw with hew|hw0
        · have he : u = v := by
            have := hb u hu0
            by_contra hn; exact gap v (Finset.mem_insert_of_mem hv) (by omega) (by omega)
          simpa only [he,hew] using hvt
        · exact ha _ _ ⟨hu0,hw0,huw,fun z hz => gap z (Finset.mem_insert_of_mem hz)⟩

private theorem reach_of_path {P : Finset Nat} {s t R} (h : IsPath R s t P) :
    ReflTransGen (Enters P) s t := by
  suffices H : ∀ v ∈ P, ReflTransGen (Enters P) s v from H _ h.2.1
  intro v; induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv; by_cases he : s=v
    · subst v; exact .refl
    have hsv : s<v := lt_of_le_of_ne (h.2.2.1 v hv).1 he
    let T := P.filter (· < v)
    have ht : T.Nonempty := ⟨s,Finset.mem_filter.mpr ⟨h.1,hsv⟩⟩
    let u := T.max' ht
    have hT := Finset.mem_filter.mp (T.max'_mem ht)
    refine (ih u hT.2 hT.1).tail ⟨hT.1,hv,hT.2,?_⟩
    intro w hw huw hwv; exact huw.not_ge (T.le_max' _ (Finset.mem_filter.mpr ⟨hw,hwv⟩))

private theorem topological {b} {E : Fin b → Fin b → Prop}
    (acy : ∀ u v, E u v → ¬ReflTransGen E v u) :
    ∃ f : Fin b → Nat, Function.Injective f ∧ ∀ u v, E u v → f u < f v := by
  classical
  let S := fun v : Fin b => Finset.univ.filter (fun u => ReflTransGen E u v)
  let f := fun v : Fin b => (S v).card*b+v.val
  refine ⟨f,?_,?_⟩
  · intro u v he; apply Fin.ext
    have he' := congrArg (· % b) he
    simpa only [f,Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod,Nat.mod_eq_of_lt u.isLt,Nat.mod_eq_of_lt v.isLt] using he'
  · intro u v h; have hsub : S u ⊆ S v := by
      intro w hw; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hw).2.tail h⟩
    have hs : (S u).card < (S v).card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,by
      intro he; have hv : v ∈ S v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
      rw [← he] at hv; exact acy u v h (Finset.mem_filter.mp hv).2⟩)
    have hm := Nat.mul_le_mul_right b (Nat.succ_le_of_lt hs)
    simp only [Nat.succ_mul] at hm; dsimp [f]; omega

private def Branch {b} (E : Fin b → Fin b → Prop) (v : Fin b) :=
  ∃ u z, E u v ∧ E z v ∧ u ≠ z

theorem branch_bound {b} (E : Fin b → Fin b → Prop) (D : Finset (Fin b × Fin b))
    (acy : ∀ u v, E u v → ¬ReflTransGen E v u)
    (reach : ∀ d ∈ D, ReflTransGen E d.1 d.2)
    (force : ∀ R : Fin b → Fin b → Prop, (∀ u v, R u v → E u v) →
      (∀ d ∈ D, ReflTransGen R d.1 d.2) → ∀ u v, E u v → R u v)
    (B : Finset (Fin b)) (hB : ∀ v ∈ B, Branch E v) : B.card ≤ D.card.choose 2 := by
  classical
  by_cases hb : b=0
  · subst b; have : B=∅ := by ext v; exact Fin.elim0 v
    simp [this]
  letI : Nonempty (Fin b) := ⟨⟨0,by omega⟩⟩
  obtain ⟨f,inj,inc⟩ := topological acy
  let g := Function.invFun f
  have gf (v) : g (f v) = v := Function.leftInverse_invFun inj v
  let A := fun u v : Nat => ∃ x y : Fin b, f x=u ∧ f y=v ∧ E x y
  have up : ∀ {u v}, A u v → u<v := by rintro _ _ ⟨x,y,rfl,rfl,he⟩; exact inc _ _ he
  let d (i : Fin D.card) : Fin b × Fin b := (D.equivFin.symm i).val
  have hd (i) : d i ∈ D := (D.equivFin.symm i).property
  have rd (i) := ReflTransGen.lift (r := E) (p := A) f (fun u v h => ⟨u,v,rfl,rfl,h⟩) _ _ (reach (d i) (hd i))
  obtain ⟨P,path,coh⟩ := choose_coherent A (fun i => f (d i).1) (fun i => f (d i).2)
    (fun i => path_of_reach (R := A) (by intro u v h; exact up h) (rd i))
  let R := fun u v : Fin b => ∃ i, Enters (P i) (f u) (f v)
  have ends (i u v) (h : Enters (P i) u v) : f (g u)=u ∧ f (g v)=v ∧ E (g u) (g v) := by
    obtain ⟨x,y,rfl,rfl,ha⟩ := (path i).2.2.2 u v h; simp [gf,ha]
  have sub : ∀ u v, R u v → E u v := by
    rintro u v ⟨i,hi⟩; simpa only [gf] using (ends _ _ _ hi).2.2
  have requests (p) (hp : p ∈ D) : ReflTransGen R p.1 p.2 := by
    let i := D.equivFin ⟨p,hp⟩
    have h := ReflTransGen.lift (r := Enters (P i)) (p := R) g (fun u v hh =>
      ⟨i,by simpa only [(ends i u v hh).1,(ends i u v hh).2.1] using hh⟩) _ _ (reach_of_path (path i))
    simpa only [Function.onFun,gf,d,i,Equiv.symm_apply_apply] using h
  have cover := force R sub requests
  have bound := branch_card_le P coh (B.image f) (by
    intro v hv; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨u,z,hu,hz,hn⟩ := hB x hx
    obtain ⟨i,hi⟩ := cover u x hu; obtain ⟨j,hj⟩ := cover z x hz
    exact ⟨i,j,f u,f z,hi,hj,inj.ne hn⟩)
  simpa only [Finset.card_image_of_injective _ inj] using bound

private theorem arc_requests {b} {K : Finset (Hidden b)} (hu : UnsatCore K) (ho : Oriented K) :
    ∃ D : Finset (Fin b × Fin b), D.card ≤ 2 * ((Marked K).card * ((Marked K).card+1) / 2) ∧
      (∀ d ∈ D, ReflTransGen (Arr K) d.1 d.2) ∧
      ∀ R : Fin b → Fin b → Prop, (∀ u v, R u v → Arr K u v) →
        (∀ d ∈ D, ReflTransGen R d.1 d.2) → ∀ u v, Arr K u v → R u v := by
  classical
  obtain ⟨D,B,hD,_,hr,hn,extend⟩ := Obstruction.requests (Marked K) (Arr K) (Ban K)
  refine ⟨D,hD,hr,?_⟩
  intro R sub req u v huv
  by_contra hh
  obtain ⟨w,hw⟩ := hu.2.1 _ huv
  have hm : Obstruction.Model R (Ban K) (fun x => w x=true) := by
    constructor
    · intro x y h
      apply holds_arr_iff.mp (hw _ (sub x y h) ?_)
      intro eq
      obtain ⟨rfl,rfl⟩ := arr_clause_inj eq
      exact hh h
    · intro x y h hx hy
      exact holds_ban_iff.mp (hw _ h (arr_ne_ban u v x y).symm) ⟨hx,hy⟩
  obtain ⟨F,model,agree⟩ := extend R (Ban K) req hn _ hm
  let h := fun v => decide (F v)
  have ah (x) : h x=true ↔ F x := by simp [h]
  have all := graph_holds_all hu ho h w
    (fun x y he hx => (ah y).2 (model.1 x y he ((ah x).1 hx)))
    (fun x y he ⟨hx,hy⟩ => model.2 x y he ((ah x).1 hx) ((ah y).1 hy))
    (fun x hx => by simpa [h,agree x hx]) (fun D hD hc => hw D hD (by
      rintro rfl; simp at hc))
  obtain ⟨D,hD,hnD⟩ := hu.1 h; exact hnD (all D hD)

theorem kernel_bound {s b : Nat} {K : Finset (Hidden b)} (hu : UnsatCore K)
    (ho : Oriented K) (ht : triples K ≤ s)
    (acy : ∀ v, ¬TransGen (Arr K) v v)
    (irreducible : ∀ v, v ∈ Marked K ∨ ∃ u z, u ≠ z ∧ Arr K u v ∧ Arr K z v) :
    b ≤ lim s := by
  classical
  obtain ⟨D,hd,hr,hforce⟩ := arc_requests hu ho
  let B := (Finset.univ : Finset (Fin b)) \ Marked K
  have hb := branch_bound (Arr K) D (fun u v ha hr => acy u (TransGen.head' ha hr)) hr hforce B (by
    intro v hv; obtain ⟨u,z,hn,hu,hz⟩ := (irreducible v).resolve_left (Finset.mem_sdiff.mp hv).2
    exact ⟨u,z,hu,hz,hn⟩)
  let p := 3*s*(3*s+1)/2
  have hm : (Marked K).card ≤ 3*s := (marked_bound K).trans (Nat.mul_le_mul_left _ ht)
  have hmono : (Marked K).card * ((Marked K).card+1) /2 ≤ p := Nat.div_le_div_right
    (Nat.mul_le_mul hm (Nat.add_le_add_right hm 1))
  have hdim := hb.trans (Nat.choose_le_choose 2 (hd.trans (Nat.mul_le_mul_left _ hmono)))
  have hmark : (Marked K).card ≤ 2*p := by
    apply hm.trans
    suffices hp : 3*s ≤ p by omega
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    cases s <;> simp <;> nlinarith
  have hc : B.card + (Marked K).card = b := by
    simpa only [B,Finset.card_univ,Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Marked K))
  unfold lim; dsimp only
  apply le_trans _ (Nat.le_max_right _ _)
  rw [Nat.choose_two_right] at hdim; change b ≤ (2*p)*(2*p-1)/2+2*p; omega
end PEqualNP.Outside.L_lib_1176.Work.Dag

theorem PEqualNP.Outside.L_lib_1176 : (∀ s : Nat,
  let p := (3*s)*(3*s+1)/2
  let limit := max 1 ((2*p)*((2*p)-1)/2+2*p)
  let feasible := fun (b n : Nat) =>
    let Clause := Finset ((Fin n × Bool) × Bool) × Finset (Fin b × Bool)
    ∃ C : Finset Clause,
      (∀ x : Fin n → Bool → Bool, (∃ i, x i false=true ∧ x i true=true) ↔
        ∃ h : Fin b → Bool, ∀ c ∈ C,
          (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ ∃ l ∈ c.2, h l.1=l.2) ∧
      (∀ c ∈ C, c.1.card+c.2.card ≤ 3) ∧ C.card ≤ 2*n+s
  ∀ b n : Nat, 0 < b → 2*b ≤ n → feasible b n →
    ∃ c d : Nat, 0 < c ∧ c ≤ b ∧ c ≤ limit ∧ feasible c d ∧ n+2*c ≤ d+2*b) := by
  intro s
  change ∀ b n : Nat, 0 < b → 2*b ≤ n → PEqualNP.Outside.L_lib_1176.Work.Feasible s b n →
    PEqualNP.Outside.L_lib_1176.Work.Result s b n
  intro b n hb _ hf
  apply PEqualNP.Outside.L_lib_1176.Work.assemble PEqualNP.Outside.L_lib_1176_aux.coreIff _ s b n hb hf
  apply PEqualNP.Outside.L_lib_1176.Work.compression_of_steps
  · exact fun h _ cyc => PEqualNP.Outside.L_lib_1176.Compression.shrink_cycle h cyc
  · exact fun hu ho ht ha hr => PEqualNP.Outside.L_lib_1176.Work.Dag.kernel_bound hu ho ht ha hr
