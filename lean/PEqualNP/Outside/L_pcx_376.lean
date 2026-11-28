import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_376_aux

open PEqualNP.ProofComplexity

section BasicLinEq

variable {V : Type}

lemma negLinEq_invol (e : LinEq V) : negLinEq (negLinEq e) = e := by
  rcases e with ⟨s, b⟩
  simp [negLinEq]

lemma linEqSat_neg_iff (x : V → Bool) (e : LinEq V) :
    LinEqSat x (negLinEq e) ↔ ¬ LinEqSat x e := by
  rcases e with ⟨s, b⟩
  cases b <;> simp [LinEqSat, negLinEq]

lemma linEqSat_single_iff [DecidableEq V] (x : V → Bool) (v : V) (s : Bool) :
    LinEqSat x (({v} : Finset V), s) ↔ x v = s := by
  cases h : x v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

lemma linTermSat_empty (x : V → Bool) : LinTermSat x (∅ : LinTerm V) := by
  intro q hq; simp at hq

lemma linTermSat_insert [DecidableEq V] (x : V → Bool) (e : LinEq V) (T : LinTerm V) :
    LinTermSat x (insert e T) ↔ LinEqSat x e ∧ LinTermSat x T := by
  simp [LinTermSat]

lemma linTermSat_union [DecidableEq V] (x : V → Bool) (T₁ T₂ : LinTerm V) :
    LinTermSat x (T₁ ∪ T₂) ↔ LinTermSat x T₁ ∧ LinTermSat x T₂ := by
  simp only [LinTermSat, Finset.mem_union]
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h1, h2⟩ q (hq | hq)
    · exact h1 q hq
    · exact h2 q hq

end BasicLinEq

section ParityTrees

variable {V : Type} [Fintype V] [DecidableEq V]

def vec (x : V → Bool) : V → ZMod 2 := fun v => if x v then 1 else 0

def unvec (u : V → ZMod 2) : V → Bool := fun v => decide (u v = 1)

omit [Fintype V] [DecidableEq V] in
lemma unvec_vec (x : V → Bool) : unvec (vec x) = x := by
  funext v
  cases hx : x v <;> simp [vec, unvec, hx]

omit [Fintype V] [DecidableEq V] in
lemma vec_unvec (u : V → ZMod 2) : vec (unvec u) = u := by
  funext v
  have hv : u v = 0 ∨ u v = 1 := by
    generalize u v = c
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hv with h | h <;> simp [vec, unvec, h]

def linForm (s : Finset V) : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun u := ∑ v ∈ s, u v
  map_add' u w := by simp [Finset.sum_add_distrib]
  map_smul' c u := by simp [Finset.mul_sum]

omit [Fintype V] [DecidableEq V] in
lemma linEqSat_iff_zmod (x : V → Bool) (e : LinEq V) :
    LinEqSat x e ↔ linForm e.1 (vec x) = if e.2 then 1 else 0 := by
  have hsum : linForm e.1 (vec x) = ((e.1.filter (fun v => x v = true)).card : ZMod 2) := by
    simp only [linForm, LinearMap.coe_mk, AddHom.coe_mk, vec]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [LinEqSat, hsum]
  set n := (e.1.filter (fun v => x v = true)).card
  have h2z : (2 : ZMod 2) = 0 := by decide
  have hodd : Odd n ↔ (n : ZMod 2) = 1 := by
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [hm]
      have h0 : ((m + m : ℕ) : ZMod 2) = 0 := by
        rw [Nat.cast_add, ← two_mul, h2z, zero_mul]
      rw [h0]
      constructor
      · rintro ⟨k, hk⟩; omega
      · intro h1; exact absurd h1 (by decide)
    · rw [hm]
      have h1 : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2z, zero_mul, zero_add, Nat.cast_one]
      rw [h1]
      exact ⟨fun _ => rfl, fun _ => ⟨m, rfl⟩⟩
  cases hb : e.2 <;> simp [hodd]
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rw [hm]
    have h0 : ((m + m : ℕ) : ZMod 2) = 0 := by
      rw [Nat.cast_add, ← two_mul, h2z, zero_mul]
    rw [h0]
    exact ⟨fun _ => rfl, fun _ => by decide⟩
  · rw [hm]
    have h1 : ((2 * m + 1 : ℕ) : ZMod 2) = 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2z, zero_mul, zero_add, Nat.cast_one]
    rw [h1]
    exact ⟨fun h => (h rfl).elim, fun h => absurd h (by decide)⟩

def kerOf (P : LinTerm V) : Submodule (ZMod 2) (V → ZMod 2) :=
  { carrier := {u | ∀ e ∈ P, linForm e.1 u = 0}, add_mem' := fun {u w} hu hw e he => by rw [map_add, hu e he, hw e he, add_zero],
    zero_mem' := fun e _ => map_zero _, smul_mem' := fun c u hu e he => by rw [map_smul, hu e he, smul_zero] }

def resSub (K : Submodule (ZMod 2) (V → ZMod 2)) (S : LinTerm V) :
    Submodule (ZMod 2) (V → ZMod 2) :=
  K ⊓ kerOf S

noncomputable def resRank (K : Submodule (ZMod 2) (V → ZMod 2)) (S : LinTerm V) : ℕ :=
  Module.finrank (ZMod 2) K - Module.finrank (ZMod 2) (resSub K S)

lemma resRank_le_card (K : Submodule (ZMod 2) (V → ZMod 2)) (S : LinTerm V) :
    resRank K S ≤ S.card := by
  let φ : K →ₗ[ZMod 2] (S → ZMod 2) :=
    { toFun := fun u e => linForm e.1.1 u.1
      map_add' := fun u w => by funext e; simp [map_add]
      map_smul' := fun c u => by funext e; simp [map_smul] }
  have hker : Module.finrank (ZMod 2) (LinearMap.ker φ) =
      Module.finrank (ZMod 2) (resSub K S) := by
    refine LinearEquiv.finrank_eq
      { toFun := fun ⟨⟨u, hu⟩, hφ⟩ => ⟨u, hu, fun e he => by
          have := congrFun hφ ⟨e, he⟩
          simpa [φ] using this⟩
        invFun := fun ⟨u, huK, huS⟩ => ⟨⟨u, huK⟩, by
          ext ⟨e, he⟩
          simpa [φ] using huS e he⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank (ZMod 2) (LinearMap.range φ) ≤ S.card := by
    calc Module.finrank (ZMod 2) (LinearMap.range φ)
        ≤ Module.finrank (ZMod 2) (S → ZMod 2) := Submodule.finrank_le _
      _ = Fintype.card S := Module.finrank_pi (ZMod 2)
      _ = S.card := Fintype.card_coe S
  rw [resRank, ← hker]
  omega

lemma kerOf_mono {P P' : LinTerm V} (h : ∀ e ∈ P, ∃ e' ∈ P', e'.1 = e.1) :
    kerOf P' ≤ kerOf P := by
  intro u hu e he
  obtain ⟨e', he', h1⟩ := h e he
  rw [← h1]
  exact hu e' he'

lemma resRank_drop {P P' T₁ S : LinTerm V} {g : (V → Bool) → Bool}
    (hK : kerOf P' ≤ kerOf P)
    (hKT : kerOf P' ≤ kerOf T₁)
    (hT₁ : ∀ y, LinTermSat y T₁ → g y = true)
    (hS : ∀ y, LinTermSat y S → g y = false)
    {x₁ y₀ : V → Bool}
    (hx₁P : LinTermSat x₁ P) (hx₁T : LinTermSat x₁ T₁)
    (hy₀P : LinTermSat y₀ P) (hy₀S : LinTermSat y₀ S) :
    resRank (kerOf P') S < resRank (kerOf P) S := by
  set K := kerOf P
  set K' := kerOf P'
  set L := resSub K S
  have hLK : L ≤ K := inf_le_left
  have hK'K : K' ≤ K := hK
  have hLinf : L ⊓ K' = resSub K' S := by
    ext u
    simp only [L, resSub, Submodule.mem_inf]
    constructor
    · rintro ⟨⟨_, hS'⟩, hK''⟩; exact ⟨hK'', hS'⟩
    · rintro ⟨hK'', hS'⟩; exact ⟨⟨hK hK'', hS'⟩, hK''⟩
  have hsup_lt : L ⊔ K' < K := by
    refine lt_of_le_of_ne (sup_le hLK hK'K) ?_
    intro heq
    have hd : vec x₁ - vec y₀ ∈ K := by
      intro e he
      rw [map_sub, (linEqSat_iff_zmod x₁ e).1 (hx₁P e he),
          (linEqSat_iff_zmod y₀ e).1 (hy₀P e he), sub_self]
    rw [← heq, Submodule.mem_sup] at hd
    obtain ⟨u, huL, w, hwK', huw⟩ := hd
    let z : V → Bool := unvec (vec y₀ + u)
    have hzu : vec z = vec y₀ + u := vec_unvec _
    have hzw : vec z = vec x₁ - w := by
      rw [hzu]
      have : vec y₀ + u + w = vec x₁ := by
        calc vec y₀ + u + w = vec y₀ + (u + w) := by rw [add_assoc]
          _ = vec y₀ + (vec x₁ - vec y₀) := by rw [huw]
          _ = vec x₁ := add_sub_cancel _ _
      exact eq_sub_of_add_eq this
    have hzS : LinTermSat z S := by
      intro e he
      rw [linEqSat_iff_zmod, hzu, map_add, huL.2 e he, add_zero]
      exact (linEqSat_iff_zmod y₀ e).1 (hy₀S e he)
    have hzT : LinTermSat z T₁ := by
      intro e he
      rw [linEqSat_iff_zmod, hzw, map_sub, hKT hwK' e he, sub_zero]
      exact (linEqSat_iff_zmod x₁ e).1 (hx₁T e he)
    have h1 := hT₁ z hzT
    have h0 := hS z hzS
    rw [h1] at h0
    simp at h0
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq L K'
  have hlt := Submodule.finrank_lt_finrank_of_lt hsup_lt
  have hle1 := Submodule.finrank_mono (le_sup_left : L ≤ L ⊔ K')
  have hle2 := Submodule.finrank_mono (inf_le_right : L ⊓ K' ≤ K')
  change Module.finrank (ZMod 2) ↥K' - Module.finrank (ZMod 2) ↥(resSub K' S) <
      Module.finrank (ZMod 2) ↥K - Module.finrank (ZMod 2) ↥L
  rw [← hLinf]
  omega

inductive PTree (V : Type) where
  | leaf (val : Bool) : PTree V
  | node (e : LinEq V) (tPos tNeg : PTree V) : PTree V

def PTree.depth : PTree V → ℕ
  | .leaf _ => 0
  | .node _ t1 t2 => 1 + max t1.depth t2.depth

noncomputable def PTree.eval (x : V → Bool) : PTree V → Bool
  | .leaf b => b
  | .node e t1 t2 => by
      classical
      exact if LinEqSat x e then t1.eval x else t2.eval x

def PTree.paths : PTree V → Bool → Finset (LinTerm V)
  | .leaf c, b => if c = b then {∅} else ∅
  | .node e t1 t2, b =>
      (t1.paths b).image (insert e) ∪ (t2.paths b).image (insert (negLinEq e))

lemma PTree.paths_card_le (tr : PTree V) (b : Bool) :
    ∀ T ∈ tr.paths b, T.card ≤ tr.depth := by
  induction tr with
  | leaf c =>
    intro T hT
    by_cases hcb : c = b <;> simp [PTree.paths, PTree.depth, hcb] at hT
    subst hT; simp
  | node e t1 t2 ih1 ih2 =>
    intro T hT
    simp only [PTree.paths, Finset.mem_union, Finset.mem_image] at hT
    rcases hT with ⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩
    · have h1 := ih1 T' hT'
      have h2 := Finset.card_insert_le e T'
      simp only [PTree.depth]; omega
    · have h1 := ih2 T' hT'
      have h2 := Finset.card_insert_le (negLinEq e) T'
      simp only [PTree.depth]; omega

lemma PTree.paths_sat_iff (tr : PTree V) (b : Bool) (x : V → Bool) :
    LinKLineSat x (tr.paths b) ↔ tr.eval x = b := by
  induction tr with
  | leaf c =>
    by_cases hcb : c = b <;> simp [PTree.paths, PTree.eval, LinKLineSat, hcb, linTermSat_empty]
  | node e t1 t2 ih1 ih2 =>
    simp only [PTree.paths, PTree.eval, LinKLineSat, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨T, (⟨T', hT', rfl⟩ | ⟨T', hT', rfl⟩), hsat⟩
      · rw [linTermSat_insert] at hsat
        simp only [hsat.1, ↓reduceIte]
        exact ih1.1 ⟨T', hT', hsat.2⟩
      · rw [linTermSat_insert, linEqSat_neg_iff] at hsat
        simp only [hsat.1, ↓reduceIte]
        exact ih2.1 ⟨T', hT', hsat.2⟩
    · intro hev
      by_cases he : LinEqSat x e
      · simp only [he, ↓reduceIte] at hev
        obtain ⟨T', hT', hsat⟩ := ih1.2 hev
        exact ⟨insert e T', Or.inl ⟨T', hT', rfl⟩, (linTermSat_insert x e T').2 ⟨he, hsat⟩⟩
      · simp only [he, ↓reduceIte] at hev
        obtain ⟨T', hT', hsat⟩ := ih2.2 hev
        exact ⟨insert (negLinEq e) T', Or.inr ⟨T', hT', rfl⟩,
          (linTermSat_insert x (negLinEq e) T').2 ⟨(linEqSat_neg_iff x e).2 he, hsat⟩⟩

def branchList (es : List (LinEq V)) (P : LinTerm V)
    (cont : LinTerm V → PTree V) : PTree V :=
  match es with
  | [] => cont P
  | e :: es' =>
      .node e (branchList es' (insert e P) cont)
              (branchList es' (insert (negLinEq e) P) cont)

lemma branchList_depth (es : List (LinEq V)) (P : LinTerm V)
    (cont : LinTerm V → PTree V) (D : ℕ)
    (hD : ∀ P', (∀ e ∈ P, e ∈ P') →
      (∀ e ∈ es, e ∈ P' ∨ negLinEq e ∈ P') → (cont P').depth ≤ D) :
    (branchList es P cont).depth ≤ es.length + D := by
  induction es generalizing P with
  | nil =>
    simp only [branchList, List.length_nil, zero_add]
    exact hD P (fun _ h => h) (by simp)
  | cons e es' ih =>
    simp only [branchList, PTree.depth, List.length_cons]
    have h1 : (branchList es' (insert e P) cont).depth ≤ es'.length + D :=
      ih (insert e P) fun P' hsub hes =>
        hD P' (fun x hx => hsub x (Finset.mem_insert_of_mem hx)) (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inl (hsub x (Finset.mem_insert_self _ _))
          · exact hes x hx)
    have h2 : (branchList es' (insert (negLinEq e) P) cont).depth ≤ es'.length + D :=
      ih (insert (negLinEq e) P) fun P' hsub hes =>
        hD P' (fun x hx => hsub x (Finset.mem_insert_of_mem hx)) (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact Or.inr (hsub (negLinEq x) (Finset.mem_insert_self _ _))
          · exact hes x hx)
    omega

lemma branchList_eval (es : List (LinEq V)) (P : LinTerm V)
    (cont : LinTerm V → PTree V) (x : V → Bool) (hx : LinTermSat x P) :
    ∃ P', LinTermSat x P' ∧ (∀ e ∈ P, e ∈ P') ∧
      (∀ e ∈ es, e ∈ P' ∨ negLinEq e ∈ P') ∧
      (branchList es P cont).eval x = (cont P').eval x := by
  induction es generalizing P with
  | nil =>
    exact ⟨P, hx, fun _ h => h, by simp, rfl⟩
  | cons e es' ih =>
    simp only [branchList, PTree.eval]
    by_cases he : LinEqSat x e
    · simp only [he, ↓reduceIte]
      obtain ⟨P', hsat, hsub, hes, hev⟩ := ih (insert e P) ((linTermSat_insert x e P).2 ⟨he, hx⟩)
      refine ⟨P', hsat, fun z hz => hsub z (Finset.mem_insert_of_mem hz), ?_, hev⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl (hsub z (Finset.mem_insert_self _ _))
      · exact hes z hz
    · simp only [he, ↓reduceIte]
      have hne : LinEqSat x (negLinEq e) := (linEqSat_neg_iff x e).2 he
      obtain ⟨P', hsat, hsub, hes, hev⟩ :=
        ih (insert (negLinEq e) P) ((linTermSat_insert x (negLinEq e) P).2 ⟨hne, hx⟩)
      refine ⟨P', hsat, fun z hz => hsub z (Finset.mem_insert_of_mem hz), ?_, hev⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inr (hsub (negLinEq z) (Finset.mem_insert_self _ _))
      · exact hes z hz

lemma buildTree_aux (g : (V → Bool) → Bool) (q : ℕ)
    (h1 : ∀ x, g x = true → ∃ T : LinTerm V, T.card ≤ q ∧ LinTermSat x T ∧
      ∀ y, LinTermSat y T → g y = true) :
    ∀ (d : ℕ) (P : LinTerm V),
      (∀ x, LinTermSat x P → g x = false → ∃ S : LinTerm V, resRank (kerOf P) S ≤ d ∧
        LinTermSat x S ∧ ∀ y, LinTermSat y S → g y = false) →
      ∃ tr : PTree V, tr.depth ≤ d * q ∧ ∀ x, LinTermSat x P → tr.eval x = g x := by
  classical
  intro d
  induction d with
  | zero =>
    intro P h0
    by_cases hT : ∃ x, LinTermSat x P ∧ g x = true
    · obtain ⟨x₁, hx₁P, hx₁g⟩ := hT
      refine ⟨.leaf true, by simp [PTree.depth], fun x hxP => ?_⟩
      simp only [PTree.eval]
      cases hgx : g x with
      | true => rfl
      | false =>
        exfalso
        obtain ⟨S, hrank, hxS, hSg⟩ := h0 x hxP hgx
        have hfin_eq : Module.finrank (ZMod 2) (resSub (kerOf P) S) =
            Module.finrank (ZMod 2) (kerOf P) := by
          have hle : Module.finrank (ZMod 2) (resSub (kerOf P) S) ≤
              Module.finrank (ZMod 2) (kerOf P) := Submodule.finrank_mono inf_le_left
          rw [resRank] at hrank
          omega
        have hsub_eq : resSub (kerOf P) S = kerOf P :=
          Submodule.eq_of_le_of_finrank_eq inf_le_left hfin_eq
        have hd : vec x₁ - vec x ∈ kerOf P := by
          intro e he
          rw [map_sub, (linEqSat_iff_zmod x₁ e).1 (hx₁P e he),
              (linEqSat_iff_zmod x e).1 (hxP e he), sub_self]
        rw [← hsub_eq] at hd
        have hx₁S : LinTermSat x₁ S := by
          intro e he
          rw [linEqSat_iff_zmod]
          have hdiff := hd.2 e he
          rw [map_sub, sub_eq_zero] at hdiff
          rw [hdiff]
          exact (linEqSat_iff_zmod x e).1 (hxS e he)
        have := hSg x₁ hx₁S
        rw [hx₁g] at this
        simp at this
    · refine ⟨.leaf false, by simp [PTree.depth], fun x hxP => ?_⟩
      simp only [PTree.eval]
      cases hgx : g x with
      | false => rfl
      | true => exact (hT ⟨x, hxP, hgx⟩).elim
  | succ d ih =>
    intro P h0
    by_cases hT : ∃ x, LinTermSat x P ∧ g x = true
    · obtain ⟨x₁, hx₁P, hx₁g⟩ := hT
      obtain ⟨T₁, hT₁card, hx₁T₁, hT₁g⟩ := h1 x₁ hx₁g
      have hbranch : ∀ P', (∀ e ∈ P, e ∈ P') → (∀ e ∈ T₁.toList, e ∈ P' ∨ negLinEq e ∈ P') →
          ∃ tr : PTree V, tr.depth ≤ d * q ∧ ∀ x, LinTermSat x P' → tr.eval x = g x := by
        intro P' hPP' hT₁P'
        have hK : kerOf P' ≤ kerOf P := kerOf_mono fun e he => ⟨e, hPP' e he, rfl⟩
        have hKT : kerOf P' ≤ kerOf T₁ := kerOf_mono fun e he => by
          rcases hT₁P' e (Finset.mem_toList.2 he) with h | h
          · exact ⟨e, h, rfl⟩
          · exact ⟨negLinEq e, h, rfl⟩
        refine ih P' fun x hxP' hgx => ?_
        have hxP : LinTermSat x P := fun e he => hxP' e (hPP' e he)
        obtain ⟨S, hrank, hxS, hSg⟩ := h0 x hxP hgx
        have hlt := resRank_drop hK hKT hT₁g hSg hx₁P hx₁T₁ hxP hxS
        exact ⟨S, by omega, hxS, hSg⟩
      let cont : LinTerm V → PTree V := fun P' =>
        if h : (∀ e ∈ P, e ∈ P') ∧ (∀ e ∈ T₁.toList, e ∈ P' ∨ negLinEq e ∈ P')
        then (hbranch P' h.1 h.2).choose
        else .leaf false
      refine ⟨branchList T₁.toList P cont, ?_, ?_⟩
      · have hd1 := branchList_depth T₁.toList P cont (d * q) fun P' h1' h2' => by
          have h12 : (∀ e ∈ P, e ∈ P') ∧ (∀ e ∈ T₁.toList, e ∈ P' ∨ negLinEq e ∈ P') := ⟨h1', h2'⟩
          dsimp only [cont]
          rw [dif_pos h12]
          exact (hbranch P' h1' h2').choose_spec.1
        have hlen : T₁.toList.length = T₁.card := Finset.length_toList T₁
        rw [Nat.succ_mul, Nat.add_comm (d * q)]
        omega
      · intro x hxP
        obtain ⟨P', hxP', h1', h2', hev⟩ := branchList_eval T₁.toList P cont x hxP
        rw [hev]
        have h12 : (∀ e ∈ P, e ∈ P') ∧ (∀ e ∈ T₁.toList, e ∈ P' ∨ negLinEq e ∈ P') := ⟨h1', h2'⟩
        dsimp only [cont]
        rw [dif_pos h12]
        exact (hbranch P' h1' h2').choose_spec.2 x hxP'
    · refine ⟨.leaf false, by simp [PTree.depth], fun x hxP => ?_⟩
      simp only [PTree.eval]
      cases hgx : g x with
      | false => rfl
      | true => exact (hT ⟨x, hxP, hgx⟩).elim

lemma exists_parity_tree (p q : ℕ) (g : (V → Bool) → Bool)
    (hcert : ∀ x : V → Bool, ∃ T : LinTerm V, T.card ≤ (if g x then q else p) ∧
      LinTermSat x T ∧ ∀ y : V → Bool, LinTermSat y T → g y = g x) :
    ∃ tr : PTree V, tr.depth ≤ p * q ∧ ∀ x, tr.eval x = g x := by
  have h1 : ∀ x, g x = true → ∃ T : LinTerm V, T.card ≤ q ∧ LinTermSat x T ∧
      ∀ y, LinTermSat y T → g y = true := by
    intro x hgx
    obtain ⟨T, hc, hs, hf⟩ := hcert x
    rw [hgx] at hc hf
    exact ⟨T, by simpa using hc, hs, fun y hy => by simpa using hf y hy⟩
  have h0 : ∀ x, LinTermSat x (∅ : LinTerm V) → g x = false →
      ∃ S : LinTerm V, resRank (kerOf (∅ : LinTerm V)) S ≤ p ∧
        LinTermSat x S ∧ ∀ y, LinTermSat y S → g y = false := by
    intro x _ hgx
    obtain ⟨S, hc, hs, hf⟩ := hcert x
    rw [hgx] at hc hf
    exact ⟨S, (resRank_le_card _ S).trans (by simpa using hc), hs,
      fun y hy => by simpa using hf y hy⟩
  obtain ⟨tr, hd, hev⟩ := buildTree_aux g q h1 p ∅ h0
  exact ⟨tr, hd, fun x => hev x (linTermSat_empty x)⟩

def PTree.flip : PTree V → PTree V
  | .leaf b => .leaf (!b)
  | .node e t1 t2 => .node e t1.flip t2.flip

lemma PTree.depth_flip (tr : PTree V) : tr.flip.depth = tr.depth := by
  induction tr with
  | leaf _ => rfl
  | node _ _ _ ih1 ih2 => simp [PTree.flip, PTree.depth, ih1, ih2]

lemma PTree.eval_flip (tr : PTree V) (x : V → Bool) : tr.flip.eval x = !(tr.eval x) := by
  induction tr with
  | leaf _ => rfl
  | node e t1 t2 ih1 ih2 =>
    simp only [PTree.flip, PTree.eval]
    split_ifs <;> simp [ih1, ih2]

lemma PTree.paths_flip (tr : PTree V) (b : Bool) : tr.flip.paths b = tr.paths (!b) := by
  induction tr with
  | leaf c =>
    cases c <;> cases b <;> simp [PTree.flip, PTree.paths]
  | node e t1 t2 ih1 ih2 =>
    simp [PTree.flip, PTree.paths, ih1, ih2]

end ParityTrees

section ResMerge

variable {U : Type} [DecidableEq U]

lemma res_subsumed {F : Set (Clause U)} {π : List (Clause U)} (hπ : IsDerivation F π)
    {C D R C' D' : Clause U} (hC' : C' ∈ π) (hD' : D' ∈ π)
    (hsubC : C' ⊆ C) (hsubD : D' ⊆ D) (hR : IsResolvent C D R) :
    ∃ (π' : List (Clause U)) (R' : Clause U),
      IsDerivation F π' ∧ (∀ X ∈ π, X ∈ π') ∧ R' ∈ π' ∧ R' ⊆ R ∧
      π'.length ≤ π.length + 1 := by
  obtain ⟨v, hvC, hvD, rfl⟩ := hR
  by_cases h1 : (v, true) ∈ C'
  · by_cases h2 : (v, false) ∈ D'
    · let R' := C'.erase (v, true) ∪ D'.erase (v, false)
      have hRes' : IsResolvent C' D' R' := ⟨v, h1, h2, rfl⟩
      have hsub : R' ⊆ C.erase (v, true) ∪ D.erase (v, false) :=
        Finset.union_subset_union (Finset.erase_subset_erase _ hsubC)
          (Finset.erase_subset_erase _ hsubD)
      exact ⟨R' :: π, R', .res hπ hC' hD' hRes',
        fun _ hx => List.mem_cons_of_mem _ hx, List.mem_cons_self, hsub, by simp⟩
    · refine ⟨π, D', hπ, fun _ hx => hx, hD', ?_, by omega⟩
      intro l hl
      exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨fun e => h2 (e ▸ hl), hsubD hl⟩)
  · refine ⟨π, C', hπ, fun _ hx => hx, hC', ?_, by omega⟩
    intro l hl
    exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun e => h1 (e ▸ hl), hsubC hl⟩)

def satBy {H : Type} (m : H → Bool) (C : Clause (U ⊕ H)) : Prop :=
  ∃ l ∈ C, ∃ b : H, l.1 = Sum.inr b ∧ m b = l.2

def restrClause {H : Type} [DecidableEq H] (C : Clause (U ⊕ H)) : Clause U :=
  C.biUnion fun l => match l.1 with | Sum.inl u => {(u, l.2)} | Sum.inr _ => ∅

lemma mem_restrClause {H : Type} [DecidableEq H] (C : Clause (U ⊕ H)) (u : U) (s : Bool) :
    (u, s) ∈ restrClause C ↔ (Sum.inl u, s) ∈ C := by
  simp only [restrClause, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨x, t⟩, hxt, hmem⟩
    cases x with
    | inl u' =>
      simp only [Finset.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩; exact hxt
    | inr _ => simp at hmem
  · intro h
    exact ⟨(Sum.inl u, s), h, by simp⟩

lemma card_restrClause {H : Type} [DecidableEq H] (C : Clause (U ⊕ H)) :
    (restrClause C).card = (C.filter (fun l => l.1.isLeft)).card := by
  have heq : restrClause C = (C.filter (fun l => l.1.isLeft)).attach.image
      (fun l => match h : l.1.1 with
        | Sum.inl u => (u, l.1.2)
        | Sum.inr _ => by
            have := (Finset.mem_filter.1 l.2).2
            simp [h] at this) := by
    ext ⟨u, s⟩
    rw [mem_restrClause, Finset.mem_image]
    constructor
    · intro h
      refine ⟨⟨(Sum.inl u, s), Finset.mem_filter.2 ⟨h, by simp⟩⟩, Finset.mem_attach _ _, rfl⟩
    · rintro ⟨⟨⟨x, t⟩, hx⟩, _, hEq⟩
      cases x with
      | inl u' =>
        simp only [Prod.mk.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        exact (Finset.mem_filter.1 hx).1
      | inr _ =>
        have := (Finset.mem_filter.1 hx).2
        simp at this
  rw [heq, Finset.card_image_of_injective, Finset.card_attach]
  rintro ⟨⟨x1, t1⟩, hx1⟩ ⟨⟨x2, t2⟩, hx2⟩ hEq
  cases x1 with
  | inr _ => exact absurd (Finset.mem_filter.1 hx1).2 (by simp)
  | inl u1 =>
    cases x2 with
    | inr _ => exact absurd (Finset.mem_filter.1 hx2).2 (by simp)
    | inl u2 =>
      simp only [Prod.mk.injEq] at hEq
      rcases hEq with ⟨rfl, rfl⟩
      rfl

def restrSet {H : Type} [DecidableEq H] (m : H → Bool) (G : Set (Clause (U ⊕ H))) :
    Set (Clause U) :=
  {X | ∃ C ∈ G, ¬ satBy m C ∧ X = restrClause C}

lemma restrict_derivation {H : Type} [DecidableEq H] (m : H → Bool)
    (G : Set (Clause (U ⊕ H))) (π : List (Clause (U ⊕ H))) (hπ : IsDerivation G π) :
    ∃ π' : List (Clause U),
      IsDerivation (restrSet m G) π' ∧
      π'.length ≤ π.length ∧
      ∀ C ∈ π, ¬ satBy m C → ∃ C' ∈ π', C' ⊆ restrClause C := by
  induction hπ with
  | nil =>
    exact ⟨[], .nil, by simp, fun _ h => by simp at h⟩
  | @ax π C hπ hC ih =>
    obtain ⟨π', hder, hlen, hcov⟩ := ih
    by_cases hsat : satBy m C
    · refine ⟨π', hder, by simp; omega, fun X hX hns => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact (hns hsat).elim
      · exact hcov X hX hns
    · refine ⟨restrClause C :: π', .ax hder ⟨C, hC, hsat, rfl⟩, by simp; omega,
        fun X hX hns => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact ⟨restrClause X, List.mem_cons_self, Finset.Subset.refl _⟩
      · obtain ⟨C', hC', hsub⟩ := hcov X hX hns
        exact ⟨C', List.mem_cons_of_mem _ hC', hsub⟩
  | @res π C D R hπ hC hD hRes ih =>
    obtain ⟨π', hder, hlen, hcov⟩ := ih
    by_cases hsatR : satBy m R
    · refine ⟨π', hder, by simp; omega, fun X hX hns => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact (hns hsatR).elim
      · exact hcov X hX hns
    · obtain ⟨v, hvC, hvD, rfl⟩ := hRes
      cases v with
      | inr b =>
        cases hmb : m b with
        | true =>
          have hnsD : ¬ satBy m D := by
            rintro ⟨l, hl, b', hb', hml⟩
            apply hsatR
            have hne : l ≠ (Sum.inr b, false) := by
              rintro rfl
              simp only [Sum.inr.injEq] at hb'
              subst hb'
              rw [hmb] at hml
              simp at hml
            exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hne, hl⟩), b', hb', hml⟩
          obtain ⟨D', hD', hsubD⟩ := hcov D hD hnsD
          refine ⟨π', hder, by simp; omega, fun X hX hns => ?_⟩
          rcases List.mem_cons.1 hX with rfl | hX
          · refine ⟨D', hD', fun l hl => ?_⟩
            have hlD := hsubD hl
            rw [mem_restrClause] at hlD ⊢
            exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨by simp, hlD⟩)
          · exact hcov X hX hns
        | false =>
          have hnsC : ¬ satBy m C := by
            rintro ⟨l, hl, b', hb', hml⟩
            apply hsatR
            have hne : l ≠ (Sum.inr b, true) := by
              rintro rfl
              simp only [Sum.inr.injEq] at hb'
              subst hb'
              rw [hmb] at hml
              simp at hml
            exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hl⟩), b', hb', hml⟩
          obtain ⟨C', hC', hsubC⟩ := hcov C hC hnsC
          refine ⟨π', hder, by simp; omega, fun X hX hns => ?_⟩
          rcases List.mem_cons.1 hX with rfl | hX
          · refine ⟨C', hC', fun l hl => ?_⟩
            have hlC := hsubC hl
            rw [mem_restrClause] at hlC ⊢
            exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨by simp, hlC⟩)
          · exact hcov X hX hns
      | inl u =>
        have hnsC : ¬ satBy m C := by
          rintro ⟨l, hl, b', hb', hml⟩
          apply hsatR
          have hne : l ≠ (Sum.inl u, true) := by rintro rfl; simp at hb'
          exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hl⟩), b', hb', hml⟩
        have hnsD : ¬ satBy m D := by
          rintro ⟨l, hl, b', hb', hml⟩
          apply hsatR
          have hne : l ≠ (Sum.inl u, false) := by rintro rfl; simp at hb'
          exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hne, hl⟩), b', hb', hml⟩
        obtain ⟨C', hC', hsubC⟩ := hcov C hC hnsC
        obtain ⟨D', hD', hsubD⟩ := hcov D hD hnsD
        have hRes' : IsResolvent (restrClause C) (restrClause D)
            (restrClause (C.erase (Sum.inl u, true) ∪ D.erase (Sum.inl u, false))) := by
          refine ⟨u, (mem_restrClause C u true).2 hvC, (mem_restrClause D u false).2 hvD, ?_⟩
          ext ⟨u', s'⟩
          simp only [mem_restrClause, Finset.mem_union, Finset.mem_erase, ne_eq, Prod.mk.injEq,
            Sum.inl.injEq]
        obtain ⟨π'', R', hder'', hkeep, hR', hsubR, hlen''⟩ :=
          res_subsumed hder hC' hD' hsubC hsubD hRes'
        refine ⟨π'', hder'', by simp; omega, fun X hX hns => ?_⟩
        rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨R', hR', hsubR⟩
        · obtain ⟨Y', hY', hsubY⟩ := hcov X hX hns
          exact ⟨Y', hkeep Y' hY', hsubY⟩

lemma restrict_refutation {H : Type} [DecidableEq H] (m : H → Bool)
    (G : Set (Clause (U ⊕ H))) (π : List (Clause (U ⊕ H))) (hπ : IsRefutation G π) :
    ∃ π' : List (Clause U),
      IsRefutation (restrSet m G) π' ∧ π'.length ≤ π.length := by
  obtain ⟨π', hder, hlen, hcov⟩ := restrict_derivation m G π hπ.1
  have hns : ¬ satBy m (∅ : Clause (U ⊕ H)) := by rintro ⟨_, hl, _⟩; simp at hl
  obtain ⟨C', hC', hsub⟩ := hcov ∅ hπ.2 hns
  have hem : restrClause (∅ : Clause (U ⊕ H)) = ∅ := by simp [restrClause]
  rw [hem, Finset.subset_empty] at hsub
  subst hsub
  exact ⟨π', ⟨hder, hC'⟩, hlen⟩

lemma append_derivation {G : Set (Clause U)} {p q : List (Clause U)}
    (hp : IsDerivation G p) (hq : IsDerivation G q) :
    IsDerivation G (q ++ p) := by
  induction hq with
  | nil => exact hp
  | ax _ hC ih => exact .ax ih hC
  | res _ hC hD hR ih =>
    exact .res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

lemma shift_refutation (A : Set (Clause U)) (D : Clause U) (ρ : List (Clause U))
    (hρ : IsRefutation A ρ) :
    ∃ (σ : List (Clause U)) (D' : Clause U),
      IsDerivation {C ∪ D | C ∈ A} σ ∧ D' ∈ σ ∧ D' ⊆ D ∧ σ.length ≤ ρ.length := by
  have hmain : ∀ (σ0 : List (Clause U)), IsDerivation A σ0 →
      ∃ σ : List (Clause U), IsDerivation {C ∪ D | C ∈ A} σ ∧ σ.length ≤ σ0.length ∧
        ∀ C ∈ σ0, ∃ C' ∈ σ, C' ⊆ C ∪ D := by
    intro σ0 hσ0
    induction hσ0 with
    | nil => exact ⟨[], .nil, by simp, fun _ h => by simp at h⟩
    | @ax π C _ hC ih =>
      obtain ⟨σ, hder, hlen, hcov⟩ := ih
      refine ⟨(C ∪ D) :: σ, .ax hder ⟨C, hC, rfl⟩, by simp; omega, fun X hX => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact ⟨X ∪ D, List.mem_cons_self, Finset.Subset.refl _⟩
      · obtain ⟨C', hC', hs⟩ := hcov X hX
        exact ⟨C', List.mem_cons_of_mem _ hC', hs⟩
    | @res π C₁ C₂ R _ h1 h2 hR ih =>
      obtain ⟨σ, hder, hlen, hcov⟩ := ih
      obtain ⟨C₁', h1', hs1⟩ := hcov C₁ h1
      obtain ⟨C₂', h2', hs2⟩ := hcov C₂ h2
      obtain ⟨v, hv1, hv2, rfl⟩ := hR
      have hResD : IsResolvent (C₁ ∪ D) (C₂ ∪ D)
          ((C₁ ∪ D).erase (v, true) ∪ (C₂ ∪ D).erase (v, false)) :=
        ⟨v, Finset.mem_union_left _ hv1, Finset.mem_union_left _ hv2, rfl⟩
      obtain ⟨σ', R', hder', hkeep, hR', hsR, hlen'⟩ :=
        res_subsumed hder h1' h2' hs1 hs2 hResD
      have hsub : (C₁ ∪ D).erase (v, true) ∪ (C₂ ∪ D).erase (v, false) ⊆
          (C₁.erase (v, true) ∪ C₂.erase (v, false)) ∪ D := by
        intro l hl
        simp only [Finset.mem_union, Finset.mem_erase] at hl ⊢
        rcases hl with ⟨hn, h | h⟩ | ⟨hn, h | h⟩
        · exact Or.inl (Or.inl ⟨hn, h⟩)
        · exact Or.inr h
        · exact Or.inl (Or.inr ⟨hn, h⟩)
        · exact Or.inr h
      refine ⟨σ', hder', by simp; omega, fun X hX => ?_⟩
      rcases List.mem_cons.1 hX with rfl | hX
      · exact ⟨R', hR', hsR.trans hsub⟩
      · obtain ⟨Y', hY', hsY⟩ := hcov X hX
        exact ⟨Y', hkeep Y' hY', hsY⟩
  obtain ⟨σ, hder, hlen, hcov⟩ := hmain ρ hρ.1
  obtain ⟨D', hD', hsub⟩ := hcov ∅ hρ.2
  rw [Finset.empty_union] at hsub
  exact ⟨σ, D', hder, hD', hsub, hlen⟩

def unionSet (A B : Set (Clause U)) : Set (Clause U) :=
  {X | ∃ C ∈ A, ∃ D ∈ B, X = C ∪ D}

lemma merge_two {A B : Set (Clause U)} {ρ₁ ρ₂ : List (Clause U)}
    (h1 : IsRefutation A ρ₁) (h2 : IsRefutation B ρ₂) :
    ∃ ρ : List (Clause U), IsRefutation (unionSet A B) ρ ∧
      ρ.length ≤ ρ₁.length * ρ₂.length := by
  have h1pos : 1 ≤ ρ₁.length := List.length_pos_of_mem h1.2
  have hmain : ∀ (σ0 : List (Clause U)), IsDerivation B σ0 →
      ∃ ρ : List (Clause U), IsDerivation (unionSet A B) ρ ∧
        ρ.length ≤ ρ₁.length * σ0.length ∧ ∀ C ∈ σ0, ∃ C' ∈ ρ, C' ⊆ C := by
    intro σ0 hσ0
    induction hσ0 with
    | nil => exact ⟨[], .nil, by simp, fun _ h => by simp at h⟩
    | @ax π D _ hD ih =>
      obtain ⟨ρ, hder, hlen, hcov⟩ := ih
      obtain ⟨σ, D', hderσ, hD', hsD, hlenσ⟩ := shift_refutation A D ρ₁ h1
      have hsubSet : {C ∪ D | C ∈ A} ⊆ unionSet A B := by
        rintro X ⟨C, hC, rfl⟩
        exact ⟨C, hC, D, hD, rfl⟩
      have hderσ' : IsDerivation (unionSet A B) σ := by
        clear hlenσ hD'
        induction hderσ with
        | nil => exact .nil
        | ax _ hC ih' => exact .ax ih' (hsubSet hC)
        | res _ hC hE hR ih' => exact .res ih' hC hE hR
      refine ⟨σ ++ ρ, append_derivation hder hderσ', ?_, fun X hX => ?_⟩
      · rw [List.length_append, List.length_cons, Nat.mul_succ]; omega
      · rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨D', List.mem_append_left _ hD', hsD⟩
        · obtain ⟨Y', hY', hsY⟩ := hcov X hX
          exact ⟨Y', List.mem_append_right _ hY', hsY⟩
    | @res π C₁ C₂ R _ hc1 hc2 hR ih =>
      obtain ⟨ρ, hder, hlen, hcov⟩ := ih
      obtain ⟨C₁', h1', hs1⟩ := hcov C₁ hc1
      obtain ⟨C₂', h2', hs2⟩ := hcov C₂ hc2
      obtain ⟨ρ', R', hder', hkeep, hR', hsR, hlen'⟩ :=
        res_subsumed hder h1' h2' hs1 hs2 hR
      refine ⟨ρ', hder', ?_, fun X hX => ?_⟩
      · rw [List.length_cons, Nat.mul_succ]; omega
      · rcases List.mem_cons.1 hX with rfl | hX
        · exact ⟨R', hR', hsR⟩
        · obtain ⟨Y', hY', hsY⟩ := hcov X hX
          exact ⟨Y', hkeep Y' hY', hsY⟩
  obtain ⟨ρ, hder, hlen, hcov⟩ := hmain ρ₂ h2.1
  obtain ⟨C', hC', hsub⟩ := hcov ∅ h2.2
  rw [Finset.subset_empty] at hsub
  subst hsub
  exact ⟨ρ, ⟨hder, hC'⟩, hlen⟩

def jointList : List (Set (Clause U)) → Set (Clause U)
  | [] => {∅}
  | [A] => A
  | A :: B :: rest => unionSet A (jointList (B :: rest))

lemma merge_list (As : List (Set (Clause U))) (S : ℕ) (hne : As ≠ [])
    (href : ∀ A ∈ As, ∃ ρ : List (Clause U), IsRefutation A ρ ∧ ρ.length ≤ S) :
    ∃ ρ : List (Clause U), IsRefutation (jointList As) ρ ∧ ρ.length ≤ S ^ As.length := by
  match As, hne, href with
  | [A], _, href =>
    obtain ⟨ρ, hρ, hlen⟩ := href A List.mem_cons_self
    exact ⟨ρ, hρ, by simpa [jointList] using hlen⟩
  | A :: B :: rest, _, href =>
    obtain ⟨ρ₁, h1, hlen1⟩ := href A List.mem_cons_self
    obtain ⟨ρ₂, h2, hlen2⟩ := merge_list (B :: rest) S (by simp)
      (fun X hX => href X (List.mem_cons_of_mem _ hX))
    obtain ⟨ρ, hρ, hlen⟩ := merge_two h1 h2
    refine ⟨ρ, hρ, ?_⟩
    calc ρ.length ≤ ρ₁.length * ρ₂.length := hlen
      _ ≤ S * S ^ (B :: rest).length := Nat.mul_le_mul hlen1 hlen2
      _ = S ^ ((B :: rest).length + 1) := (pow_succ' S _).symm
      _ = S ^ (A :: B :: rest).length := rfl

lemma jointList_mem_spec (As : List (Set (Clause U))) (hne : As ≠ []) (D : Clause U)
    (hD : D ∈ jointList As) :
    ∃ fs : Fin As.length → Clause U,
      (∀ i : Fin As.length, fs i ∈ As.get i) ∧
      D = Finset.univ.biUnion fs := by
  match As, hne, hD with
  | [A], _, hD =>
    refine ⟨fun _ => D, fun i => ?_, ?_⟩
    · fin_cases i; exact hD
    · ext x; simp
  | A :: B :: rest, _, hD =>
    obtain ⟨C, hC, E, hE, rfl⟩ := hD
    obtain ⟨fs, hfs, hEq⟩ := jointList_mem_spec (B :: rest) (by simp) E hE
    refine ⟨Fin.cons C fs, fun i => ?_, ?_⟩
    · cases i using Fin.cases with
      | zero => exact hC
      | succ i' => exact hfs i'
    · ext x
      rw [Finset.mem_union, hEq, Finset.mem_biUnion, Finset.mem_biUnion]
      constructor
      · rintro (hx | ⟨i', _, hx⟩)
        · exact ⟨0, Finset.mem_univ _, hx⟩
        · exact ⟨i'.succ, Finset.mem_univ _, hx⟩
      · rintro ⟨i, _, hx⟩
        cases i using Fin.cases with
        | zero => exact Or.inl hx
        | succ i' => exact Or.inr ⟨i', Finset.mem_univ _, hx⟩

end ResMerge

section LinKCalc

variable {V : Type} [DecidableEq V]

def negClause (P : LinTerm V) : LinKLine V :=
  P.image (fun e => ({negLinEq e} : LinTerm V))

def WidthOk (k : ℕ) (L : LinKLine V) : Prop :=
  ∀ T ∈ L, T.card ≤ k

lemma widthOk_empty (k : ℕ) : WidthOk k (∅ : LinKLine V) := fun _ h => by simp at h

lemma widthOk_union {k : ℕ} {L M : LinKLine V} (hL : WidthOk k L) (hM : WidthOk k M) :
    WidthOk k (L ∪ M) := fun T hT => (Finset.mem_union.1 hT).elim (hL T) (hM T)

lemma widthOk_subset {k : ℕ} {L M : LinKLine V} (hsub : L ⊆ M) (hM : WidthOk k M) :
    WidthOk k L := fun T hT => hM T (hsub hT)

lemma widthOk_negClause {k : ℕ} (hk : 1 ≤ k) (P : LinTerm V) : WidthOk k (negClause P) := by
  intro T hT
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.1 hT
  simpa using hk

lemma widthOk_linKOfClause {k : ℕ} (hk : 1 ≤ k) (C : Clause V) :
    WidthOk k (linKOfClause C) := by
  intro T hT
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hT
  simpa using hk

lemma negClause_empty : negClause (∅ : LinTerm V) = ∅ := by simp [negClause]

lemma negClause_insert (e : LinEq V) (P : LinTerm V) :
    negClause (insert e P) = insert ({negLinEq e} : LinTerm V) (negClause P) := by
  simp [negClause]

lemma negClause_union (P Q : LinTerm V) :
    negClause (P ∪ Q) = negClause P ∪ negClause Q := by
  simp [negClause, Finset.image_union]

abbrev LinKDer (k : ℕ) (F : Set (Clause V)) :=
  IsLinKDerivation k IsLinKWeakening (linKOfClause '' F)

def Ext (k : ℕ) (F : Set (Clause V)) (p : List (LinKLine V)) (m : ℕ) (L : LinKLine V) : Prop :=
  ∃ p' : List (LinKLine V), LinKDer k F p' ∧ (∀ X ∈ p, X ∈ p') ∧ L ∈ p' ∧
    p'.length ≤ p.length + m

lemma Ext.refl {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} {L : LinKLine V}
    (dp : LinKDer k F p) (hL : L ∈ p) : Ext k F p 0 L :=
  ⟨p, dp, fun _ h => h, hL, by omega⟩

lemma Ext.mono {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} {m₁ m₂ : ℕ} {L : LinKLine V}
    (h : Ext k F p m₁ L) (hm : m₁ ≤ m₂) : Ext k F p m₂ L := by
  obtain ⟨p', dp', keep, hL, hlen⟩ := h
  exact ⟨p', dp', keep, hL, by omega⟩

lemma Ext.bind {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} {m₁ m₂ : ℕ} {L₁ L₂ : LinKLine V}
    (h1 : Ext k F p m₁ L₁)
    (h2 : ∀ p₁, LinKDer k F p₁ → (∀ X ∈ p, X ∈ p₁) → L₁ ∈ p₁ → Ext k F p₁ m₂ L₂) :
    Ext k F p (m₁ + m₂) L₂ := by
  obtain ⟨p₁, dp₁, keep₁, hL₁, hlen₁⟩ := h1
  obtain ⟨p₂, dp₂, keep₂, hL₂, hlen₂⟩ := h2 p₁ dp₁ keep₁ hL₁
  exact ⟨p₂, dp₂, fun X hX => keep₂ X (keep₁ X hX), hL₂, by omega⟩

lemma weak_sub {L M : LinKLine V} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

lemma Ext.weak {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} (dp : LinKDer k F p)
    {L M : LinKLine V} (hL : L ∈ p) (hw : IsLinKWeakening L M) (hM : WidthOk k M) :
    Ext k F p 1 M :=
  ⟨M :: p, .weak dp hL hw hM, fun _ h => List.mem_cons_of_mem _ h, List.mem_cons_self, by simp⟩

lemma Ext.weak_sub {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} (dp : LinKDer k F p)
    {L M : LinKLine V} (hL : L ∈ p) (hsub : L ⊆ M) (hM : WidthOk k M) :
    Ext k F p 1 M :=
  Ext.weak dp hL (L_pcx_376_aux.weak_sub hsub) hM

lemma Ext.cut_single {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} (dp : LinKDer k F p)
    {L₁ L₂ R : LinKLine V} (h1 : L₁ ∈ p) (h2 : L₂ ∈ p) (e : LinEq V)
    (hsub1 : L₁.erase {e} ⊆ R) (hsub2 : L₂.erase {negLinEq e} ⊆ R) (hR : WidthOk k R) :
    Ext k F p 2 R := by
  by_cases he1 : ({e} : LinTerm V) ∈ L₁
  · by_cases he2 : ({negLinEq e} : LinTerm V) ∈ L₂
    · let C := L₁.erase {e} ∪ (L₂ \ ({e} : LinTerm V).image (fun q => ({negLinEq q} : LinTerm V)))
      have hcut : IsLinKCut L₁ L₂ C := by
        refine ⟨{e}, he1, ?_, rfl⟩
        intro q hq
        rw [Finset.mem_singleton.1 hq]
        exact he2
      have hsubC : C ⊆ R := by
        intro T hT
        rcases Finset.mem_union.1 hT with hT | hT
        · exact hsub1 hT
        · obtain ⟨hT2, hnot⟩ := Finset.mem_sdiff.1 hT
          have hne : T ≠ {negLinEq e} := fun hEq => hnot (by simp [hEq])
          exact hsub2 (Finset.mem_erase.2 ⟨hne, hT2⟩)
      have dC : LinKDer k F (C :: p) := .cut dp h1 h2 hcut (widthOk_subset hsubC hR)
      exact ⟨R :: C :: p, .weak dC List.mem_cons_self (L_pcx_376_aux.weak_sub hsubC) hR,
        fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), List.mem_cons_self, by simp⟩
    · have hsub : L₂ ⊆ R := by
        intro T hT
        exact hsub2 (Finset.mem_erase.2 ⟨fun hEq => he2 (hEq ▸ hT), hT⟩)
      exact (Ext.weak_sub dp h2 hsub hR).mono (by omega)
  · have hsub : L₁ ⊆ R := by
      intro T hT
      exact hsub1 (Finset.mem_erase.2 ⟨fun hEq => he1 (hEq ▸ hT), hT⟩)
    exact (Ext.weak_sub dp h1 hsub hR).mono (by omega)

lemma Ext.andIntro_step {k : ℕ} {F : Set (Clause V)} {p : List (LinKLine V)} (dp : LinKDer k F p)
    {L₁ L₂ R : LinKLine V} (h1 : L₁ ∈ p) (h2 : L₂ ∈ p) {T₁ T₂ : LinTerm V}
    (hT₁ : T₁ ∈ L₁) (hT₂ : T₂ ∈ L₂)
    (hsub : (L₁.erase T₁ ∪ L₂.erase T₂) ∪ {T₁ ∪ T₂} ⊆ R) (hR : WidthOk k R) :
    Ext k F p 2 R := by
  let C := (L₁.erase T₁ ∪ L₂.erase T₂) ∪ {T₁ ∪ T₂}
  have hAI : IsLinKAndIntro L₁ L₂ C := ⟨T₁, T₂, hT₁, hT₂, rfl⟩
  have dC : LinKDer k F (C :: p) := .andIntro dp h1 h2 hAI (widthOk_subset hsub hR)
  exact ⟨R :: C :: p, .weak dC List.mem_cons_self (L_pcx_376_aux.weak_sub hsub) hR,
    fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h), List.mem_cons_self, by simp⟩

lemma Ext.tautTerm {k : ℕ} (hk : 1 ≤ k) {F : Set (Clause V)} {p : List (LinKLine V)}
    (dp : LinKDer k F p) {A₀ : LinKLine V} (hA₀ : A₀ ∈ p) (Q : LinTerm V) (hQ : Q.card ≤ k) :
    Ext k F p (3 * Q.card + 1) (insert Q (negClause Q)) := by
  induction Q using Finset.induction_on generalizing p with
  | empty =>
    refine (Ext.weak dp hA₀ (fun T _ => Or.inl ⟨∅, by simp, fun a _ => linTermSat_empty a⟩) ?_).mono
      (by omega)
    intro T hT
    simp only [negClause_empty, Finset.mem_insert, Finset.notMem_empty, or_false] at hT
    subst hT; simp
  | @insert e Q' he ih =>
    have hQ'card : Q'.card ≤ k := by
      have := Finset.card_insert_of_notMem he; omega
    have h1 := ih dp hA₀ hQ'card
    have htot : 3 * Q'.card + 1 + (1 + 2) = 3 * (insert e Q').card + 1 := by
      rw [Finset.card_insert_of_notMem he]; omega
    rw [← htot]
    refine Ext.bind h1 fun p₁ dp₁ keep₁ hmem₁ => ?_
    let pairE : LinKLine V := {{e}, {negLinEq e}}
    have hpairW : WidthOk k pairE := by
      intro T hT
      simp only [pairE, Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl <;> simpa using hk
    have hweakPair : IsLinKWeakening A₀ pairE := by
      intro T _
      right
      intro x _
      by_cases hx : LinEqSat x e
      · exact ⟨e, by simp [pairE], hx⟩
      · exact ⟨negLinEq e, by simp [pairE], (linEqSat_neg_iff x e).2 hx⟩
    refine Ext.bind (Ext.weak dp₁ (keep₁ A₀ hA₀) hweakPair hpairW) fun p₂ dp₂ keep₂ hmem₂ => ?_
    have hRwidth : WidthOk k (insert (insert e Q') (negClause (insert e Q'))) := by
      intro T hT
      rw [Finset.mem_insert] at hT
      rcases hT with rfl | hT
      · exact hQ
      · exact widthOk_negClause hk _ T hT
    refine Ext.andIntro_step dp₂ (keep₂ _ hmem₁) hmem₂ (Finset.mem_insert_self Q' _)
      (Finset.mem_insert_self {e} _) ?_ hRwidth
    intro T hT
    simp only [pairE, Finset.mem_union, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton,
      negClause_insert] at hT ⊢
    rcases hT with (⟨hne, rfl | hT⟩ | ⟨hne, rfl | rfl⟩) | rfl
    · exact (hne rfl).elim
    · exact Or.inr (Or.inr hT)
    · exact (hne rfl).elim
    · exact Or.inr (Or.inl rfl)
    · left
      ext x
      simp [or_comm]

lemma PTree.path_disagree_aux (tr : PTree V) (b : Bool) :
    ∀ (P Q : LinTerm V), P ∈ tr.paths b → Q ∈ tr.paths (!b) →
      ∃ e ∈ P, negLinEq e ∈ Q := by
  induction tr with
  | leaf c =>
    intro P Q hP hQ
    cases c <;> cases b <;> simp [PTree.paths] at hP hQ
  | node e t1 t2 ih1 ih2 =>
    intro P Q hP hQ
    simp only [PTree.paths, Finset.mem_union, Finset.mem_image] at hP hQ
    rcases hP with ⟨P', hP', rfl⟩ | ⟨P', hP', rfl⟩
    · rcases hQ with ⟨Q', hQ', rfl⟩ | ⟨Q', hQ', rfl⟩
      · obtain ⟨q, hqP, hqQ⟩ := ih1 P' Q' hP' hQ'
        exact ⟨q, Finset.mem_insert_of_mem hqP, Finset.mem_insert_of_mem hqQ⟩
      · exact ⟨e, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
    · rcases hQ with ⟨Q', hQ', rfl⟩ | ⟨Q', hQ', rfl⟩
      · exact ⟨negLinEq e, Finset.mem_insert_self _ _,
          by rw [negLinEq_invol]; exact Finset.mem_insert_self _ _⟩
      · obtain ⟨q, hqP, hqQ⟩ := ih2 P' Q' hP' hQ'
        exact ⟨q, Finset.mem_insert_of_mem hqP, Finset.mem_insert_of_mem hqQ⟩

lemma Ext.elimTree {k : ℕ} (hk : 1 ≤ k) {F : Set (Clause V)} (B : LinKLine V) (hB : WidthOk k B)
    (M : ℕ) (tr : PTree V) :
    ∀ (p : List (LinKLine V)) (P₀ : LinTerm V),
      LinKDer k F p →
      (∀ (b : Bool) (Q : LinTerm V), Q ∈ tr.paths b →
        ∀ (p1 : List (LinKLine V)), LinKDer k F p1 → (∀ X ∈ p, X ∈ p1) →
          Ext k F p1 M (B ∪ negClause (P₀ ∪ Q))) →
      Ext k F p ((M + 2) * 2 ^ tr.depth - 2) (B ∪ negClause P₀) := by
  induction tr with
  | leaf c =>
    intro p P₀ dp hleaf
    have hmem : (∅ : LinTerm V) ∈ (PTree.leaf c).paths c := by simp [PTree.paths]
    have h1 := hleaf c ∅ hmem p dp (fun _ h => h)
    rw [Finset.union_empty] at h1
    exact h1.mono (by simp [PTree.depth])
  | node e t1 t2 ih1 ih2 =>
    intro p P₀ dp hleaf
    have hrec1 : Ext k F p ((M + 2) * 2 ^ t1.depth - 2) (B ∪ negClause (insert e P₀)) := by
      refine ih1 p (insert e P₀) dp fun b Q hQ p1 dp1 keep1 => ?_
      have hQ' : insert e Q ∈ (PTree.node e t1 t2).paths b :=
        Finset.mem_union_left _ (Finset.mem_image_of_mem _ hQ)
      have heq : insert e P₀ ∪ Q = P₀ ∪ insert e Q := by ext x; simp [or_left_comm, or_assoc]
      rw [heq]
      exact hleaf b (insert e Q) hQ' p1 dp1 keep1
    have htot : ((M + 2) * 2 ^ t1.depth - 2) + (((M + 2) * 2 ^ t2.depth - 2) + 2) ≤
        (M + 2) * 2 ^ (PTree.node e t1 t2).depth - 2 := by
      simp only [PTree.depth, pow_add, pow_one]
      have hle1 : 2 ^ t1.depth ≤ 2 ^ max t1.depth t2.depth :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have hle2 : 2 ^ t2.depth ≤ 2 ^ max t1.depth t2.depth :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have hpos1 : 1 ≤ 2 ^ t1.depth := Nat.one_le_two_pow
      have hpos2 : 1 ≤ 2 ^ t2.depth := Nat.one_le_two_pow
      have hm1 : 2 ≤ (M + 2) * 2 ^ t1.depth := by
        have := Nat.mul_le_mul (show 2 ≤ M + 2 by omega) hpos1; simpa using this
      have hm2 : 2 ≤ (M + 2) * 2 ^ t2.depth := by
        have := Nat.mul_le_mul (show 2 ≤ M + 2 by omega) hpos2; simpa using this
      have hm3 : (M + 2) * 2 ^ t1.depth ≤ (M + 2) * 2 ^ max t1.depth t2.depth :=
        Nat.mul_le_mul_left _ hle1
      have hm4 : (M + 2) * 2 ^ t2.depth ≤ (M + 2) * 2 ^ max t1.depth t2.depth :=
        Nat.mul_le_mul_left _ hle2
      have h2x : (M + 2) * (2 * 2 ^ max t1.depth t2.depth) =
          (M + 2) * 2 ^ max t1.depth t2.depth + (M + 2) * 2 ^ max t1.depth t2.depth := by ring
      omega
    refine (Ext.bind hrec1 fun p1 dp1 keep1 hm1 => ?_).mono htot
    have hrec2 : Ext k F p1 ((M + 2) * 2 ^ t2.depth - 2)
        (B ∪ negClause (insert (negLinEq e) P₀)) := by
      refine ih2 p1 (insert (negLinEq e) P₀) dp1 fun b Q hQ p2 dp2 keep2 => ?_
      have hQ' : insert (negLinEq e) Q ∈ (PTree.node e t1 t2).paths b :=
        Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)
      have heq : insert (negLinEq e) P₀ ∪ Q = P₀ ∪ insert (negLinEq e) Q := by
        ext x; simp [or_left_comm, or_assoc]
      rw [heq]
      exact hleaf b (insert (negLinEq e) Q) hQ' p2 dp2 (fun X hX => keep2 X (keep1 X hX))
    refine Ext.bind hrec2 fun p2 dp2 keep2 hm2 => ?_
    refine Ext.cut_single dp2 hm2 (keep2 _ hm1) e ?_ ?_
      (widthOk_union hB (widthOk_negClause hk P₀))
    · intro T hT
      simp only [Finset.mem_erase, Finset.mem_union, negClause_insert, Finset.mem_insert,
        negLinEq_invol] at hT ⊢
      rcases hT with ⟨hne, hB' | rfl | hP⟩
      · exact Or.inl hB'
      · exact (hne rfl).elim
      · exact Or.inr hP
    · intro T hT
      simp only [Finset.mem_erase, Finset.mem_union, negClause_insert, Finset.mem_insert] at hT ⊢
      rcases hT with ⟨hne, hB' | rfl | hP⟩
      · exact Or.inl hB'
      · exact (hne rfl).elim
      · exact Or.inr hP

lemma Ext.treePivot {k : ℕ} (hk : 1 ≤ k) {F : Set (Clause V)} {p : List (LinKLine V)}
    (dp : LinKDer k F p) (tr : PTree V) {B L₁ L₂ : LinKLine V} (hB : WidthOk k B)
    (h1 : L₁ ∈ p) (h2 : L₂ ∈ p)
    (hsub1 : L₁ ⊆ B ∪ tr.paths true) (hsub2 : L₂ ⊆ B ∪ tr.paths false) :
    Ext k F p (3 * 2 ^ tr.depth) B := by
  have h := Ext.elimTree hk B hB 1 tr p ∅ dp fun b Q hQ p1 dp1 keep1 => by
    rw [Finset.empty_union]
    cases b with
    | true =>
      refine Ext.weak dp1 (keep1 L₂ h2) ?_ (widthOk_union hB (widthOk_negClause hk Q))
      intro T hT
      rcases Finset.mem_union.1 (hsub2 hT) with hTB | hTQ
      · exact Or.inl ⟨T, Finset.mem_union_left _ hTB, fun _ hx => hx⟩
      · obtain ⟨e, heQ, hneT⟩ := PTree.path_disagree_aux tr true Q T hQ hTQ
        exact Or.inr fun a ha => ⟨negLinEq e,
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ heQ), ha (negLinEq e) hneT⟩
    | false =>
      refine Ext.weak dp1 (keep1 L₁ h1) ?_ (widthOk_union hB (widthOk_negClause hk Q))
      intro T hT
      rcases Finset.mem_union.1 (hsub1 hT) with hTB | hTQ
      · exact Or.inl ⟨T, Finset.mem_union_left _ hTB, fun _ hx => hx⟩
      · obtain ⟨e, heQ, hneT⟩ := PTree.path_disagree_aux tr false Q T hQ hTQ
        exact Or.inr fun a ha => ⟨negLinEq e,
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ heQ), ha (negLinEq e) hneT⟩
  rw [negClause_empty, Finset.union_empty] at h
  exact h.mono (by omega)

end LinKCalc

section MainProof

variable {V : Type} [Fintype V] [DecidableEq V]

def liftU (a : ℕ) (cl : Clause V) : Clause (V ⊕ Fin a) :=
  cl.image (fun l => (Sum.inl l.1, l.2))

def liftW (a h : ℕ) (cl : Clause V) : Clause ((V ⊕ Fin a) ⊕ Fin h) :=
  cl.image (fun l => (Sum.inl (Sum.inl l.1), l.2))

lemma restr_liftW (a h : ℕ) (cl : Clause V) :
    restrClause (liftW a h cl) = liftU a cl := by
  ext ⟨u, s⟩
  rw [mem_restrClause]
  simp only [liftW, liftU, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨l, hl, h1, rfl⟩
    exact ⟨l, hl, by simpa using h1, rfl⟩
  · rintro ⟨l, hl, h1, rfl⟩
    exact ⟨l, hl, by simp [h1], rfl⟩

lemma not_satBy_liftW {a h : ℕ} (m : Fin h → Bool) (cl : Clause V) :
    ¬ satBy m (liftW a h cl) := by
  rintro ⟨l, hl, b, hb, _⟩
  obtain ⟨l₀, _, rfl⟩ := Finset.mem_image.1 hl
  simp at hb

def litTree {a : ℕ} (trees : Fin a → PTree V) : Literal (V ⊕ Fin a) → PTree V
  | (Sum.inl v, s) => .node (({v} : Finset V), s) (.leaf true) (.leaf false)
  | (Sum.inr i, true) => trees i
  | (Sum.inr i, false) => (trees i).flip

lemma litTree_depth {a k : ℕ} (hk : 1 ≤ k) (trees : Fin a → PTree V)
    (hdepth : ∀ i, (trees i).depth ≤ k) (l : Literal (V ⊕ Fin a)) :
    (litTree trees l).depth ≤ k := by
  rcases l with ⟨v | i, s⟩
  · simpa [litTree, PTree.depth] using hk
  · cases s
    · simpa [litTree, PTree.depth_flip] using hdepth i
    · exact hdepth i

lemma litTree_eval {a : ℕ} (f : (V → Bool) → Fin a → Bool) (trees : Fin a → PTree V)
    (heval : ∀ i x, (trees i).eval x = f x i) (l : Literal (V ⊕ Fin a)) (x : V → Bool) :
    (litTree trees l).eval x = decide (Sum.elim x (f x) l.1 = l.2) := by
  rcases l with ⟨v | i, s⟩
  · simp only [litTree, PTree.eval, Sum.elim_inl, linEqSat_single_iff]
    by_cases h : x v = s <;> simp [h]
  · cases s
    · simp only [litTree, PTree.eval_flip, heval i x, Sum.elim_inr]
      by_cases hf : f x i = true
      · simp [hf]
      · rw [Bool.not_eq_true] at hf; simp [hf]
    · simp only [litTree, heval i x, Sum.elim_inr]
      by_cases hf : f x i = true
      · simp [hf]
      · rw [Bool.not_eq_true] at hf; simp [hf]

def transLit {a : ℕ} (trees : Fin a → PTree V) (l : Literal (V ⊕ Fin a)) : LinKLine V :=
  (litTree trees l).paths true

def transClause {a : ℕ} (trees : Fin a → PTree V) (C : Clause (V ⊕ Fin a)) : LinKLine V :=
  C.biUnion (transLit trees)

lemma transLit_inl {a : ℕ} (trees : Fin a → PTree V) (v : V) (s : Bool) :
    transLit trees (Sum.inl v, s) = {{(({v} : Finset V), s)}} := by
  simp [transLit, litTree, PTree.paths]

lemma transLit_inr_true {a : ℕ} (trees : Fin a → PTree V) (i : Fin a) :
    transLit trees (Sum.inr i, true) = (trees i).paths true := rfl

lemma transLit_inr_false {a : ℕ} (trees : Fin a → PTree V) (i : Fin a) :
    transLit trees (Sum.inr i, false) = (trees i).paths false := by
  simp [transLit, litTree, PTree.paths_flip]

lemma transClause_empty {a : ℕ} (trees : Fin a → PTree V) :
    transClause trees ∅ = ∅ := by
  simp [transClause]

lemma transClause_liftU {a : ℕ} (trees : Fin a → PTree V) (C : Clause V) :
    transClause trees (liftU a C) = linKOfClause C := by
  ext T
  simp only [transClause, liftU, linKOfClause, linOfClause, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hT⟩
    rw [transLit_inl, Finset.mem_singleton] at hT
    exact ⟨({l.1}, l.2), ⟨l, hl, rfl⟩, hT.symm⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨(Sum.inl l.1, l.2), ⟨l, hl, rfl⟩, ?_⟩
    rw [transLit_inl]; simp

lemma widthOk_transClause {a k : ℕ} (hk : 1 ≤ k) (trees : Fin a → PTree V)
    (hdepth : ∀ i, (trees i).depth ≤ k) (C : Clause (V ⊕ Fin a)) :
    WidthOk k (transClause trees C) := by
  intro T hT
  obtain ⟨l, _, hTl⟩ := Finset.mem_biUnion.1 hT
  exact (PTree.paths_card_le _ _ T hTl).trans (litTree_depth hk trees hdepth l)

lemma Ext.tautList {a k : ℕ} (hk : 1 ≤ k) {F : Set (Clause V)}
    (f : (V → Bool) → Fin a → Bool) (trees : Fin a → PTree V)
    (hdepth : ∀ i, (trees i).depth ≤ k) (heval : ∀ i x, (trees i).eval x = f x i)
    {A₀ B : LinKLine V} (hB : WidthOk k B) :
    ∀ (L : List (Literal (V ⊕ Fin a))) (p : List (LinKLine V)) (P : LinTerm V),
      LinKDer k F p → A₀ ∈ p →
      (∀ l ∈ L, transLit trees l ⊆ B) →
      (∀ x : V → Bool, LinTermSat x P → ∃ l ∈ L, Sum.elim x (f x) l.1 = l.2) →
      Ext k F p ((3 * k + 5) * 2 ^ (k * L.length) - 2) (B ∪ negClause P) := by
  intro L
  induction L with
  | nil =>
    intro p P dp hA₀ _ hsat
    have hweak : IsLinKWeakening A₀ (B ∪ negClause P) := by
      intro T _
      right
      intro x _
      by_contra hno
      have hxP : LinTermSat x P := by
        intro e he
        by_contra hne
        exact hno ⟨negLinEq e, Finset.mem_union_right _ (Finset.mem_image_of_mem _ he),
          (linEqSat_neg_iff x e).2 hne⟩
      obtain ⟨_, hl, _⟩ := hsat x hxP
      simp at hl
    exact (Ext.weak dp hA₀ hweak (widthOk_union hB (widthOk_negClause hk P))).mono
      (by simp only [List.length_nil, Nat.mul_zero, pow_zero, mul_one]; omega)
  | cons l L' ih =>
    intro p P dp hA₀ hsub hsat
    let tr := litTree trees l
    let M' := (3 * k + 5) * 2 ^ (k * L'.length) - 2
    have htrd : tr.depth ≤ k := litTree_depth hk trees hdepth l
    have hM'ge : 3 * k + 2 ≤ M' := by
      have hpow : 1 ≤ 2 ^ (k * L'.length) := Nat.one_le_two_pow
      have hmul1 : 3 * k + 5 ≤ (3 * k + 5) * 2 ^ (k * L'.length) := by
        simpa using Nat.mul_le_mul_left (3 * k + 5) hpow
      dsimp [M']
      omega
    have hstep := Ext.elimTree hk B hB M' tr p P dp fun b Q hQ p1 dp1 keep1 => by
      cases b with
      | true =>
        have hQB : Q ∈ B := hsub l List.mem_cons_self hQ
        have hQcard : Q.card ≤ k := hB Q hQB
        have h1 := Ext.tautTerm hk dp1 (keep1 A₀ hA₀) Q hQcard
        have h2 : Ext k F p1 (3 * Q.card + 1 + 1) (B ∪ negClause (P ∪ Q)) :=
          Ext.bind h1 fun p2 dp2 _ hmem =>
            Ext.weak_sub dp2 hmem (fun T hT => by
              rw [Finset.mem_insert] at hT
              rcases hT with rfl | hT
              · exact Finset.mem_union_left _ hQB
              · exact Finset.mem_union_right _
                  (by rw [negClause_union]; exact Finset.mem_union_right _ hT))
              (widthOk_union hB (widthOk_negClause hk (P ∪ Q)))
        exact h2.mono (by omega)
      | false =>
        refine ih p1 (P ∪ Q) dp1 (keep1 A₀ hA₀)
          (fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')) fun x hxPQ => ?_
        obtain ⟨hxP, hxQ⟩ := (linTermSat_union x P Q).1 hxPQ
        have hev : tr.eval x = false := (PTree.paths_sat_iff tr false x).1 ⟨Q, hQ, hxQ⟩
        have hne : Sum.elim x (f x) l.1 ≠ l.2 := by
          have := litTree_eval f trees heval l x
          rw [hev] at this
          simpa using this.symm
        obtain ⟨l', hl', hok⟩ := hsat x hxP
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact (hne hok).elim
        · exact ⟨l', hl', hok⟩
    refine hstep.mono ?_
    have hM'pos : 2 ≤ (3 * k + 5) * 2 ^ (k * L'.length) := by
      have hpow : 1 ≤ 2 ^ (k * L'.length) := Nat.one_le_two_pow
      have := Nat.mul_le_mul (show 2 ≤ 3 * k + 5 by omega) hpow; simpa using this
    have hadd : M' + 2 = (3 * k + 5) * 2 ^ (k * L'.length) := Nat.sub_add_cancel hM'pos
    rw [hadd]
    have hpowle : 2 ^ tr.depth ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) htrd
    have hmul : (3 * k + 5) * 2 ^ (k * L'.length) * 2 ^ tr.depth ≤
        (3 * k + 5) * 2 ^ (k * (l :: L').length) := by
      calc (3 * k + 5) * 2 ^ (k * L'.length) * 2 ^ tr.depth
          ≤ (3 * k + 5) * 2 ^ (k * L'.length) * 2 ^ k := Nat.mul_le_mul_left _ hpowle
        _ = (3 * k + 5) * (2 ^ (k * L'.length) * 2 ^ k) := Nat.mul_assoc _ _ _
        _ = (3 * k + 5) * 2 ^ (k * (l :: L').length) := by
            rw [← pow_add, List.length_cons, Nat.mul_succ]
    omega

lemma Ext.tautClause {a k : ℕ} (hk : 1 ≤ k) {F : Set (Clause V)}
    (f : (V → Bool) → Fin a → Bool) (trees : Fin a → PTree V)
    (hdepth : ∀ i, (trees i).depth ≤ k) (heval : ∀ i x, (trees i).eval x = f x i)
    {p : List (LinKLine V)} (dp : LinKDer k F p) {A₀ : LinKLine V} (hA₀ : A₀ ∈ p)
    (D : Clause (V ⊕ Fin a)) (hsat : ∀ x : V → Bool, ClauseSat (Sum.elim x (f x)) D) :
    Ext k F p ((3 * k + 5) * 2 ^ (k * D.card)) (transClause trees D) := by
  have h := Ext.tautList hk f trees hdepth heval
    (widthOk_transClause hk trees hdepth D) D.toList p ∅ dp hA₀
    (fun l hl T hT => Finset.mem_biUnion.2 ⟨l, Finset.mem_toList.1 hl, hT⟩)
    (fun x _ => by
      obtain ⟨l, hl, hok⟩ := hsat x
      exact ⟨l, Finset.mem_toList.2 hl, hok⟩)
  rw [negClause_empty, Finset.union_empty, Finset.length_toList] at h
  exact h.mono (by omega)

lemma simulate_resolution {a k r t : ℕ} (hk : 1 ≤ k) (ht : 0 < t)
    (F : Set (Clause V)) (hF : F.Nonempty)
    (f : (V → Bool) → Fin a → Bool) (trees : Fin a → PTree V)
    (hdepth : ∀ i, (trees i).depth ≤ k) (heval : ∀ i x, (trees i).eval x = f x i)
    (J : Set (Clause (V ⊕ Fin a)))
    (hJ : ∀ D ∈ J, (∃ C₀ ∈ F, liftU a C₀ ⊆ D) ∨
      (D.card ≤ r * t ∧ ∀ x : V → Bool, ClauseSat (Sum.elim x (f x)) D))
    (piJ : List (Clause (V ⊕ Fin a))) (hpiJ : IsRefutation J piJ) :
    ∃ τ : List (LinKLine V), IsLinKRefutation k F τ ∧
      τ.length ≤ 1 + piJ.length * (8 * (k + 1) * 2 ^ (k * (r + 1) * t)) := by
  obtain ⟨C₀, hC₀⟩ := hF
  let A₀ := linKOfClause C₀
  let stepCost := 8 * (k + 1) * 2 ^ (k * (r + 1) * t)
  have hstep_ax : ∀ m ≤ r * t, (3 * k + 5) * 2 ^ (k * m) ≤ stepCost := by
    intro m hm
    have h1 : 3 * k + 5 ≤ 8 * (k + 1) := by omega
    have h2 : k * m ≤ k * (r + 1) * t := by
      calc k * m ≤ k * (r * t) := Nat.mul_le_mul_left k hm
        _ = k * r * t := (Nat.mul_assoc k r t).symm
        _ ≤ k * (r + 1) * t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left k (by omega))
    exact Nat.mul_le_mul h1 (Nat.pow_le_pow_right (by omega) h2)
  have hstep_piv : 3 * 2 ^ k ≤ stepCost := by
    have h1 : 3 ≤ 8 * (k + 1) := by omega
    have h2 : k ≤ k * (r + 1) * t := by
      have hrt : 1 ≤ (r + 1) * t := Nat.mul_pos (by omega) ht
      calc k = k * 1 := (Nat.mul_one k).symm
        _ ≤ k * ((r + 1) * t) := Nat.mul_le_mul_left k hrt
        _ = k * (r + 1) * t := (Nat.mul_assoc k (r + 1) t).symm
    exact Nat.mul_le_mul h1 (Nat.pow_le_pow_right (by omega) h2)
  have hmain : ∀ (σ : List (Clause (V ⊕ Fin a))), IsDerivation J σ →
      ∃ τ : List (LinKLine V), LinKDer k F τ ∧ A₀ ∈ τ ∧
        (∀ C ∈ σ, transClause trees C ∈ τ) ∧
        τ.length ≤ 1 + σ.length * stepCost := by
    intro σ hσ
    induction hσ with
    | nil =>
      refine ⟨[A₀], .ax .nil ⟨C₀, hC₀, rfl⟩ (widthOk_linKOfClause hk C₀),
        List.mem_cons_self, fun _ h => by simp at h, by simp⟩
    | @ax σ D _ hD ih =>
      obtain ⟨τ, dτ, hA₀, hcov, hlen⟩ := ih
      have hExt : Ext k F τ stepCost (transClause trees D) := by
        rcases hJ D hD with ⟨C₁, hC₁, hsub⟩ | ⟨hcard, hsat⟩
        · have d1 : LinKDer k F (linKOfClause C₁ :: τ) :=
            .ax dτ ⟨C₁, hC₁, rfl⟩ (widthOk_linKOfClause hk C₁)
          have hsubL : linKOfClause C₁ ⊆ transClause trees D := by
            rw [← transClause_liftU trees C₁]
            intro T hT
            obtain ⟨l, hl, hTl⟩ := Finset.mem_biUnion.1 hT
            exact Finset.mem_biUnion.2 ⟨l, hsub hl, hTl⟩
          have h2 : Ext k F τ 2 (transClause trees D) :=
            ⟨transClause trees D :: linKOfClause C₁ :: τ,
              .weak d1 List.mem_cons_self (weak_sub hsubL)
                (widthOk_transClause hk trees hdepth D),
              fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h),
              List.mem_cons_self, by simp⟩
          exact h2.mono (by have : 2 ≤ 3 * 2 ^ k := by have := @Nat.one_le_two_pow k; omega
                            omega)
        · exact (Ext.tautClause hk f trees hdepth heval dτ hA₀ D hsat).mono (hstep_ax _ hcard)
      obtain ⟨τ', dτ', keep, hmem, hlen'⟩ := hExt
      refine ⟨τ', dτ', keep A₀ hA₀, fun X hX => ?_, ?_⟩
      · rcases List.mem_cons.1 hX with rfl | hX
        · exact hmem
        · exact keep _ (hcov X hX)
      · rw [List.length_cons, Nat.succ_mul]; omega
    | @res σ C D R _ hC hD hR ih =>
      obtain ⟨τ, dτ, hA₀, hcov, hlen⟩ := ih
      obtain ⟨u, _, _, rfl⟩ := hR
      let B := transClause trees (C.erase (u, true) ∪ D.erase (u, false))
      have hBw : WidthOk k B := widthOk_transClause hk trees hdepth _
      have hExt : Ext k F τ stepCost B := by
        cases u with
        | inl v =>
          have h1 : (transClause trees C).erase {({v}, true)} ⊆ B := by
            intro T hT
            obtain ⟨hne, hTC⟩ := Finset.mem_erase.1 hT
            obtain ⟨l, hl, hTl⟩ := Finset.mem_biUnion.1 hTC
            have hlne : l ≠ (Sum.inl v, true) := by
              rintro rfl
              rw [transLit_inl, Finset.mem_singleton] at hTl
              exact hne hTl
            exact Finset.mem_biUnion.2
              ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hlne, hl⟩), hTl⟩
          have h2 : (transClause trees D).erase {negLinEq ({v}, true)} ⊆ B := by
            intro T hT
            obtain ⟨hne, hTD⟩ := Finset.mem_erase.1 hT
            obtain ⟨l, hl, hTl⟩ := Finset.mem_biUnion.1 hTD
            have hlne : l ≠ (Sum.inl v, false) := by
              rintro rfl
              rw [transLit_inl, Finset.mem_singleton] at hTl
              exact hne hTl
            exact Finset.mem_biUnion.2
              ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hlne, hl⟩), hTl⟩
          exact (Ext.cut_single dτ (hcov C hC) (hcov D hD) ({v}, true) h1 h2 hBw).mono
            (by have : 2 ≤ 3 * 2 ^ k := by have := @Nat.one_le_two_pow k; omega
                omega)
        | inr i =>
          have hsub1 : transClause trees C ⊆ B ∪ (trees i).paths true := by
            intro T hT
            obtain ⟨l, hl, hTl⟩ := Finset.mem_biUnion.1 hT
            by_cases hle : l = (Sum.inr i, true)
            · subst hle
              exact Finset.mem_union_right _ hTl
            · exact Finset.mem_union_left _ (Finset.mem_biUnion.2
                ⟨l, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hle, hl⟩), hTl⟩)
          have hsub2 : transClause trees D ⊆ B ∪ (trees i).paths false := by
            intro T hT
            obtain ⟨l, hl, hTl⟩ := Finset.mem_biUnion.1 hT
            by_cases hle : l = (Sum.inr i, false)
            · subst hle
              rw [transLit_inr_false] at hTl
              exact Finset.mem_union_right _ hTl
            · exact Finset.mem_union_left _ (Finset.mem_biUnion.2
                ⟨l, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hle, hl⟩), hTl⟩)
          exact (Ext.treePivot hk dτ (trees i) hBw (hcov C hC) (hcov D hD) hsub1 hsub2).mono
            ((Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (hdepth i))).trans hstep_piv)
      obtain ⟨τ', dτ', keep, hmem, hlen'⟩ := hExt
      refine ⟨τ', dτ', keep A₀ hA₀, fun X hX => ?_, ?_⟩
      · rcases List.mem_cons.1 hX with rfl | hX
        · exact hmem
        · exact keep _ (hcov X hX)
      · rw [List.length_cons, Nat.succ_mul]; omega
  obtain ⟨τ, dτ, _, hcov, hlen⟩ := hmain piJ hpiJ.1
  have hEmpty : (∅ : LinKLine V) ∈ τ := by
    rw [← transClause_empty trees]
    exact hcov ∅ hpiJ.2
  exact ⟨τ, ⟨dτ, hEmpty⟩, hlen⟩

lemma pow_add_one_ge (s t : ℕ) (ht : 0 < t) : s ^ t + 1 ≤ (s + 1) ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    cases t with
    | zero => simp
    | succ t' =>
      have h1 := ih (by omega)
      have hexp : (s ^ (t' + 1) + 1) * (s + 1) = s ^ (t' + 1) * s + s ^ (t' + 1) + s + 1 := by ring
      calc s ^ (t' + 2) + 1 = s ^ (t' + 1) * s + 1 := by rw [pow_succ]
        _ ≤ (s ^ (t' + 1) + 1) * (s + 1) := by omega
        _ ≤ (s + 1) ^ (t' + 1) * (s + 1) := Nat.mul_le_mul_right _ h1
        _ = (s + 1) ^ (t' + 2) := (pow_succ _ _).symm

theorem main (F : Set (Clause V)) (hF : F.Nonempty) (a h t r p q : ℕ)
    (f : (V → Bool) → Fin a → Bool) (menu : Fin t → Fin h → Bool)
    (ht : 0 < t)
    (hcert : ∀ (x : V → Bool) (i : Fin a), ∃ T : LinTerm V,
      T.card ≤ (if f x i then q else p) ∧ LinTermSat x T ∧
      ∀ y : V → Bool, LinTermSat y T → f y i = f x i)
    (extra : Set (Clause ((V ⊕ Fin a) ⊕ Fin h)))
    (hwidth : ∀ D ∈ extra, (D.filter (fun l => l.1.isLeft)).card ≤ r)
    (hmenu : ∀ x : V → Bool, ∃ j : Fin t,
      Satisfies (Sum.elim (Sum.elim x (f x)) (menu j)) extra)
    (π : List (Clause ((V ⊕ Fin a) ⊕ Fin h)))
    (hπ : IsRefutation (Set.image (liftW a h) F ∪ extra) π) :
    let k := max 1 (p * q)
    ∃ τ : List (LinKLine V), IsLinKRefutation k F τ ∧
      τ.length ≤ (16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1))) ^ t := by
  intro k
  have hk : 1 ≤ k := le_max_left 1 (p * q)

  have htrees_ex : ∀ i : Fin a, ∃ tr : PTree V, tr.depth ≤ k ∧ ∀ x, tr.eval x = f x i := by
    intro i
    obtain ⟨tr, hd, hev⟩ := exists_parity_tree p q (fun x => f x i) (fun x => hcert x i)
    exact ⟨tr, hd.trans (le_max_right 1 (p * q)), hev⟩
  choose trees hdepth heval using htrees_ex

  let G := Set.image (liftW a h) F ∪ extra
  let Aj : Fin t → Set (Clause (V ⊕ Fin a)) := fun j => restrSet (menu j) G
  have hrefj : ∀ j : Fin t, ∃ ρ : List (Clause (V ⊕ Fin a)),
      IsRefutation (Aj j) ρ ∧ ρ.length ≤ π.length := fun j =>
    restrict_refutation (menu j) G π hπ
  let As : List (Set (Clause (V ⊕ Fin a))) := List.ofFn Aj
  have hAs_ne : As ≠ [] := by
    intro hnil
    have := congrArg List.length hnil
    simp [As] at this
    omega
  have hAs_ref : ∀ A ∈ As, ∃ ρ : List (Clause (V ⊕ Fin a)),
      IsRefutation A ρ ∧ ρ.length ≤ π.length := by
    intro A hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hA
    exact hrefj j

  obtain ⟨piJ, hpiJ, hpiJlen⟩ := merge_list As π.length hAs_ne hAs_ref
  have hAs_len : As.length = t := List.length_ofFn
  rw [hAs_len] at hpiJlen

  have hJ : ∀ D ∈ jointList As, (∃ C₀ ∈ F, liftU a C₀ ⊆ D) ∨
      (D.card ≤ r * t ∧ ∀ x : V → Bool, ClauseSat (Sum.elim x (f x)) D) := by
    intro D hD
    obtain ⟨fs, hfs, hDeq⟩ := jointList_mem_spec As hAs_ne D hD
    by_cases hphys : ∃ (i : Fin As.length) (C₀ : Clause V), C₀ ∈ F ∧ fs i = liftU a C₀
    · obtain ⟨i, C₀, hC₀, hfi⟩ := hphys
      left
      refine ⟨C₀, hC₀, ?_⟩
      rw [hDeq, ← hfi]
      exact Finset.subset_biUnion_of_mem fs (Finset.mem_univ i)
    · right
      have hall_extra : ∀ i : Fin As.length, ∃ E ∈ extra, ¬ satBy (menu (i.cast hAs_len)) E ∧
          fs i = restrClause E := by
        intro i
        have hi := hfs i
        have hget : As.get i = Aj (i.cast hAs_len) := by
          simp [As, List.get_eq_getElem]; rfl
        rw [hget] at hi
        obtain ⟨E, hEG, hns, hEq⟩ := hi
        rcases hEG with ⟨C₀, hC₀, rfl⟩ | hEex
        · exfalso
          rw [restr_liftW] at hEq
          exact hphys ⟨i, C₀, hC₀, hEq⟩
        · exact ⟨E, hEex, hns, hEq⟩
      constructor
      · rw [hDeq]
        calc (Finset.univ.biUnion fs).card
            ≤ ∑ i : Fin As.length, (fs i).card := Finset.card_biUnion_le
          _ ≤ ∑ _i : Fin As.length, r := by
              refine Finset.sum_le_sum fun i _ => ?_
              obtain ⟨E, hEex, _, hEq⟩ := hall_extra i
              rw [hEq, card_restrClause]
              exact hwidth E hEex
          _ = As.length * r := by simp
          _ = r * t := by rw [hAs_len, Nat.mul_comm]
      · intro x
        obtain ⟨j, hj⟩ := hmenu x
        let i : Fin As.length := j.cast hAs_len.symm
        obtain ⟨E, hEex, hns, hEq⟩ := hall_extra i
        have hsatE := hj E hEex
        obtain ⟨l, hlE, hval⟩ := hsatE
        rcases l with ⟨u | b, s⟩
        · have hlfs : (u, s) ∈ fs i := by
            rw [hEq, mem_restrClause]; exact hlE
          refine ⟨(u, s), ?_, by simpa using hval⟩
          rw [hDeq]
          exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, hlfs⟩
        · exfalso
          have hcast : i.cast hAs_len = j := by ext; rfl
          rw [hcast] at hns
          exact hns ⟨(Sum.inr b, s), hlE, b, rfl, by simpa using hval⟩

  obtain ⟨τ, hτ, hτlen⟩ := simulate_resolution hk ht F hF f trees hdepth heval (jointList As) hJ piJ hpiJ
  refine ⟨τ, hτ, ?_⟩
  let X := 8 * (k + 1) * 2 ^ (k * (r + 1) * t)
  have hXpos : 1 ≤ X := Nat.mul_pos (by omega) Nat.one_le_two_pow
  have hstep1 : τ.length ≤ (π.length + 1) ^ t * X := by
    calc τ.length ≤ 1 + piJ.length * X := hτlen
      _ ≤ 1 + π.length ^ t * X := Nat.add_le_add_left (Nat.mul_le_mul_right X hpiJlen) 1
      _ ≤ (π.length ^ t + 1) * X := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ (π.length + 1) ^ t * X := Nat.mul_le_mul_right X (pow_add_one_ge π.length t ht)
  have h8 : 8 ≤ 16 ^ t := by
    calc 8 ≤ 16 ^ 1 := by norm_num
      _ ≤ 16 ^ t := Nat.pow_le_pow_right (by omega) ht
  have hk1 : k + 1 ≤ (k + 1) ^ t := by
    calc k + 1 = (k + 1) ^ 1 := (pow_one _).symm
      _ ≤ (k + 1) ^ t := Nat.pow_le_pow_right (by omega) ht
  have hXle : X ≤ 16 ^ t * (k + 1) ^ t * (2 ^ (k * (r + 1))) ^ t := by
    dsimp [X]
    rw [pow_mul]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h8 hk1)
  calc τ.length ≤ (π.length + 1) ^ t * X := hstep1
    _ ≤ (π.length + 1) ^ t * (16 ^ t * (k + 1) ^ t * (2 ^ (k * (r + 1))) ^ t) :=
        Nat.mul_le_mul_left _ hXle
    _ = (16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1))) ^ t := by
        simp only [mul_pow]; ring

end MainProof

end PEqualNP.Outside.L_pcx_376_aux

theorem PEqualNP.Outside.L_pcx_376 : (∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)),
  F.Nonempty → ∀ (a h t r p q : ℕ) (f : (V → Bool) → Fin a → Bool)
    (menu : Fin t → Fin h → Bool),
    let W := (V ⊕ Fin a) ⊕ Fin h
    let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
      cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
    let k := max 1 (p*q)
    0 < t →
    (∀ (x : V → Bool) (i : Fin a), ∃ T : PEqualNP.ProofComplexity.LinTerm V,
      T.card ≤ (if f x i then q else p) ∧ PEqualNP.ProofComplexity.LinTermSat x T ∧
      ∀ y : V → Bool, PEqualNP.ProofComplexity.LinTermSat y T → f y i = f x i) →
    ∀ extra : Set (PEqualNP.ProofComplexity.Clause W),
      (∀ D ∈ extra, (D.filter (fun l => l.1.isLeft)).card ≤ r) →
      (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
        (Sum.elim (Sum.elim x (f x)) (menu j)) extra) →
      ∀ π : List (PEqualNP.ProofComplexity.Clause W),
        PEqualNP.ProofComplexity.IsRefutation (Set.image lift F ∪ extra) π →
        ∃ τ : List (PEqualNP.ProofComplexity.LinKLine V),
          PEqualNP.ProofComplexity.IsLinKRefutation k F τ ∧
          τ.length ≤ (16*(k+1)*(π.length+1)*2^(k*(r+1)))^t) := by
  intro V _ _ F hF a h t r p q f menu W lift k ht hcert extra hwidth hmenu π hπ
  exact PEqualNP.Outside.L_pcx_376_aux.main F hF a h t r p q f menu ht hcert extra hwidth hmenu π hπ
