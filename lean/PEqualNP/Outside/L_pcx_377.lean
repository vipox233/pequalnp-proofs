import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_377_aux
open PEqualNP.ProofComplexity PEqualNP.Expanders
namespace L376
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
  Ext.weak dp hL (L376.weak_sub hsub) hM
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
      exact ⟨R :: C :: p, .weak dC List.mem_cons_self (L376.weak_sub hsubC) hR,
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
  exact ⟨R :: C :: p, .weak dC List.mem_cons_self (L376.weak_sub hsub) hR,
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
end L376
theorem L376_main : (∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)),
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
  exact L376.main F hF a h t r p q f menu ht hcert extra hwidth hmenu π hπ
namespace C.Helpers
open PEqualNP.Expanders
def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)
def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial
def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1
end C.Helpers
namespace C.Helpers
open PEqualNP.Expanders
theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.LeftDegLe (permGraph σ) b := by
  intro i
  have hsub : (permGraph σ i).map Fin.castSuccEmb ⊆ Finset.univ.image (fun k => σ k i) := by
    intro x hx
    simp only [Finset.mem_map, permGraph, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb] at hx
    obtain ⟨j, ⟨k, hk⟩, rfl⟩ := hx
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  calc (permGraph σ i).card = ((permGraph σ i).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.image (fun k => σ k i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp
theorem permGraph_rightDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.RightDegLe (permGraph σ) b := by
  intro j
  have hsub : rightNbrs (permGraph σ) j ⊆
      Finset.univ.image (fun k => (σ k).symm j.castSucc) := by
    intro i hi
    simp only [rightNbrs, permGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [← hk]; simp⟩
  calc (rightNbrs (permGraph σ) j).card
      ≤ (Finset.univ.image (fun k => (σ k).symm j.castSucc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp
theorem permGraph_trap {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1)))
    (hT : 5 * T.card ≤ n + 1)
    (hbad : (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
    ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y := by
  set G := permGraph σ with hG
  set N := T.biUnion G with hN
  set U := uniqueNbrs G T with hU
  have he : ∑ i ∈ T, (G i).card = ∑ j ∈ N, (T.filter (fun i => j ∈ G i)).card := by
    have h1 : ∀ i ∈ T, (G i).card = ∑ j ∈ N, if j ∈ G i then 1 else 0 := by
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨i, hi, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  have hle8 : ∑ i ∈ T, (G i).card ≤ 8 * T.card := by
    have := Finset.sum_le_card_nsmul T (fun i => (G i).card) 8
      (fun i _ => permGraph_leftDegLe σ i)
    simpa [mul_comm] using this
  have hpt : ∀ j ∈ N, 2 ≤ (T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0 := by
    intro j hj
    have hpos : 0 < (T.filter (fun i => j ∈ G i)).card := by
      rw [hN, Finset.mem_biUnion] at hj
      obtain ⟨i, hi, hji⟩ := hj
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hji⟩⟩
    by_cases h1 : (T.filter (fun i => j ∈ G i)).card = 1
    · have : j ∈ U := by
        simp only [hU, uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      simp [this, h1]
    · split_ifs <;> omega
  have hsum : 2 * N.card ≤ ∑ i ∈ T, (G i).card + U.card := by
    have h2 : ∑ j ∈ N, 2 ≤ ∑ j ∈ N,
        ((T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← he] at h2
    have h3 : (N.filter (fun j => j ∈ U)).card ≤ U.card :=
      Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hNc : N.card + 1 ≤ 5 * T.card := by omega
  set Y0 := N.map Fin.castSuccEmb ∪ {Fin.last n} with hY0
  have hY0c : Y0.card ≤ 5 * T.card := by
    calc Y0.card ≤ (N.map Fin.castSuccEmb).card + ({Fin.last n} : Finset _).card :=
          Finset.card_union_le _ _
      _ = N.card + 1 := by simp
      _ ≤ 5 * T.card := hNc
  obtain ⟨Y, hY0Y, hYc⟩ := Finset.exists_superset_card_eq hY0c (by simpa using hT)
  refine ⟨Y, hYc, fun k x hx => hY0Y ?_⟩
  induction h : σ k x using Fin.lastCases with
  | last => simp [hY0]
  | cast j =>
    have hj : j ∈ N := by
      rw [hN, Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      simp only [hG, permGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, h⟩
    simp only [hY0, Finset.mem_union, Finset.mem_map, Fin.coe_castSuccEmb]
    exact Or.inl ⟨j, hj, rfl⟩
end C.Helpers
namespace C.Helpers
open Finset
theorem permCount : PermCountStmt := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, mem_filter, mem_univ, true_and] at hσ
    simp only [t, mem_filter, mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)
  have ht : t.card ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this
  have hfib : ∀ g ∈ t, (S.filter (fun σ => f σ = g)).card ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty {σ ∈ S | f σ = g} with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ ({σ ∈ S | f σ = g} : Finset _)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (mem_filter.mp σ.2).2
        have h2 : σ.1 a = σ₀ a := by
          have e := congrFun (h1.trans hσ₀g.symm) ⟨a, ha'⟩
          simpa [f] using e
        simp [Equiv.Perm.mul_apply, h2]⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [F] using this
    have := Fintype.card_le_of_injective F hF
    rw [hcardP, Fintype.card_coe] at this
    exact this
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  calc S.card ≤ (Fintype.card α - T.card).factorial * t.card := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _
end C.Helpers
namespace C.Helpers
open Finset
lemma arith_choose_le (N r : ℕ) (hr : 0 < r) : (N.choose r : ℝ) ≤ (3 * N / r) ^ r := by
  have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r N
  have h2 : (r : ℝ) ^ r / r.factorial ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
  have h3 : Real.exp r ≤ 3 ^ r := by
    have : Real.exp (r : ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
    rw [this]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hrr : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := h1
    _ = (N : ℝ) ^ r / (r : ℝ) ^ r * ((r : ℝ) ^ r / r.factorial) := by field_simp
    _ ≤ (N : ℝ) ^ r / (r : ℝ) ^ r * 3 ^ r := by gcongr; exact h2.trans h3
    _ = (3 * N / r) ^ r := by rw [div_pow, mul_pow]; ring
lemma arith_ratio_le (N t : ℕ) (ht : 1 ≤ t) (hN : 2 * t ≤ N) :
    ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ) ≤ (10 * t / N) ^ t := by
  have hnum : ((5 * t).descFactorial t : ℝ) ≤ ((5 * t : ℕ) : ℝ) ^ t := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hden0 : ((N + 1 - t : ℕ) : ℝ) ^ t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsub : (N : ℝ) / 2 ≤ ((N + 1 - t : ℕ) : ℝ) := by
    have hle : t ≤ N + 1 := by omega
    rw [Nat.cast_sub hle]
    have : (2 * t : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hden : ((N : ℝ) / 2) ^ t ≤ (N.descFactorial t : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hsub t).trans hden0
  calc ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ)
      ≤ ((5 * t : ℕ) : ℝ) ^ t / ((N : ℝ) / 2) ^ t :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (10 * t / N) ^ t := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
        ring
lemma arith_term_le (n t : ℕ) (ht : 1 ≤ t) (hts : t * 100000 ≤ n) :
    ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 ≤
      (1 / 4 : ℝ) ^ t := by
  have htpos : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hN : ((n + 1 : ℕ) : ℝ) ≥ 100000 * t := by
    have : t * 100000 ≤ n + 1 := by omega
    have h : ((t * 100000 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := arith_choose_le (n + 1) t (by omega)
  have h2 := arith_choose_le (n + 1) (5 * t) (by omega)
  have h3 := arith_ratio_le (n + 1) t ht (by omega)
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hratio0 : (0 : ℝ) ≤ ((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ) := by
    positivity
  have h5 : ((5 * t : ℕ) : ℝ) = 5 * (t : ℝ) := by push_cast; ring
  rw [h5] at h2
  have hbase : (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 = 23328000 * t ^ 2 / N ^ 2 := by
    field_simp
    ring
  have hq : (23328000 : ℝ) * t ^ 2 / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) ≤ (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 := by positivity
  calc ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ (3 * N / t) ^ t * (3 * N / (5 * t)) ^ (5 * t) * ((10 * t / N) ^ t) ^ 8 := by
        gcongr
    _ = ((3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8) ^ t := by
        rw [pow_mul (3 * N / (5 * t)) 5 t, ← pow_mul (10 * t / N) t 8, mul_comm t 8,
          pow_mul (10 * t / N) 8 t, mul_pow, mul_pow]
    _ ≤ (1 / 4 : ℝ) ^ t := by
        rw [hbase] at hq0 ⊢
        exact pow_le_pow_left₀ hq0 hq t
theorem arith : ArithStmt := by
  refine ⟨100000, 0, by norm_num, fun n _ => ?_⟩
  calc ∑ t ∈ Finset.Icc 1 (n / 100000),
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ ∑ t ∈ Finset.Icc 1 (n / 100000), (1 / 4 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Icc] at ht
        exact arith_term_le n t ht.1 ((Nat.le_div_iff_mul_le (by norm_num)).1 ht.2)
    _ = ∑ t ∈ Finset.Ico 1 (n / 100000 + 1), (1 / 4 : ℝ) ^ t := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 / 4 : ℝ) ^ 1 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ < 1 := by norm_num
end C.Helpers
namespace C.Helpers
open PEqualNP.Expanders
theorem expander_of_parts (hP : PermCountStmt) (hA : ArithStmt)
    (hL : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.LeftDegLe (permGraph σ) b)
    (hR : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.RightDegLe (permGraph σ) b)
    (hT : ∀ {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1))),
      5 * T.card ≤ n + 1 →
      (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card →
      ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y) :
    ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
        PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 := by
  classical
  obtain ⟨s₀, n₀, h5, hsum⟩ := hA
  refine ⟨8, s₀, n₀, by omega, ?_⟩
  intro n hn
  have hs1 := hsum n hn
  have hsn : 5 * (n / s₀) ≤ n := by
    have h1 := Nat.div_mul_le_self n s₀
    have h2 : 5 * (n / s₀) ≤ n / s₀ * s₀ := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (n / s₀) h5
    omega
  set s := n / s₀ with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, hL σ, hR σ, hσ⟩
  by_contra hno
  push Not at hno
  let A : Finset (Fin (n + 1)) → Finset (Fin (n + 1)) → Finset (Equiv.Perm (Fin (n + 1))) :=
    fun T Y => Finset.univ.filter (fun τ => ∀ x ∈ T, τ x ∈ Y)
  let U : Finset (Fin 8 → Equiv.Perm (Fin (n + 1))) :=
    (Finset.Icc 1 s).biUnion (fun t =>
      (Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun T =>
        (Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun Y =>
          Fintype.piFinset (fun _ : Fin 8 => A T Y))))
  have hsub : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))) ⊆ U := by
    intro σ _
    have hbad := hno σ
    unfold IsBdryExpander at hbad
    push Not at hbad
    obtain ⟨T, hTs, hTlt⟩ := hbad
    have ht1 : 1 ≤ T.card := by
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · rw [h0] at hTlt; omega
      · exact h0
    obtain ⟨Y, hYc, hY⟩ := hT σ T (by omega) hTlt
    simp only [U, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Fintype.mem_piFinset]
    refine ⟨T.card, ⟨ht1, hTs⟩, T, ⟨Finset.subset_univ _, rfl⟩, Y,
      ⟨Finset.subset_univ _, hYc⟩, ?_⟩
    intro k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun x hx => hY k x hx
  have hAcard : ∀ t, ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
      ∀ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
      (A T Y).card ≤ (5 * t).descFactorial t * (n + 1 - t).factorial := by
    intro t T hT' Y hY'
    rw [Finset.mem_powersetCard] at hT' hY'
    have h := hP (Fin (n + 1)) T Y
    rw [hT'.2, hY'.2, Fintype.card_fin] at h
    convert h
  have hUcard : U.card ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t * ((n + 1).choose (5 * t) *
      ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
          (n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
          apply Finset.sum_le_sum
          intro T hT'
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
                ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
                apply Finset.sum_le_sum
                intro Y hY'
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                exact Nat.pow_le_pow_left (hAcard t T hT' Y hY') 8
            _ = _ := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  have hcardΩ : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))).card =
      ((n + 1).factorial) ^ 8 := by
    rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  have hle : ((n + 1).factorial) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t *
      ((n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) :=
    hcardΩ ▸ (Finset.card_le_card hsub).trans hUcard
  have hleR : (((n + 1).factorial : ℕ) : ℝ) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) := by
    exact_mod_cast hle
  have hid : ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) =
      (((n + 1).factorial : ℕ) : ℝ) ^ 8 * ∑ t ∈ Finset.Icc 1 s,
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htn : t ≤ n + 1 := by omega
    have hEF : ((n + 1 - t).factorial : ℝ) * ((n + 1).descFactorial t : ℝ) =
        (((n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial htn
    have hE : ((n + 1).descFactorial t : ℝ) ≠ 0 := by
      have : (n + 1).descFactorial t ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    rw [← hEF]
    field_simp
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) ^ 8 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  have hlt := mul_lt_mul_of_pos_left hs1 hpos
  rw [hid] at hleR
  linarith
end C.Helpers
namespace C
theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)
end C
namespace C.PhpFinal
open PEqualNP.ProofComplexity PEqualNP.Expanders
theorem card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ m * b := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter (fun e : Fin m × Fin N => e.2 ∈ G e.1)).filter
        (fun e => e.1 = i)).card ≤ b := by
    intro i _
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hb i)
    · intro e he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have h1 := (Finset.mem_filter.mp he'.1).2
      rw [he'.2] at h1
      exact Finset.mem_coe.mpr h1
    · intro e he e' he' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
      exact Prod.ext (h1.trans h2.symm) h
  calc _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum hfib
    _ = m * b := by simp
theorem graphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ graphPHP G, C.card ≤ max b 2 := by
  classical
  intro C hC
  rcases hC with ⟨i, rfl⟩ | ⟨e, e', -, -, rfl⟩
  · refine le_trans (le_trans
      (Finset.card_le_card_of_injOn (fun l : Literal (GEdge G) => l.1.1.2) ?_ ?_) (hb i))
      (le_max_left _ _)
    · intro l hl
      have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h1 : l.1.1.2 ∈ G l.1.1.1 := l.1.2
      rw [hl'.1] at h1
      exact Finset.mem_coe.mpr h1
    · intro l hl l' hl' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
      exact Prod.ext (Subtype.ext (Prod.ext (h1.1.trans h2.1.symm) h)) (h1.2.trans h2.2.symm)
  · exact le_trans Finset.card_le_two (le_max_right _ _)
end C.PhpFinal
namespace C.Helpers
open MvPolynomial
variable {σ τ : Type}
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)
theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]
theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this
theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)
theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this
theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide
theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega
end C.Helpers
namespace C.Helpers
open MvPolynomial
theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by
  have hsum : ∀ (v : σ) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ a ∈ s, a.degree + 1 ≤ D) →
      R (X v * ∑ a ∈ s, c a • monomial a 1) =
        R (X v * R (∑ a ∈ s, c a • monomial a 1)) := by
    intro v s c hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
    exact Finset.sum_congr rfl fun a ha => by rw [hmul v a (hs a ha)]
  have key : ∀ {p : MvPolynomial σ (ZMod 2)}, PCDerivable F D p → R p = 0 := by
    intro p h
    induction h with
    | ax hp hdeg => exact hax _ hp hdeg
    | zero => exact map_zero R
    | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
    | @mulX j p _ hdeg ih =>
      by_cases hp0 : p = 0
      · rw [hp0, mul_zero, map_zero]
      · have hdeg' : p.totalDegree + 1 ≤ D := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X] at hdeg
          omega
        have hp : p = ∑ a ∈ p.support, p.coeff a • monomial a (1 : ZMod 2) := by
          conv_lhs => rw [p.as_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
        have hs : ∀ a ∈ p.support, a.degree + 1 ≤ D := by
          intro a ha
          have h1 : a.degree ≤ p.totalDegree := le_totalDegree ha
          omega
        have h2 := hsum j p.support (fun a => p.coeff a) hs
        rw [← hp, ih, mul_zero, map_zero] at h2
        exact h2
  intro href
  exact hone (key href)
end C.Helpers
namespace C.Helpers
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1
noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap
theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl
def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)
def pigeonClause (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)
theorem locIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') : locIdeal G S ≤ locIdeal G S' := by
  intro f hf
  rw [mem_locIdeal] at hf ⊢
  exact fun α hα => hf α ⟨hα.1, fun i hi => hα.2 i (h hi)⟩
theorem X_mul_mem_locIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) : X v * f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]
theorem bool_mem_locIdeal (S : Finset (Fin m)) (v : GEdge G) :
    X v * X v + X v ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α _
  have h : ∀ x : ZMod 2, x * x + x = 0 := by decide
  simpa using h (α v)
theorem hole_mem_locIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.2 = e'.1.2) (h2 : e.1.1 ≠ e'.1.1) : X e * X e' ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  simpa using hα.1 e e' h1 h2
theorem pigeon_mem_locIdeal {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    clausePoly (pigeonClause G i) ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  obtain ⟨e, he, hαe⟩ := hα.2 i hi
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [clausePoly, map_prod]
  refine Finset.prod_eq_zero (i := ((e, true) : Literal (GEdge G))) ?_ ?_
  · simp [pigeonClause, he]
  · simp [hαe, h2]
theorem one_not_mem_locIdeal_empty : (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ locIdeal G ∅ := by
  rw [mem_locIdeal]
  intro h
  have h0 := h (fun _ => 0) ⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩
  rw [map_one] at h0
  exact one_ne_zero h0
theorem card_monoHoles_le (a : GEdge G →₀ ℕ) : (monoHoles G a).card ≤ a.degree := by
  refine Finset.card_image_le.trans ?_
  rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]
theorem localSat_card_pigeonClause (i : Fin m) : (pigeonClause G i).card = (G i).card := by
  refine Finset.card_bij (fun l _ => l.1.1.2) ?_ ?_ ?_
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2.1
    have := l.1.2
    rwa [h] at this
  · rintro ⟨⟨⟨p, j⟩, hpj⟩, b⟩ hl ⟨⟨⟨p', j'⟩, hpj'⟩, b'⟩ hl' hjj
    have h := (Finset.mem_filter.mp hl).2
    have h' := (Finset.mem_filter.mp hl').2
    simp only at h h' hjj
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    subst hjj
    rfl
  · intro j hj
    exact ⟨((⟨(i, j), hj⟩ : GEdge G), true), by simp [pigeonClause], rfl⟩
theorem totalDegree_pigeonClause (i : Fin m) :
    (clausePoly (pigeonClause G i)).totalDegree = (G i).card := by
  classical
  have hdeg : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 1 := by
    intro v
    rw [totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_X]; exact Nat.zero_lt_one), totalDegree_X]
  have hne : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)) ≠ 0 := by
    intro v h0
    have := hdeg v
    rw [h0, totalDegree_zero] at this
    exact Nat.zero_ne_one this
  rw [localSat_clausePoly_pigeonClause, ← localSat_card_pigeonClause]
  generalize pigeonClause G i = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (hne _) (Finset.prod_ne_zero_iff.mpr fun l _ => hne _),
      ih, hdeg, add_comm]
theorem monoHoles_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoHoles G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  have := l.1.2
  rwa [h] at this
theorem cnfSystem_graphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (graphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    ∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · refine Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩)
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp
end C.Helpers
namespace C.Helpers
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0
noncomputable def funLocIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : funLocalSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap
theorem mem_funLocIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ funLocIdeal G S ↔ ∀ α, funLocalSat G S α → eval α f = 0 := by
  simp only [funLocIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl
theorem locIdeal_le_funLocIdeal (S : Finset (Fin m)) : locIdeal G S ≤ funLocIdeal G S := by
  intro f hf
  rw [mem_locIdeal] at hf
  rw [mem_funLocIdeal]
  exact fun α hα => hf α hα.1
theorem funLocIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') :
    funLocIdeal G S ≤ funLocIdeal G S' := by
  intro f hf
  rw [mem_funLocIdeal] at hf ⊢
  exact fun α hα => hf α ⟨⟨hα.1.1, fun i hi => hα.1.2 i (h hi)⟩, hα.2⟩
theorem X_mul_mem_funLocIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    X v * f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]
theorem fun_mem_funLocIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.1 = e'.1.1) (h2 : e.1.2 ≠ e'.1.2) : X e * X e' ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal]
  intro α hα
  simpa using hα.2 e e' h1 h2
theorem one_not_mem_funLocIdeal_empty :
    (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ funLocIdeal G ∅ := by
  rw [mem_funLocIdeal]
  intro h
  have h0 := h (fun _ => 0)
    ⟨⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩, fun _ _ _ _ => mul_zero _⟩
  rw [map_one] at h0
  exact one_ne_zero h0
def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)
def monoNbrs (a : GEdge G →₀ ℕ) : Finset (Fin N) := (monoPigeons G a).biUnion G
theorem card_monoNbrs_le {d : ℕ} (hd : LeftDegLe G d) (a : GEdge G →₀ ℕ) :
    (monoNbrs G a).card ≤ d * a.degree := by
  have h1 : (monoNbrs G a).card ≤ (monoPigeons G a).card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hd i
  have h2 : (monoPigeons G a).card ≤ a.degree := by
    refine Finset.card_image_le.trans ?_
    rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  calc (monoNbrs G a).card ≤ (monoPigeons G a).card * d := h1
    _ ≤ a.degree * d := Nat.mul_le_mul_right d h2
    _ = d * a.degree := Nat.mul_comm _ _
theorem monoNbrs_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoNbrs G (a + Finsupp.single v 1) = monoNbrs G a ∪ G v.1.1 := by
  ext j
  simp only [monoNbrs, monoPigeons, Finset.mem_biUnion, Finset.mem_image, Finset.mem_union,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hj⟩
    by_cases hev : e = v
    · exact Or.inr (hev ▸ hj)
    · refine Or.inl ⟨e.1.1, ⟨e, ?_, rfl⟩, hj⟩
      rwa [Finsupp.single_apply, ite_eq_right (Ne.symm hev), add_zero] at he
  · rintro (⟨i, ⟨e, he, rfl⟩, hj⟩ | hj)
    · exact ⟨e.1.1, ⟨e, fun h0 => he (Nat.eq_zero_of_add_eq_zero_right h0), rfl⟩, hj⟩
    · exact ⟨v.1.1, ⟨v, by rw [Finsupp.single_eq_same]; omega, rfl⟩, hj⟩
theorem monoNbrs_subset_of_monoPigeons {a b : GEdge G →₀ ℕ} {S : Finset (Fin m)}
    (h : monoPigeons G b ⊆ monoPigeons G a ∪ S) :
    monoNbrs G b ⊆ monoNbrs G a ∪ S.biUnion G := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  rcases Finset.mem_union.mp (h hi) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
theorem monoNbrs_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoNbrs G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨i', hi', hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  rwa [h] at hji
theorem cnfSystem_funGraphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    (∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e') ∨
    ∃ e e' : GEdge G, e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with hC | ⟨e, e', h1, h2, rfl⟩
    · rcases cnfSystem_graphPHP_cases G (Or.inr ⟨C, hC, rfl⟩) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩))
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp
end C.Helpers
namespace C.Helpers
open MvPolynomial
variable {σ : Type} [Countable σ]
noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)
def MonoLt (b a : σ →₀ ℕ) : Prop := monoKey b < monoKey a
theorem monoKey_injective : Function.Injective (monoKey (σ := σ)) := by
  intro a b h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [monoKey, ofLex_toLex] at h2
  exact Classical.choose_spec (Countable.exists_injective_nat (σ →₀ ℕ)) h2
theorem monoLt_of_degree_lt {a b : σ →₀ ℕ} (h : b.degree < a.degree) : MonoLt b a := by
  unfold MonoLt monoKey
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)
theorem degree_le_of_monoLt {a b : σ →₀ ℕ} (h : MonoLt b a) : b.degree ≤ a.degree := by
  unfold MonoLt monoKey at h
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le
theorem monoLt_wellFounded : WellFounded (MonoLt (σ := σ)) :=
  InvImage.wf monoKey wellFounded_lt
theorem monoLt_trans {a b c : σ →₀ ℕ} (h1 : MonoLt a b) (h2 : MonoLt b c) : MonoLt a c :=
  lt_trans (α := ℕ ×ₗ ℕ) h1 h2
def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}
noncomputable def echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {a | IsStd U a}
omit [Countable σ] in
theorem echelon_restrictSupport_le {s : Set (σ →₀ ℕ)}
    {P : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    (h : ∀ b ∈ s, monomial b (1 : ZMod 2) ∈ P) : restrictSupport (ZMod 2) s ≤ P := by
  rw [restrictSupport_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb
theorem echelon_disjoint (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Disjoint (echelonStd U) U := by
  classical
  rw [Submodule.disjoint_def]
  intro h hS hU
  by_contra hne
  have hsupp : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image h.support monoKey hsupp
  have hstd : IsStd U a := ((mem_restrictSupport_iff (R := ZMod 2)).1 hS) ha
  apply hstd
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hc : h.coeff a = 1 := key _ (mem_support_iff.1 ha)
  have hw : h - monomial a 1 ∈ restrictSupport (ZMod 2) {b | MonoLt b a} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    have hb' : (h - monomial a 1).coeff b ≠ 0 := mem_support_iff.1 hb
    rw [coeff_sub, coeff_monomial] at hb'
    by_cases hab : a = b
    · subst hab
      simp [hc] at hb'
    · rw [if_neg hab, sub_zero] at hb'
      have hbS : b ∈ h.support := mem_support_iff.2 hb'
      exact lt_of_le_of_ne (hmax b hbS) (fun e => hab (monoKey_injective e).symm)
  have heq : monomial a (1 : ZMod 2) = h - (h - monomial a 1) := (sub_sub_cancel _ _).symm
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hU) (Submodule.mem_sup_right hw)
theorem echelon_monomial_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) :
    monomial a (1 : ZMod 2) ∈
      U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
  induction a using (monoLt_wellFounded (σ := σ)).induction
  rename_i a ih
  by_cases hs : IsStd U a
  · apply Submodule.mem_sup_right
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl hs)
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  · have hmem : monomial a (1 : ZMod 2) ∈ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} :=
      Classical.byContradiction fun h => hs h
    have hle : U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} ≤
        U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
      refine sup_le le_sup_left ?_
      refine echelon_restrictSupport_le ?_
      intro b hb
      refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
        (ih b hb)
      intro c hc
      rcases hc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr (monoLt_trans hc hb)
    exact hle hmem
theorem echelon_le_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s) :
    restrictSupport (ZMod 2) s ≤ U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) s) := by
  refine echelon_restrictSupport_le ?_
  intro a ha
  refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
    (echelon_monomial_mem U a)
  intro b hb
  rcases hb with hb | hb
  · rw [hb]; exact ha
  · exact hs a ha b hb
theorem echelon_isCompl (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    IsCompl (echelonStd U) U := by
  refine ⟨echelon_disjoint U, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro f _
  have hf : f ∈ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ)) := by
    rw [mem_restrictSupport_iff]
    exact Set.subset_univ _
  have h := echelon_le_of_downClosed U (s := Set.univ) (fun _ _ _ _ => trivial) hf
  have hle : U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ))) ≤
      echelonStd U ⊔ U :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  exact hle h
noncomputable def nf (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Submodule.projection (echelonStd U) U (echelon_isCompl U)
theorem nf_mem_echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f ∈ echelonStd U :=
  Submodule.projection_apply_mem (echelon_isCompl U) f
theorem nf_sub_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : f - nf U f ∈ U :=
  Submodule.sub_projection_mem (echelon_isCompl U) f
theorem nf_support_isStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : ∀ a ∈ (nf U f).support, IsStd U a :=
  fun _ ha => ((mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_echelonStd U f)) ha
theorem nf_unique (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {f g : MvPolynomial σ (ZMod 2)} (hg : ∀ a ∈ g.support, IsStd U a) (hfg : f - g ∈ U) :
    nf U f = g := by
  have hgS : g ∈ echelonStd U := (mem_restrictSupport_iff (R := ZMod 2)).2 fun a ha => hg a ha
  have h1 : nf U f - g ∈ echelonStd U := Submodule.sub_mem _ (nf_mem_echelonStd U f) hgS
  have h2 : nf U f - g ∈ U := by
    have h3 := Submodule.sub_mem _ hfg (nf_sub_mem U f)
    rwa [sub_sub_sub_cancel_left] at h3
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (echelon_disjoint U)) _ h1 h2)
theorem nf_eq_zero_iff (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f = 0 ↔ f ∈ U := by
  constructor
  · intro h
    have h3 := nf_sub_mem U f
    rwa [h, sub_zero] at h3
  · intro h
    exact nf_unique U (by simp) (by rwa [sub_zero])
theorem nf_mem_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s)
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ restrictSupport (ZMod 2) s) :
    nf U f ∈ restrictSupport (ZMod 2) s := by
  obtain ⟨u, hu, g, hg, hug⟩ := Submodule.mem_sup.1 (echelon_le_of_downClosed U hs hf)
  have hgs := Submodule.mem_inf.1 hg
  have hnf : nf U f = g := by
    refine nf_unique U (fun c hc => (mem_restrictSupport_iff (R := ZMod 2)).1 hgs.1 hc) ?_
    rw [← hug, add_sub_cancel_right]
    exact hu
  rw [hnf]
  exact hgs.2
theorem nf_monomial_support (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) : ∀ b ∈ (nf U (monomial a 1)).support, b = a ∨ MonoLt b a := by
  have hd : ∀ c ∈ {b | b = a ∨ MonoLt b a}, ∀ b, MonoLt b c → b ∈ {b | b = a ∨ MonoLt b a} := by
    intro c hc b hb
    rcases hc with hc | hc
    · rw [hc] at hb
      exact Or.inr hb
    · exact Or.inr (monoLt_trans hb hc)
  have hm : monomial a (1 : ZMod 2) ∈ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a} :=
    (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  intro b hb
  exact (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hm) hb
omit [Countable σ] in
theorem echelon_sum_eq_degree (b : σ →₀ ℕ) : (b.sum fun _ e => e) = b.degree := by
  rw [Finsupp.degree_apply]
  rfl
theorem totalDegree_nf_le (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : (nf U f).totalDegree ≤ f.totalDegree := by
  have hd : ∀ c ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree}, ∀ b, MonoLt b c →
      b ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} :=
    fun _ hc _ hb => le_trans (degree_le_of_monoLt hb) hc
  have hf : f ∈ restrictSupport (ZMod 2) {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    exact (echelon_sum_eq_degree b).symm.trans_le (le_totalDegree hb)
  have hg := (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hf)
  unfold totalDegree
  exact Finset.sup_le fun b hb => (echelon_sum_eq_degree b).trans_le (hg hb)
end C.Helpers
namespace C.Helpers
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H
open Classical in
noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)
open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]
def SuppClosed (s : ℕ) (K : Finset (Fin N)) (S : Finset (Fin m)) : Prop :=
  ∀ T : Finset (Fin m), S ⊂ T → T.card ≤ s → ¬ uniqueNbrs G T ⊆ K ∪ S.biUnion G
lemma mem_uniqueNbrs {T : Finset (Fin m)} {j : Fin N} :
    j ∈ uniqueNbrs G T ↔ (T.filter (fun i => j ∈ G i)).card = 1 := by
  simp [uniqueNbrs]
theorem uniqueNbrs_union_subset (A B : Finset (Fin m)) :
    uniqueNbrs G (A ∪ B) ⊆ uniqueNbrs G A ∪ uniqueNbrs G B := by
  intro j hj
  rw [mem_uniqueNbrs, Finset.filter_union] at hj
  rw [Finset.mem_union, mem_uniqueNbrs, mem_uniqueNbrs]
  by_cases hA : (A.filter (fun i => j ∈ G i)).card = 0
  · right
    rw [Finset.card_eq_zero] at hA
    rw [hA, Finset.empty_union] at hj
    exact hj
  · left
    have h1 : (A.filter (fun i => j ∈ G i)).card ≤ 1 :=
      hj ▸ Finset.card_le_card Finset.subset_union_left
    omega
lemma two_mul_card_le_of_containedIn {s : ℕ} (hG : IsBdryExpander G s 2)
    {H : Finset (Fin N)} {T : Finset (Fin m)} (hT : ContainedIn G s H T) :
    2 * T.card ≤ H.card :=
  (hG T hT.1).trans (Finset.card_le_card hT.2)
lemma containedIn_union {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) {A B : Finset (Fin m)} (hA : ContainedIn G s H A)
    (hB : ContainedIn G s H B) : ContainedIn G s H (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · have h1 := two_mul_card_le_of_containedIn G hG hA
    have h2 := two_mul_card_le_of_containedIn G hG hB
    have h3 := Finset.card_union_le A B
    omega
  · exact (uniqueNbrs_union_subset G A B).trans (Finset.union_subset hA.2 hB.2)
lemma containedIn_empty (s : ℕ) (H : Finset (Fin N)) :
    ContainedIn G s H (∅ : Finset (Fin m)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [uniqueNbrs] at hj
theorem supp_containedIn {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : ContainedIn G s H (supp G s H) := by
  have key : ∀ U : Finset (Fin m), U ⊆ supp G s H →
      ∃ T, U ⊆ T ∧ T ⊆ supp G s H ∧ ContainedIn G s H T := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _, containedIn_empty G s H⟩
    | insert i U _ ih =>
      intro hU
      obtain ⟨T, hUT, hTS, hT⟩ := ih ((Finset.subset_insert i U).trans hU)
      have hi : i ∈ supp G s H := hU (Finset.mem_insert_self i U)
      obtain ⟨Ti, hiTi, hTi⟩ := (mem_supp G).mp hi
      have hTiS : Ti ⊆ supp G s H := fun k hk =>
        (mem_supp G).mpr ⟨Ti, hk, hTi⟩
      refine ⟨Ti ∪ T, ?_, Finset.union_subset hTiS hTS, containedIn_union G hG hH hTi hT⟩
      exact Finset.insert_subset (Finset.mem_union_left _ hiTi)
        (hUT.trans Finset.subset_union_right)
  obtain ⟨T, h1, h2, hT⟩ := key (supp G s H) (Finset.Subset.refl _)
  rw [← Finset.Subset.antisymm h2 h1]
  exact hT
theorem two_mul_card_supp_le {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : 2 * (supp G s H).card ≤ H.card :=
  two_mul_card_le_of_containedIn G hG (supp_containedIn G hG hH)
lemma mem_uniqueNbrs_of_subset {S T : Finset (Fin m)} (hST : S ⊆ T) {j : Fin N}
    (hj : j ∈ uniqueNbrs G T) (hjS : j ∈ S.biUnion G) : j ∈ uniqueNbrs G S := by
  rw [mem_uniqueNbrs] at hj ⊢
  obtain ⟨i, hiS, hji⟩ := Finset.mem_biUnion.mp hjS
  have h1 : (S.filter (fun i => j ∈ G i)).card ≤ 1 :=
    hj ▸ Finset.card_le_card (Finset.filter_subset_filter _ hST)
  have h2 : 0 < (S.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hji⟩⟩
  omega
theorem suppClosed_supp {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : SuppClosed G s H (supp G s H) := by
  intro T hST hT hsub
  have hS := supp_containedIn G hG hH
  have hTH : uniqueNbrs G T ⊆ H := by
    intro j hj
    rcases Finset.mem_union.mp (hsub hj) with h | h
    · exact h
    · exact hS.2 (mem_uniqueNbrs_of_subset G hST.subset hj h)
  have hTS : T ⊆ supp G s H := fun k hk =>
    (mem_supp G).mpr ⟨T, hk, hT, hTH⟩
  exact (Finset.not_subset.mp hST.2).elim fun k ⟨hkT, hkS⟩ => hkS (hTS hkT)
theorem SuppClosed.mono {s : ℕ} {K K' : Finset (Fin N)} {S : Finset (Fin m)}
    (h : SuppClosed G s K S) (hK : K' ⊆ K ∪ S.biUnion G) : SuppClosed G s K' S := by
  intro T hST hT hsub
  apply h T hST hT
  intro j hj
  rcases Finset.mem_union.mp (hsub hj) with h1 | h1
  · exact hK h1
  · exact Finset.mem_union_right _ h1
theorem SuppClosed.peel {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (h : SuppClosed G s K S) (hST : S ⊂ T) (hT : T.card ≤ s) :
    ∃ p ∈ T, p ∉ S ∧ ∃ j ∈ G p, j ∉ K ∧ j ∉ (T.erase p).biUnion G := by
  obtain ⟨j, hj, hjK⟩ := Finset.not_subset.mp (h T hST hT)
  rw [Finset.mem_union, not_or] at hjK
  obtain ⟨hjK, hjS⟩ := hjK
  rw [mem_uniqueNbrs, Finset.card_eq_one] at hj
  obtain ⟨p, hp⟩ := hj
  have hpmem : p ∈ T.filter (fun i => j ∈ G i) := hp ▸ Finset.mem_singleton_self p
  obtain ⟨hpT, hjp⟩ := Finset.mem_filter.mp hpmem
  refine ⟨p, hpT, ?_, j, hjp, hjK, ?_⟩
  · intro hpS
    exact hjS (Finset.mem_biUnion.mpr ⟨p, hpS, hjp⟩)
  · intro hj'
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj'
    obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
    have : q ∈ T.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hqT, hjq⟩
    rw [hp, Finset.mem_singleton] at this
    exact hqp this
lemma uniqueNbrs_singleton (i : Fin m) : uniqueNbrs G {i} = G i := by
  ext j
  rw [mem_uniqueNbrs]
  by_cases hj : j ∈ G i
  · simp [Finset.filter_singleton, hj]
  · simp [Finset.filter_singleton, hj]
theorem mem_supp_self {s : ℕ} (hs : 1 ≤ s) (i : Fin m) {H : Finset (Fin N)}
    (hi : G i ⊆ H) : i ∈ supp G s H :=
  (mem_supp G).mpr ⟨{i}, Finset.mem_singleton_self i,
    by simpa using hs, by rw [uniqueNbrs_singleton]; exact hi⟩
end C.Helpers
namespace C.Helpers
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]
theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]
noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)
theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega
end C.Helpers
namespace C.Helpers
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
noncomputable def funNF_zeroOut (Q : Finset (Fin m)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 ∈ Q then X e else 0
theorem funNF_zeroOut_monomial (Q : Finset (Fin m)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (funNF_zeroOut G Q) (monomial b c)
      = if monoPigeons G b ⊆ Q then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, funNF_zeroOut G Q e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [funNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxQ⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [funNF_zeroOut, ite_eq_right hxQ, zero_pow (Finsupp.mem_support_iff.mp he)]
theorem funNF_zeroOut_mem {S Q : Finset (Fin m)} (hQ : S ⊆ Q)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    bind₁ (funNF_zeroOut G Q) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have key : ∀ e e' : GEdge G, α e * α e' = 0 →
      eval α (funNF_zeroOut G Q e) * eval α (funNF_zeroOut G Q e') = 0 := by
    intro e e' h0
    by_cases h : e.1.1 ∈ Q
    · by_cases h' : e'.1.1 ∈ Q
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact h0
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [funNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    exact key e e' (hα.1.1 e e' h1 h2)
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.1.2 i hi
    have hmem : e.1.1 ∈ Q := by
      rw [he]
      exact hQ hi
    refine ⟨e, he, ?_⟩
    show eval α (funNF_zeroOut G Q e) = 1
    rw [funNF_zeroOut, ite_eq_left hmem, eval_X, h1]
  · intro e e' h1 h2
    exact key e e' (hα.2 e e' h1 h2)
theorem funNF_zeroOut_eq (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (funNF_zeroOut G Q) r
      = ∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => funNF_zeroOut_monomial G Q b _
theorem funNF_support_sum_filter (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoPigeons G b ⊆ Q) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc
theorem nf_funLocIdeal_pigeons (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support,
      monoPigeons G b ⊆ monoPigeons G a ∪ S := by
  have hsub := funNF_support_sum_filter G (monoPigeons G a ∪ S)
    (nf (funLocIdeal G S) (monomial a 1))
  have heq : nf (funLocIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
          (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
          monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (funLocIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (funLocIdeal G S) (monomial a 1) b
        (Finset.mem_filter.mp (hsub hb)).1
    · have h := funNF_zeroOut_mem G (S := S) (Q := monoPigeons G a ∪ S)
        Finset.subset_union_right (nf_sub_mem (funLocIdeal G S) (monomial a 1))
      rw [map_sub, funNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        funNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
      (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
      monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2
noncomputable def funNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else X e)
theorem funNF_override_monomial_of_notMem {p : Fin m} {j : Fin N} {b : GEdge G →₀ ℕ}
    (hp : p ∉ monoPigeons G b) (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (funNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, funNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne1 : e.1.1 ≠ p := fun h => hp (h ▸ Finset.mem_image_of_mem _ he)
    have hne2 : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [funNF_override, ite_eq_right hne1, ite_eq_right hne2]
  rw [hprod, monomial_eq]
  rfl
theorem funNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hp : p ∉ S)
    (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ funLocIdeal G (insert p S)) :
    bind₁ (funNF_override G p j) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have hval : ∀ e : GEdge G, eval α (funNF_override G p j e)
      = if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else α e) := by
    intro e
    rw [funNF_override]
    split_ifs <;> simp
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hj1 : e.1.2 = j
    · have hj2 : e'.1.2 = j := h1.symm.trans hj1
      by_cases hp1 : e.1.1 = p
      · have hp2 : ¬ e'.1.1 = p := fun h3 => h2 (hp1.trans h3.symm)
        rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
    · have hj2 : ¬ e'.1.2 = j := fun h3 => hj1 (h1.trans h3)
      by_cases hp1 : e.1.1 = p
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
      · by_cases hp2 : e'.1.1 = p
        · rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.1.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (funNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [hval, ite_eq_left rfl, ite_eq_left rfl]
    · obtain ⟨e, he, h1⟩ := hα.1.2 i h
      have hne1 : ¬ e.1.1 = p := by
        intro h3
        rw [he] at h3
        exact hp (h3 ▸ h)
      have hne2 : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (funNF_override G p j e) = 1
      rw [hval, ite_eq_right hne1, ite_eq_right hne2, h1]
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hp1 : e.1.1 = p
    · have hp2 : e'.1.1 = p := h1.symm.trans hp1
      by_cases hj1 : e.1.2 = j
      · have hj2 : ¬ e'.1.2 = j := fun h3 => h2 (hj1.trans h3.symm)
        rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
    · have hp2 : ¬ e'.1.1 = p := fun h3 => hp1 (h1.trans h3)
      by_cases hj1 : e.1.2 = j
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
      · by_cases hj2 : e'.1.2 = j
        · rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.2 e e' h1 h2
theorem funNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (funNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (funNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, (e.1.1 = p ∧ ¬ e.1.2 = j) ∨ (¬ e.1.1 = p ∧ e.1.2 = j)
  · obtain ⟨e, he, h⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [funNF_override, ite_eq_left h1, ite_eq_right h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
    · rw [funNF_override, ite_eq_right h1, ite_eq_left h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz1 : ∀ e ∈ c.support, e.1.1 = p → e.1.2 = j := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inl ⟨h, h2⟩⟩
    have hz2 : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inr ⟨h2, h⟩⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), funNF_override, ite_eq_left (hz2 e he h),
        ite_eq_left h, one_pow]
    · have hne : ¬ e.1.1 = p := fun h3 => h (hz1 e he h3)
      rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        funNF_override, ite_eq_right hne, ite_eq_right h]
theorem funNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (funNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases funNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))
theorem nf_funLocIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoNbrs G a) :
    nf (funLocIdeal G (insert p S)) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  refine nf_unique (funLocIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (funLocIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hloc := nf_funLocIdeal_pigeons G S a b hb
    have hbp : p ∉ monoPigeons G b := by
      intro h
      rcases Finset.mem_union.mp (hloc h) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨p, h', hj⟩)
      · exact hp h'
    have hbj : j ∉ monoHoles G b := by
      intro h
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp h
      have hje : j ∈ G e.1.1 := by
        rw [← hej]
        exact e.2
      rcases Finset.mem_union.mp (hloc (Finset.mem_image_of_mem _ he)) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
      · exact hjS (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
    have himg := congrArg (bind₁ (funNF_override G p j)) huw
    rw [map_add, funNF_override_monomial_of_notMem G hbp hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (funNF_override_mem G hp hj hjS hu)
      (funNF_override_mem_restrictSupport G p j hw)
  · exact funLocIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (funLocIdeal G S) (monomial a 1))
theorem nf_funLocIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoNbrs G a ⊆ K) :
    nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_funLocIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl
end C.Helpers
namespace C.Helpers
theorem monomial_one_mul_X {σ : Type} (a : σ →₀ ℕ) (v : σ) :
    MvPolynomial.monomial a (1 : ZMod 2) * MvPolynomial.X v = MvPolynomial.monomial (a + Finsupp.single v 1) 1 := by
  rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, mul_one]
theorem totalDegree_monomial_one {σ : Type} (a : σ →₀ ℕ) :
    (MvPolynomial.monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [MvPolynomial.totalDegree_monomial _ one_ne_zero]; rfl
open MvPolynomial
open PEqualNP.Expanders
variable {m N : ℕ} (G : BipGraph m N)
noncomputable def funPseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1))
theorem funPseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1)) a
  simpa only [funPseudoR, coe_basisMonomials] using h
theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji
theorem funPseudoR_monomial_eq_nf {s B : ℕ} (hG : IsBdryExpander G s 2) (hB : B ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ B) {a : GEdge G →₀ ℕ}
    (ha : (monoNbrs G a).card ≤ B)
    (haK : monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s (monomial a 1) = nf (funLocIdeal G (supp G s K)) (monomial a 1) := by
  rw [funPseudoR_monomial]
  have hH : (monoNbrs G a).card ≤ s := ha.trans hB
  have hKs : K.card ≤ s := hK.trans hB
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoNbrs G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoNbrs G a)) (supp G s K)
    omega
  have e1 := nf_funLocIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoNbrs G a))
  have e2 := nf_funLocIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoNbrs G a))
  exact e1.symm.trans e2
theorem funPseudoR_eq_nf_of_monomials {s : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)))
    {f : MvPolynomial (GEdge G) (ZMod 2)}
    (h : ∀ a ∈ f.support, funPseudoR G s (monomial a 1) = nf U (monomial a 1)) :
    funPseudoR G s f = nf U f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (funPseudoR G s), e (nf U)]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]
theorem funPseudoR_eq_nf {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) {K : Finset (Fin N)} (hK : K.card ≤ d * D)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s f = nf (funLocIdeal G (supp G s K)) f :=
  funPseudoR_eq_nf_of_monomials G _ fun a ha =>
    funPseudoR_monomial_eq_nf G hG hB hK
      ((card_monoNbrs_le G hd a).trans
        (Nat.mul_le_mul_left d ((le_totalDegree ha).trans hf))) (hfK a ha)
theorem funPseudoR_mul {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    funPseudoR G s (X v * monomial a 1)
      = funPseudoR G s (X v * funPseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoNbrs G (a + Finsupp.single v 1)).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hKa : (monoNbrs G a).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoNbrs G a ⊆ monoNbrs G (a + Finsupp.single v 1) := by
    rw [monoNbrs_add_single]
    exact Finset.subset_union_left
  have e1 : funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1)))) (monomial a 1) :=
    funPseudoR_monomial_eq_nf G hG hB hK0 hKa (haK0.trans Finset.subset_union_left)
  have e2 : funPseudoR G s (X v * monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact funPseudoR_monomial_eq_nf G hG hB hK0 hK0 Finset.subset_union_left
  have hq : (nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : funPseudoR G s
        (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1))
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine funPseudoR_eq_nf G hG hd hB hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := monoNbrs_subset_of_monoPigeons G (nf_funLocIdeal_pigeons G _ a c hc)
      rw [addRightEmbedding_apply, monoNbrs_add_single]
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
      · refine Finset.mem_union_left _ ?_
        rw [monoNbrs_add_single]
        exact Finset.mem_union_right _ hj
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1)
      ∈ funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_funLocIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0
theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem
theorem totalDegree_X_mul_X (e e' : GEdge G) :
    (X e * X e' : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
  have h : (X e * X e' : MvPolynomial (GEdge G) (ZMod 2))
      = monomial (Finsupp.single e 1 + Finsupp.single e' 1) 1 := by
    have hX : (X e : MvPolynomial (GEdge G) (ZMod 2)) = monomial (Finsupp.single e 1) 1 := rfl
    rw [hX, monomial_one_mul_X]
  rw [h, totalDegree_monomial_one, map_add, Finsupp.degree_single, Finsupp.degree_single]
theorem funPseudoR_axiom {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hs : 1 ≤ s) (hB : d * D ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) (hdeg : f.totalDegree ≤ D) : funPseudoR G s f = 0 := by
  have hcard : ∀ i, 1 ≤ D → (G i).card ≤ d * D := fun i hD =>
    (hd i).trans (Nat.le_mul_of_pos_right d hD)
  rcases cnfSystem_funGraphPHP_cases G hf with
    ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
      rw [totalDegree_add_eq_left_of_totalDegree_lt, totalDegree_X_mul_X]
      rw [totalDegree_X_mul_X, totalDegree_X]
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G v.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (bool_mem_locIdeal G _ v))
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
  · have hi : (G i).card ≤ D := by
      rw [← totalDegree_pigeonClause G i]
      exact hdeg
    have hi' : (G i).card ≤ s := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · omega
      · exact (hcard i h0).trans hB
    exact funPseudoR_eq_zero_of_mem G hG (K := G i) hi' (monoNbrs_pigeonClause G i)
      (locIdeal_le_funLocIdeal G _
        (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _))))
  · rw [totalDegree_X_mul_X] at hdeg
    have hK : (G e.1.1 ∪ G e'.1.1).card ≤ s := by
      have h3 := Finset.card_union_le (G e.1.1) (G e'.1.1)
      have h4 := hd e.1.1
      have h5 := hd e'.1.1
      have h6 : d * 2 ≤ d * D := Nat.mul_le_mul_left d hdeg
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1 ∪ G e'.1.1) hK
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (hole_mem_locIdeal G _ h1 h2))
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_left
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_right
  · rw [totalDegree_X_mul_X] at hdeg
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_) (fun_mem_funLocIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
theorem funPseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : funPseudoR G s 1 ≠ 0 := by
  have hm : monoNbrs G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoNbrs monoPigeons
    rw [Finsupp.support_zero, Finset.image_empty, Finset.biUnion_empty]
  have h0 : supp G s (monoNbrs G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : funPseudoR G s 1 = nf (funLocIdeal G ∅) 1 := by
    have h := funPseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_funLocIdeal_empty G ((nf_eq_zero_iff _ _).mp h)
theorem funGraphPHP_no_pc_refutation {s d D : ℕ} (hG : IsBdryExpander G s 2)
    (hd : LeftDegLe G d) (hs : 1 ≤ s) (hB : d * D ≤ s) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (funPseudoR G s)
    (fun _ hf hdeg => funPseudoR_axiom G hG hd hs hB hf hdeg)
    (fun v a ha => funPseudoR_mul G hG hd hB v a ha)
    (funPseudoR_one G hG)
end C.Helpers
namespace C
theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB
end C
namespace C.Helpers
open MvPolynomial PEqualNP.ProofComplexity
section Generic
variable {σ : Type}
theorem char2_add_self (x : MvPolynomial σ (ZMod 2)) : x + x = 0 :=
  CharTwo.add_self_eq_zero x
theorem totalDegree_mul_le' {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ}
    (hp : p.totalDegree ≤ a) (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hq)
theorem pcDerivable_mul_le {F : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (hp : PCDerivable F B p) (q : MvPolynomial σ (ZMod 2))
    {dq dp : ℕ} (hq : q.totalDegree ≤ dq) (hpd : p.totalDegree ≤ dp) (hB : B ≤ B')
    (hd : dq + dp ≤ B') : PCDerivable F B' (q * p) :=
  pcDerivable_mono (pcDerivable_mul_left hp q) (max_le hB (by omega)) subset_rfl
theorem totalDegree_prod_one_add_le {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) {e : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ e) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ e * s.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ u ∈ s, (1 + a u).totalDegree ≤ ∑ _u ∈ s, e := by
        refine Finset.sum_le_sum fun u hu => ?_
        refine (totalDegree_add _ _).trans ?_
        rw [totalDegree_one]
        exact max_le (Nat.zero_le _) (ha u hu)
    _ = e * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
theorem pcDerivable_prod_absorb {F : Set (MvPolynomial σ (ZMod 2))} {B e dQ : ℕ} {ι : Type}
    [DecidableEq ι] (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (Q : MvPolynomial σ (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (ha : ∀ u ∈ s, PCDerivable F B (a u * Q))
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ e)
    (hB : e * s.card + dQ ≤ B) :
    PCDerivable F B ((∏ u ∈ s, (1 + a u)) * Q + Q) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact .zero
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.mul_succ] at hB
    have h1 := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv))
      (fun v hv => hdeg v (Finset.mem_insert_of_mem hv)) (by omega)
    have h2 := pcDerivable_mul_le (ha u (Finset.mem_insert_self u s)) (∏ v ∈ s, (1 + a v))
      (totalDegree_prod_one_add_le s a fun v hv => hdeg v (Finset.mem_insert_of_mem hv))
      (totalDegree_mul_le' (hdeg u (Finset.mem_insert_self u s)) hdQ) le_rfl (by omega)
    have h3 := h1.add h2
    have hEq : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (∏ v ∈ s, (1 + a v)) * Q + Q + (∏ v ∈ s, (1 + a v)) * (a u * Q) := by
      rw [Finset.prod_insert hu]
      ring
    rw [hEq]
    exact h3
theorem sum_mul_self_add (ι : Type) [DecidableEq ι] (s : Finset ι)
    (x : ι → MvPolynomial σ (ZMod 2)) :
    (∑ v ∈ s, x v) * (∑ v ∈ s, x v) + ∑ v ∈ s, x v = ∑ v ∈ s, (x v * x v + x v) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert u s hu ih =>
    rw [Finset.sum_insert hu, Finset.sum_insert hu, ← ih]
    linear_combination char2_add_self (x u * ∑ v ∈ s, x v)
end Generic
section Blocks
variable {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ}
  {g : Fin M → Fin W → MvPolynomial V (ZMod 2)}
theorem totalDegree_rename_inl_le (p : MvPolynomial V (ZMod 2)) {d : ℕ}
    (hp : p.totalDegree ≤ d) :
    (rename (Sum.inl : V → BlockVar V h M W) p).totalDegree ≤ d :=
  (totalDegree_rename_le _ _).trans hp
theorem totalDegree_blockFactor_le (j : Fin M) (u : Fin h)
    (hg : ∀ i, (g j i).totalDegree ≤ 1) :
    (∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
      (g j i)).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun i _ => ?_
  have := totalDegree_mul_le' (a := 1) (b := 1)
    (p := (X (Sum.inr (j, u, i)) : MvPolynomial (BlockVar V h M W) (ZMod 2)))
    (q := rename Sum.inl (g j i)) (totalDegree_X _).le (totalDegree_rename_inl_le _ (hg i))
  exact this
theorem totalDegree_blockProduct_le (j : Fin M) (hg : ∀ i, (g j i).totalDegree ≤ 1) :
    (blockProduct h M W g j).totalDegree ≤ 2 * h := by
  have := totalDegree_prod_one_add_le (Finset.univ : Finset (Fin h))
    (fun u => ∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
      (g j i)) (e := 2) (fun u _ => totalDegree_blockFactor_le j u hg)
  simpa [blockProduct] using this
theorem block_transfer (j : Fin M) (hg : ∀ i, (g j i).totalDegree ≤ 1) {B dQ : ℕ}
    (Q : MvPolynomial (BlockVar V h M W) (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (hB : 2 * h + dQ ≤ B)
    (hP : PCDerivable (blockSystem F h M W g) B (blockProduct h M W g j))
    (hQ : ∀ i, PCDerivable (blockSystem F h M W g) B (rename Sum.inl (g j i) * Q)) :
    PCDerivable (blockSystem F h M W g) B Q := by
  classical
  have ha : ∀ u ∈ (Finset.univ : Finset (Fin h)), PCDerivable (blockSystem F h M W g) B
      ((∑ i : Fin W, X (Sum.inr (j, u, i)) * rename (Sum.inl : V → BlockVar V h M W)
        (g j i)) * Q) := by
    intro u _
    have hh : 1 ≤ h := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
    rw [Finset.sum_mul]
    refine pcDerivable_sum _ _ fun i _ => ?_
    rw [mul_assoc]
    exact pcDerivable_mul_le (hQ i) _ (totalDegree_X _).le
      (totalDegree_mul_le' (totalDegree_rename_inl_le _ (hg i)) hdQ) le_rfl (by omega)
  have h1 := pcDerivable_prod_absorb (Finset.univ : Finset (Fin h)) _ Q hdQ ha
    (fun u _ => totalDegree_blockFactor_le j u hg) (by simpa using hB)
  have h2 := pcDerivable_mul_le hP Q hdQ (totalDegree_blockProduct_le j hg) le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) *
      rename (Sum.inl : V → BlockVar V h M W) (g j i))) * Q + Q
      + Q * blockProduct h M W g j = Q := by
    unfold blockProduct
    linear_combination char2_add_self ((∏ u : Fin h, (1 + ∑ i : Fin W, X (Sum.inr (j, u, i)) *
      rename (Sum.inl : V → BlockVar V h M W) (g j i))) * Q)
  rw [hEq] at h3
  exact h3
end Blocks
section Clauses
variable {V : Type} [DecidableEq V]
noncomputable def eqPoly (q : LinEq V) : MvPolynomial V (ZMod 2) :=
  ∑ v ∈ q.1, X v + C (if q.2 = true then 0 else 1)
omit [DecidableEq V] in
theorem totalDegree_eqPoly_le (q : LinEq V) : (eqPoly q).totalDegree ≤ 1 := by
  unfold eqPoly
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact totalDegree_finsetSum_le fun v _ => (totalDegree_X v).le
  · rw [totalDegree_C]
    exact Nat.zero_le _
noncomputable def clauseInputs {M W : ℕ} (e : Fin W → LinEq V) (cl : Fin M → LinClause V) :
    Fin M → Fin W → MvPolynomial V (ZMod 2) :=
  fun j i => if e i ∈ cl j then eqPoly (e i) else 0
theorem totalDegree_clauseInputs_le {M W : ℕ} (e : Fin W → LinEq V)
    (cl : Fin M → LinClause V) (j : Fin M) (i : Fin W) :
    (clauseInputs e cl j i).totalDegree ≤ 1 := by
  unfold clauseInputs
  split_ifs
  · exact totalDegree_eqPoly_le _
  · simp
variable {F : Set (MvPolynomial V (ZMod 2))} {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}
theorem block_companion (he : Function.Surjective e) (j : Fin M) {q : LinEq V}
    (hq : q ∈ cl j) {B : ℕ} (hB : 2 * h + 1 ≤ B) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * blockProduct h M W (clauseInputs e cl) j) := by
  obtain ⟨i, rfl⟩ := he q
  have hgi : clauseInputs e cl j i = eqPoly (e i) := by simp [clauseInputs, hq]
  rw [← hgi]
  refine .ax (Or.inr (Or.inr ⟨j, i, rfl⟩)) ?_
  have := totalDegree_mul_le'
    (totalDegree_rename_inl_le (h := h) (M := M) (W := W) _
      (totalDegree_clauseInputs_le e cl j i))
    (totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j))
  omega
theorem clause_transfer (j : Fin M) {B dQ : ℕ}
    (Q : MvPolynomial (BlockVar V h M W) (ZMod 2)) (hdQ : Q.totalDegree ≤ dQ)
    (hB : 2 * h + dQ ≤ B)
    (hP : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j))
    (hQ : ∀ q ∈ cl j, PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * Q)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B Q := by
  refine block_transfer j (totalDegree_clauseInputs_le e cl j) Q hdQ hB hP fun i => ?_
  unfold clauseInputs
  split_ifs with hi
  · exact hQ _ hi
  · rw [map_zero, zero_mul]
    exact .zero
theorem block_weak (he : Function.Surjective e) (jC jD : Fin M) {B : ℕ}
    (hB : 4 * h + 1 ≤ B) (hh : 1 ≤ h)
    (halt : ∀ q ∈ cl jC, ∃ J : Finset (LinEq V), J ⊆ cl jD ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q))
    (hP : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jC)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jD) := by
  have hdP := totalDegree_blockProduct_le (h := h) jD (totalDegree_clauseInputs_le e cl jD)
  refine clause_transfer jC _ hdP (by omega) hP fun q hq => ?_
  obtain ⟨J, hJ, hsum⟩ := halt q hq
  have hcomp : ∀ d ∈ J, PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) :=
    fun d hd => block_companion he jD (hJ hd) (by omega)
  rcases hsum with h1 | h1
  · have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q)
          * blockProduct h M W (clauseInputs e cl) jD
        = ∑ d ∈ J, rename Sum.inl (eqPoly q) *
          (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) := by
      have := congrArg (rename (Sum.inl : V → BlockVar V h M W)) h1
      rw [map_sum, map_one] at this
      rw [← Finset.mul_sum, ← Finset.sum_mul, this, one_mul]
    rw [hEq]
    refine pcDerivable_sum _ _ fun d hd => ?_
    exact pcDerivable_mul_le (hcomp d hd) _
      (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le q))
      (totalDegree_mul_le' (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le d)) hdP)
      le_rfl (by omega)
  · have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q)
          * blockProduct h M W (clauseInputs e cl) jD
        = ∑ d ∈ J,
          (rename Sum.inl (eqPoly d) * blockProduct h M W (clauseInputs e cl) jD) := by
      rw [← h1, map_sum, Finset.sum_mul]
    rw [hEq]
    exact pcDerivable_sum _ _ hcomp
theorem block_bool (hbool : ∀ v : V, X v * X v + X v ∈ F) (q : LinEq V) {B : ℕ}
    (hB : 2 ≤ B) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly q) * rename Sum.inl (eqPoly q) + rename Sum.inl (eqPoly q)) := by
  have hc : ∀ c : ZMod 2, c * c + c = 0 := by decide
  have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q) * rename Sum.inl (eqPoly q)
        + rename Sum.inl (eqPoly q)
      = ∑ v ∈ q.1, (X (Sum.inl v) * X (Sum.inl v) + X (Sum.inl v)) := by
    rw [← sum_mul_self_add]
    simp only [eqPoly, map_add, map_sum, rename_X, rename_C]
    have hC : (C (if q.2 = true then (0 : ZMod 2) else 1) :
        MvPolynomial (BlockVar V h M W) (ZMod 2)) * C (if q.2 = true then 0 else 1)
        + C (if q.2 = true then 0 else 1) = 0 := by
      rw [← C_mul, ← C_add, hc, C_0]
    linear_combination hC + char2_add_self ((∑ v ∈ q.1, X (Sum.inl v)) *
      (C (if q.2 = true then (0 : ZMod 2) else 1) : MvPolynomial (BlockVar V h M W) (ZMod 2)))
  rw [hEq]
  refine pcDerivable_sum _ _ fun v _ => ?_
  refine .ax (Or.inl ⟨_, hbool v, by simp⟩) ?_
  refine ((totalDegree_add _ _).trans (max_le ?_ ?_)).trans hB
  · exact totalDegree_mul_le' (totalDegree_X _).le (totalDegree_X _).le
  · exact (totalDegree_X _).le.trans (by omega)
theorem block_res (he : Function.Surjective e) (hbool : ∀ v : V, X v * X v + X v ∈ F)
    (jC jD jR : Fin M) {B : ℕ} (hB : 4 * h + 1 ≤ B) (hh : 1 ≤ h)
    (hres : IsLinResolvent (cl jC) (cl jD) (cl jR))
    (hPC : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jC))
    (hPD : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jD)) :
    PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) jR) := by
  obtain ⟨f, hfC, hfD, hR⟩ := hres
  have hdP := totalDegree_blockProduct_le (h := h) jR (totalDegree_clauseInputs_le e cl jR)
  have hdu := totalDegree_rename_inl_le (h := h) (M := M) (W := W) _
    (totalDegree_eqPoly_le (f, true))
  have hu1 : rename (Sum.inl : V → BlockVar V h M W) (eqPoly (f, false))
      = rename Sum.inl (eqPoly (f, true)) + 1 := by
    simp [eqPoly]
  have hstep1 : PCDerivable (blockSystem F h M W (clauseInputs e cl)) B
      (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR) := by
    refine clause_transfer jC _ (totalDegree_mul_le' hdu hdP) (by omega) hPC fun q hq => ?_
    by_cases hqf : q = (f, false)
    · subst hqf
      have hb := block_bool (F := F) (h := h) (M := M) (W := W) (e := e) (cl := cl) hbool
        (f, true) (B := B) (by omega)
      have hm := pcDerivable_mul_le hb (blockProduct h M W (clauseInputs e cl) jR) hdP
        (dp := 2) ((totalDegree_add _ _).trans (max_le
          (totalDegree_mul_le' hdu hdu) (hdu.trans (by omega)))) le_rfl (by omega)
      rw [hu1]
      have hEq : (rename (Sum.inl : V → BlockVar V h M W) (eqPoly (f, true)) + 1) *
          (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR)
          = blockProduct h M W (clauseInputs e cl) jR *
            (rename Sum.inl (eqPoly (f, true)) * rename Sum.inl (eqPoly (f, true))
              + rename Sum.inl (eqPoly (f, true))) := by ring
      rw [hEq]
      exact hm
    · have hqR : q ∈ cl jR := by
        rw [hR]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hqf, hq⟩)
      have hc := block_companion (F := F) (h := h) he jR hqR (B := B) (by omega)
      have hm := pcDerivable_mul_le hc (rename Sum.inl (eqPoly (f, true))) hdu
        (totalDegree_mul_le' (totalDegree_rename_inl_le _ (totalDegree_eqPoly_le q)) hdP)
        le_rfl (by omega)
      have hEq : rename (Sum.inl : V → BlockVar V h M W) (eqPoly q) *
          (rename Sum.inl (eqPoly (f, true)) * blockProduct h M W (clauseInputs e cl) jR)
          = rename Sum.inl (eqPoly (f, true)) *
            (rename Sum.inl (eqPoly q) * blockProduct h M W (clauseInputs e cl) jR) := by
        ring
      rw [hEq]
      exact hm
  refine clause_transfer jD _ hdP (by omega) hPD fun q hq => ?_
  by_cases hqf : q = (f, true)
  · subst hqf
    exact hstep1
  · have hqR : q ∈ cl jR := by
      rw [hR]
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hqf, hq⟩)
    exact block_companion he jR hqR (by omega)
end Clauses
section Axioms
variable {m l h M W : ℕ} {e : Fin W → LinEq (Fin m × Fin l)}
  {cl : Fin M → LinClause (Fin m × Fin l)}
theorem block_ax (he : Function.Surjective e) (j : Fin M) {B : ℕ}
    (hB1 : 2 * h + l ≤ B) (hB2 : 2 * h + 1 ≤ B)
    (hax : cl j ∈ (fun C => linOfClause C) '' BPHP m l) :
    PCDerivable (blockSystem (bitPHPSystem m l) h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j) := by
  classical
  obtain ⟨A, ⟨i, i', α, hii, rfl⟩, hA⟩ := hax
  have hdP := totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j)
  have hmem1 : ∀ t : Fin l, (({(i, t)} : Finset (Fin m × Fin l)), !α t) ∈ cl j := by
    intro t
    rw [← hA]
    simp only [linOfClause, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    exact ⟨((i, t), !α t), Or.inl ⟨t, rfl⟩, rfl⟩
  have hmem2 : ∀ t : Fin l, (({(i', t)} : Finset (Fin m × Fin l)), !α t) ∈ cl j := by
    intro t
    rw [← hA]
    simp only [linOfClause, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and]
    exact ⟨((i', t), !α t), Or.inr ⟨t, rfl⟩, rfl⟩
  set S := blockSystem (bitPHPSystem m l) h M W (clauseInputs e cl) with hS
  set P := blockProduct h M W (clauseInputs e cl) j with hPdef
  let a : Fin l → MvPolynomial (BlockVar (Fin m × Fin l) h M W) (ZMod 2) :=
    fun t => X (Sum.inl (i, t)) + X (Sum.inl (i', t))
  have hda : ∀ t ∈ (Finset.univ : Finset (Fin l)), (a t).totalDegree ≤ 1 := fun t _ =>
    (totalDegree_add _ _).trans (max_le (totalDegree_X _).le (totalDegree_X _).le)
  have ha : ∀ t ∈ (Finset.univ : Finset (Fin l)), PCDerivable S B (a t * P) := by
    intro t _
    have h1 := block_companion (F := bitPHPSystem m l) (h := h) he j (hmem1 t) (B := B) hB2
    have h2 := block_companion (F := bitPHPSystem m l) (h := h) he j (hmem2 t) (B := B) hB2
    have h3 := h1.add h2
    have hEq : rename (Sum.inl : _ → BlockVar (Fin m × Fin l) h M W)
          (eqPoly (({(i, t)} : Finset (Fin m × Fin l)), !α t)) * P
        + rename Sum.inl (eqPoly (({(i', t)} : Finset (Fin m × Fin l)), !α t)) * P
        = a t * P := by
      simp only [eqPoly, Finset.sum_singleton, map_add, rename_X, rename_C, a]
      linear_combination char2_add_self
        ((C (if (!α t) = true then (0 : ZMod 2) else 1) :
          MvPolynomial (BlockVar (Fin m × Fin l) h M W) (ZMod 2)) * P)
    rw [← hEq]
    exact h3
  have h1 := pcDerivable_prod_absorb (Finset.univ : Finset (Fin l)) a P hdP ha hda
    (by simpa using (by omega : 1 * l + 2 * h ≤ B))
  have hE : PCDerivable S B (∏ t : Fin l, (1 + a t)) := by
    refine .ax (Or.inl ⟨_, Or.inr ⟨i, i', hii, rfl⟩, ?_⟩) ?_
    · simp [a, add_assoc]
    · have := totalDegree_prod_one_add_le (Finset.univ : Finset (Fin l)) a hda
      simp only [Finset.card_univ, Fintype.card_fin, one_mul] at this
      omega
  have h2 := pcDerivable_mul_le hE P hdP
    (by simpa using totalDegree_prod_one_add_le (Finset.univ : Finset (Fin l)) a hda)
    le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ t : Fin l, (1 + a t)) * P + P + P * ∏ t : Fin l, (1 + a t) = P := by
    linear_combination char2_add_self ((∏ t : Fin l, (1 + a t)) * P)
  rw [hEq] at h3
  exact h3
end Axioms
end C.Helpers
namespace C.Helpers
open MvPolynomial PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]
def eqVec (q : LinEq V) : (V → ZMod 2) × ZMod 2 :=
  (fun v => if v ∈ q.1 then 1 else 0, if q.2 = true then 0 else 1)
noncomputable def affPoly : ((V → ZMod 2) × ZMod 2) →ₗ[ZMod 2] MvPolynomial V (ZMod 2) :=
  (Fintype.linearCombination (ZMod 2) (fun v : V => (X v : MvPolynomial V (ZMod 2)))).coprod
    (Algebra.linearMap (ZMod 2) (MvPolynomial V (ZMod 2)))
theorem affPoly_eqVec (q : LinEq V) : affPoly (eqVec q) = eqPoly q := by
  simp [affPoly, eqVec, eqPoly, Fintype.linearCombination_apply, MvPolynomial.algebraMap_eq,
    Finset.sum_ite_mem]
omit [DecidableEq V] in
theorem affPoly_one : affPoly ((0, 1) : (V → ZMod 2) × ZMod 2) = 1 := by
  simp [affPoly, Fintype.linearCombination_apply]
omit [Fintype V] [DecidableEq V] in
theorem linEqSat_iff_sum (a : V → ZMod 2) (q : LinEq V) :
    LinEqSat (fun v => decide (a v = 1)) q ↔
      ∑ v ∈ q.1, a v + (if q.2 = true then 0 else 1) = 1 := by
  unfold LinEqSat
  have hs : ∑ v ∈ q.1, a v
      = ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    generalize a v = x
    revert x
    decide
  rw [hs, ← ZMod.natCast_eq_one_iff_odd]
  generalize ((q.1.filter (fun v => decide (a v = 1) = true)).card : ZMod 2) = x
  rcases q with ⟨f, b⟩
  cases b
  · simp only [Bool.false_eq_true, iff_false, ite_false]
    revert x
    decide
  · simp
theorem dual_apply (φ : Module.Dual (ZMod 2) ((V → ZMod 2) × ZMod 2))
    (h1 : φ (0, 1) = 1) (q : LinEq V) :
    φ (eqVec q) = ∑ v ∈ q.1, φ (fun j => if v = j then 1 else 0, 0) + (if q.2 = true then 0 else 1) := by
  have hsplit : eqVec q = LinearMap.inl (ZMod 2) (V → ZMod 2) (ZMod 2)
      (fun v => if v ∈ q.1 then 1 else 0)
      + (if q.2 = true then (0 : ZMod 2) else 1) • ((0, 1) : (V → ZMod 2) × ZMod 2) := by
    rcases q with ⟨f, b⟩
    cases b <;> simp [eqVec]
  rw [hsplit, map_add, map_smul, h1, ← LinearMap.comp_apply, LinearMap.pi_apply_eq_sum_univ]
  simp [Finset.sum_ite_mem]
theorem lin_choice (q : LinEq V) (D : LinClause V)
    (himp : ∀ a : V → Bool, LinEqSat a q → LinClauseSat a D) :
    ∃ J : Finset (LinEq V), J ⊆ D ∧
      (∑ d ∈ J, eqPoly d = 1 ∨ ∑ d ∈ J, eqPoly d = eqPoly q) := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (insert (eqVec q + (0, 1)) (eqVec '' (D : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hq : LinEqSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) q := by
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Set.mem_insert _ _))
      rw [map_add, h1] at this
      generalize φ (eqVec q) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hq
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨d, hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.mem_span_insert] at hmem
  obtain ⟨c, z, hz, hEq⟩ := hmem
  rw [Finsupp.mem_span_image_iff_linearCombination] at hz
  obtain ⟨lc, hlc, rfl⟩ := hz
  have hJ : lc.support ⊆ D := by
    intro d hd
    exact Finsupp.mem_supported _ _ |>.mp hlc hd
  have hsum : affPoly (Finsupp.linearCombination (ZMod 2) eqVec lc)
      = ∑ d ∈ lc.support, eqPoly d := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
    have h1 : lc d = 1 := by
      generalize lc d = x at h0
      revert x
      decide
    rw [h1, one_smul, affPoly_eqVec]
  have hP := congrArg affPoly hEq
  rw [map_add, map_smul, map_add, affPoly_one, affPoly_eqVec, hsum] at hP
  refine ⟨lc.support, hJ, ?_⟩
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc c with rfl | rfl
  · left
    rw [zero_smul, zero_add] at hP
    exact hP.symm
  · right
    rw [one_smul] at hP
    linear_combination hP + char2_add_self (∑ d ∈ lc.support, eqPoly d)
end C.Helpers
namespace C.Helpers
open MvPolynomial Module
def rowLinearSet (m l k : ℕ) : Set ((Fin m × Fin l) →₀ ℕ) :=
  {u | (u.sum fun _ e => e) ≤ k ∧ ∀ i, ∑ t, u (i, t) ≤ 1}
noncomputable def rowLinear (m l k : ℕ) : Submodule (ZMod 2) (MvPolynomial (Fin m × Fin l) (ZMod 2)) :=
  restrictSupport (ZMod 2) (rowLinearSet m l k)
theorem rowLinearSet_finite (m l k : ℕ) : (rowLinearSet m l k).Finite := by
  have h : {u : (Fin m × Fin l) →₀ ℕ | ∀ a, u a ≤ 1}.Finite :=
    (Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn
  refine h.subset fun u hu a => ?_
  refine le_trans ?_ (hu.2 a.1)
  exact Finset.single_le_sum (f := fun t => u (a.1, t)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a.2)
theorem rowLinear_le_restrictTotalDegree (m l k : ℕ) :
    rowLinear m l k ≤ restrictTotalDegree (Fin m × Fin l) (ZMod 2) k :=
  restrictSupport_mono (ZMod 2) fun _ hu => hu.1
theorem totalDegree_le_of_mem_rowLinear {m l k : ℕ}
    {f : MvPolynomial (Fin m × Fin l) (ZMod 2)} (hf : f ∈ rowLinear m l k) :
    f.totalDegree ≤ k :=
  (mem_restrictTotalDegree _ _ _).1 (rowLinear_le_restrictTotalDegree m l k hf)
noncomputable def rowMonomial {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) :
    (Fin m × Fin l) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    fun x => if h : x.1 ∈ S then (if c ⟨x.1, h⟩ = x.2 then 1 else 0) else 0
theorem rowMonomial_apply {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) (x : Fin m × Fin l) :
    rowMonomial S c x = if h : x.1 ∈ S then (if c ⟨x.1, h⟩ = x.2 then 1 else 0) else 0 :=
  rfl
theorem rowMonomial_row_sum {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) (i : Fin m) :
    ∑ t, rowMonomial S c (i, t) = if i ∈ S then 1 else 0 := by
  by_cases h : i ∈ S
  · simp only [rowMonomial_apply, h, dite_true, ite_true]
    exact (Finset.sum_ite_eq Finset.univ (c ⟨i, h⟩) (fun _ => 1)).trans (by simp)
  · simp [rowMonomial_apply, h]
theorem rowMonomial_mem {m l k : ℕ} (S : Finset (Fin m)) (hS : S.card = k) (c : S → Fin l) :
    rowMonomial S c ∈ rowLinearSet m l k := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
    simp [rowMonomial_row_sum, hS]
  · rw [rowMonomial_row_sum]
    split_ifs <;> simp
theorem rowMonomial_injective {m l : ℕ} {S S' : Finset (Fin m)} {c : S → Fin l}
    {c' : S' → Fin l} (h : rowMonomial S c = rowMonomial S' c') : S = S' ∧ HEq c c' := by
  have hS : S = S' := by
    ext i
    have := congrArg (fun u : (Fin m × Fin l) →₀ ℕ => ∑ t, u (i, t)) h
    simp only [rowMonomial_row_sum] at this
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all
  subst hS
  refine ⟨rfl, heq_of_eq (funext fun i => ?_)⟩
  by_contra hne
  have hne' : ¬ c' i = c i := fun h' => hne h'.symm
  have := DFunLike.congr_fun h (i.1, c i)
  simp [rowMonomial_apply, hne'] at this
theorem le_finrank_rowLinear (m l k : ℕ) :
    m.choose k * l ^ k ≤ finrank (ZMod 2) (rowLinear m l k) := by
  classical
  have hfin : Finite (rowLinearSet m l k) := (rowLinearSet_finite m l k).to_subtype
  have hrank : finrank (ZMod 2) (rowLinear m l k) = Nat.card (rowLinearSet m l k) :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport (ZMod 2) (rowLinearSet m l k))
  rw [hrank]
  let g : (Σ S : {S : Finset (Fin m) // S.card = k}, (S.1 → Fin l)) → rowLinearSet m l k :=
    fun p => ⟨rowMonomial p.1.1 p.2, rowMonomial_mem p.1.1 p.1.2 p.2⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨S, hS⟩, c⟩ ⟨⟨S', hS'⟩, c'⟩ h
    obtain ⟨rfl, hc⟩ := rowMonomial_injective (congrArg Subtype.val h)
    obtain rfl := eq_of_heq hc
    rfl
  have hcard : Nat.card (Σ S : {S : Finset (Fin m) // S.card = k}, (S.1 → Fin l))
      = m.choose k * l ^ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    have : ∀ S : {S : Finset (Fin m) // S.card = k}, Fintype.card (S.1 → Fin l) = l ^ k := by
      intro S
      simp [S.2]
    rw [Finset.sum_congr rfl fun S _ => this S]
    simp
  rw [← hcard]
  exact Nat.card_le_card_of_injective g hg
theorem exists_ne_zero_forall_eq_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V →ₗ[K] W i) (D : ι → ℕ)
    (hD : ∀ i, finrank K (LinearMap.range (f i)) ≤ D i) (h : ∑ i, D i < finrank K V) :
    ∃ v, v ≠ 0 ∧ ∀ i, f i v = 0 := by
  have hV : Module.Finite K V := Module.finite_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le _) h)
  by_contra hcon
  push Not at hcon
  let F : V →ₗ[K] (∀ i, LinearMap.range (f i)) := LinearMap.pi fun i => (f i).rangeRestrict
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    obtain ⟨i, hi⟩ := hcon v hv0
    exact hi (congrArg Subtype.val (congrFun hv i))
  have h1 := LinearMap.finrank_le_finrank_of_injective hF
  rw [Module.finrank_pi_fintype] at h1
  exact absurd (lt_of_le_of_lt (h1.trans (Finset.sum_le_sum fun i _ => hD i)) h) (lt_irrefl _)
theorem totalDegree_aeval_le {σ τ K : Type*} [Field K]
    (φ : σ → MvPolynomial τ K) (hφ : ∀ x, (φ x).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (aeval φ f).totalDegree ≤ f.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finsetSum_le fun u hu => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_totalDegree hu)
  refine (totalDegree_pow _ _).trans ?_
  exact (Nat.mul_le_mul_left _ (hφ i)).trans (le_of_eq (mul_one _))
theorem card_degree_le (d k : ℕ) :
    Nat.card {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} ≤ (d + k).choose k := by
  classical
  let g : {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} → Sym (Option (Fin d)) k := fun u =>
    ⟨(Finsupp.toMultiset u.1).map some
        + Multiset.replicate (k - (u.1.sum fun _ e => e)) none, by
      have h : (u.1.sum fun _ e => e) ≤ k := u.2
      have e : (u.1.sum fun _ => id) = u.1.sum fun _ e => e := rfl
      simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
        Finsupp.card_toMultiset, e]
      omega⟩
  have hg : Function.Injective g := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    apply Subtype.ext
    ext x
    have h1 := congrArg (fun s : Sym (Option (Fin d)) k => Multiset.count (some x) s.1) h
    simpa [g, Multiset.count_map_eq_count' some _ (Option.some_injective _),
      Multiset.count_replicate] using h1
  have h2 := Nat.card_le_card_of_injective g hg
  have h3 : Nat.card (Sym (Option (Fin d)) k) = (d + k).choose k := by
    rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_multichoose, Nat.multichoose_eq]
    simp
  exact h3 ▸ h2
theorem finrank_restrictTotalDegree_le (K : Type*) [Field K] (d k : ℕ) :
    finrank K (restrictTotalDegree (Fin d) K k) ≤ (d + k).choose k := by
  have h : finrank K (restrictTotalDegree (Fin d) K k)
      = Nat.card {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
  rw [h]
  exact card_degree_le d k
theorem finrank_range_aeval_rowLinear_le {m l k d : ℕ}
    (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2)) (hφ : ∀ x, (φ x).totalDegree ≤ 1) :
    finrank (ZMod 2)
      (LinearMap.range ((aeval φ).toLinearMap ∘ₗ (rowLinear m l k).subtype))
      ≤ (d + k).choose k := by
  refine le_trans (Submodule.finrank_mono ?_) (finrank_restrictTotalDegree_le (ZMod 2) d k)
  rintro _ ⟨f, rfl⟩
  rw [mem_restrictTotalDegree]
  exact (totalDegree_aeval_le φ hφ f.1).trans (totalDegree_le_of_mem_rowLinear f.2)
theorem exists_cofactors_monomial {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
    (ψ : σ → MvPolynomial σ K) (hψ : ∀ x, (ψ x).totalDegree ≤ 1) :
    ∀ (n : ℕ) (s : σ →₀ ℕ) (c : K), (s.sum fun _ e => e) = n →
      ∃ a : σ → MvPolynomial σ K,
        monomial s c - aeval ψ (monomial s c) = ∑ x, a x * (X x - ψ x) ∧
        ∀ x, a x = 0 ∨ (a x).totalDegree + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro s c hs
    have hs0 : s = 0 := by
      ext y
      by_contra hy
      have hmem : y ∈ s.support := Finsupp.mem_support_iff.2 hy
      have h1 : s y ≤ ∑ i ∈ s.support, s i :=
        Finset.single_le_sum (f := fun i => s i) (fun _ _ => Nat.zero_le _) hmem
      have h2 : ∑ i ∈ s.support, s i = 0 := hs
      exact hy (by simpa using Nat.le_zero.1 (h2 ▸ h1))
    subst hs0
    refine ⟨fun _ => 0, ?_, fun _ => Or.inl rfl⟩
    have : (monomial (0 : σ →₀ ℕ) c : MvPolynomial σ K) = C c := rfl
    simp [this]
  | succ n ih =>
    intro s c hs
    obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : s = 0 := Finsupp.ext hcon
      subst this
      simp at hs
    set s' : σ →₀ ℕ := s - Finsupp.single x 1 with hs'
    have hsplit : s = s' + Finsupp.single x 1 := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp only [hs', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]
        omega
      · simp [hs', Ne.symm hy]
    have hsum : (s'.sum fun _ e => e) = n := by
      have h1 : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1 := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      omega
    obtain ⟨a, ha, hdeg⟩ := ih s' c hsum
    set p : MvPolynomial σ K := monomial s' c with hp
    have hmon : monomial s c = p * X x := by
      rw [hsplit, monomial_add_single, pow_one]
    have hpdeg : p.totalDegree ≤ n := by
      have := totalDegree_monomial_le s' c
      exact this.trans (le_of_eq hsum)
    refine ⟨fun y => ψ x * a y + if y = x then p else 0, ?_, fun y => Or.inr ?_⟩
    · have e1 : ∑ y, (ψ x * a y + if y = x then p else 0) * (X y - ψ y)
          = ψ x * ∑ y, a y * (X y - ψ y) + p * (X x - ψ x) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, ite_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [e1, ← ha, hmon, map_mul, aeval_X]
      ring
    · show (ψ x * a y + if y = x then p else 0).totalDegree + 1 ≤ n + 1
      have h1 : (ψ x * a y).totalDegree ≤ n := by
        rcases hdeg y with h0 | h0
        · simp [h0]
        · have := totalDegree_mul (ψ x) (a y)
          have := hψ x
          omega
      have h2 : (if y = x then p else 0 : MvPolynomial σ K).totalDegree ≤ n := by
        split_ifs
        · exact hpdeg
        · simp
      have := totalDegree_add (ψ x * a y) (if y = x then p else 0)
      have := max_le h1 h2
      omega
theorem exists_cofactors {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
    (ψ : σ → MvPolynomial σ K) (hψ : ∀ x, (ψ x).totalDegree ≤ 1)
    (f : MvPolynomial σ K) (k : ℕ) (hf : f.totalDegree ≤ k) :
    ∃ a : σ → MvPolynomial σ K,
      f - aeval ψ f = ∑ x, a x * (X x - ψ x) ∧ ∀ x, (a x).totalDegree ≤ k - 1 := by
  choose A hA1 hA2 using fun (u : σ →₀ ℕ) (c : K) =>
    exists_cofactors_monomial ψ hψ _ u c rfl
  refine ⟨fun x => ∑ u ∈ f.support, A u (f.coeff u) x, ?_, fun x => ?_⟩
  · conv_lhs => rw [← support_sum_monomial_coeff f]
    rw [map_sum, ← Finset.sum_sub_distrib]
    simp_rw [hA1, Finset.sum_mul]
    exact Finset.sum_comm
  · refine totalDegree_finsetSum_le fun u hu => ?_
    rcases hA2 u (f.coeff u) x with h0 | h0
    · simp [h0]
    · have h1 : (u.sum fun _ e => e) ≤ f.totalDegree := le_totalDegree hu
      omega
theorem choose_mul_pow_le {m l k d : ℕ} (hkm : k ≤ m)
    (hd : d + 3 * l * (k + 1) + 1 ≤ m * l) :
    (d + k).choose k * m ^ k ≤ m.choose k * l ^ k * (m - k) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  have hsub : k + j - k = j := by omega
  rw [hsub]
  have hkl : k ≤ l * k := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp at hd
    · exact Nat.le_mul_of_pos_left k hl
  have h1 : d + k + l * k ≤ j * l := by nlinarith
  have key : (d + k) * (k + j) ≤ l * (j + 1) * j := by
    nlinarith [Nat.mul_le_mul_right (k + j) h1]
  have hA : (d + k).choose k * k.factorial ≤ (d + k) ^ k := by
    have := Nat.descFactorial_le_pow (d + k) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    rwa [mul_comm]
  have hB : (j + 1) ^ k ≤ k.factorial * (k + j).choose k := by
    have := Nat.pow_sub_le_descFactorial (k + j) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    have e : k + j + 1 - k = j + 1 := by omega
    rwa [e] at this
  have hpos : 0 < (j + 1) ^ k := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (j + 1) ^ k * ((d + k).choose k * (k + j) ^ k)
      ≤ (k.factorial * (k + j).choose k) * ((d + k).choose k * (k + j) ^ k) :=
        Nat.mul_le_mul_right _ hB
    _ = ((d + k).choose k * k.factorial) * ((k + j) ^ k * (k + j).choose k) := by ring
    _ ≤ (d + k) ^ k * ((k + j) ^ k * (k + j).choose k) := Nat.mul_le_mul_right _ hA
    _ = ((d + k) * (k + j)) ^ k * (k + j).choose k := by rw [mul_pow]; ring
    _ ≤ (l * (j + 1) * j) ^ k * (k + j).choose k :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left key k)
    _ = (j + 1) ^ k * ((k + j).choose k * l ^ k * j ^ k) := by rw [mul_pow, mul_pow]; ring
theorem mul_choose_lt {m l k M d : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (hd : d + 3 * l * (k + 1) + 1 ≤ m * l) :
    M * (d + k).choose k < m.choose k * l ^ k := by
  have hBpos : 0 < m.choose k * l ^ k :=
    Nat.mul_pos (Nat.choose_pos hkm) (by positivity)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa using hBpos
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hd
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := choose_mul_pow_le hkm hd
  have hNR : ((d + k).choose k : ℝ) * (m : ℝ) ^ k
      ≤ (m.choose k : ℝ) * (l : ℝ) ^ k * ((m : ℝ) - k) ^ k := by
    have := (Nat.cast_le (α := ℝ)).2 hN
    push_cast [Nat.cast_sub hkm] at this
    exact this
  have hjm : (0 : ℝ) ≤ (m : ℝ) - k := by
    have : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  have h1 : ((m : ℝ) - k) / m ≤ Real.exp (-(k / m)) := by
    have := Real.add_one_le_exp (-((k : ℝ) / m))
    have e : ((m : ℝ) - k) / m = -((k : ℝ) / m) + 1 := by field_simp; ring
    rw [e]; exact this
  have h2 : (((m : ℝ) - k) / m) ^ k ≤ Real.exp (-((k : ℝ) ^ 2 / m)) := by
    refine (pow_le_pow_left₀ (div_nonneg hjm hmR.le) h1 k).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : (4 * M : ℝ) ≤ Real.exp ((k : ℝ) ^ 2 / m) := by
    have hpos : (0 : ℝ) < 4 * M := by positivity
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hmR]
    linarith
  have h4 : ((m : ℝ) - k) ^ k * (4 * M) ≤ (m : ℝ) ^ k := by
    have h5 : (((m : ℝ) - k) / m) ^ k * (4 * M) ≤ 1 := by
      calc (((m : ℝ) - k) / m) ^ k * (4 * M)
          ≤ Real.exp (-((k : ℝ) ^ 2 / m)) * Real.exp ((k : ℝ) ^ 2 / m) :=
            mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)] at h5
    exact h5
  have hBR : (0 : ℝ) ≤ (m.choose k : ℝ) * (l : ℝ) ^ k := by positivity
  have h6 : (4 * M * (d + k).choose k : ℝ) * (m : ℝ) ^ k
      ≤ ((m.choose k : ℝ) * (l : ℝ) ^ k) * (m : ℝ) ^ k := by
    calc (4 * M * (d + k).choose k : ℝ) * (m : ℝ) ^ k
        = (4 * M) * (((d + k).choose k : ℝ) * (m : ℝ) ^ k) := by ring
      _ ≤ (4 * M) * ((m.choose k : ℝ) * (l : ℝ) ^ k * ((m : ℝ) - k) ^ k) :=
          mul_le_mul_of_nonneg_left hNR (by positivity)
      _ = ((m.choose k : ℝ) * (l : ℝ) ^ k) * (((m : ℝ) - k) ^ k * (4 * M)) := by ring
      _ ≤ ((m.choose k : ℝ) * (l : ℝ) ^ k) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h4 hBR
  have h7 : (4 * M * (d + k).choose k : ℝ) ≤ (m.choose k : ℝ) * (l : ℝ) ^ k :=
    le_of_mul_le_mul_right h6 (by positivity)
  have h8 : 4 * M * (d + k).choose k ≤ m.choose k * l ^ k := by exact_mod_cast h7
  have h9 : 4 * (M * (d + k).choose k) ≤ m.choose k * l ^ k := by rw [← mul_assoc]; exact h8
  omega
theorem exists_rowLinear_aeval_eq_zero {m l k M : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (d : Fin M → ℕ) (hd : ∀ j, d j + 3 * l * (k + 1) + 1 ≤ m * l)
    (φ : ∀ j, Fin m × Fin l → MvPolynomial (Fin (d j)) (ZMod 2))
    (hφ : ∀ j x, (φ j x).totalDegree ≤ 1) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2),
      f ∈ rowLinear m l k ∧ f ≠ 0 ∧ ∀ j, aeval (φ j) f = 0 := by
  have hsum : ∑ j, (d j + k).choose k < finrank (ZMod 2) (rowLinear m l k) := by
    refine lt_of_lt_of_le ?_ (le_finrank_rowLinear m l k)
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simpa using Nat.mul_pos (Nat.choose_pos hkm) (pow_pos hl k)
    ·
      obtain ⟨d0, hd0, hmax⟩ : ∃ d0, d0 + 3 * l * (k + 1) + 1 ≤ m * l ∧ ∀ j, d j ≤ d0 := by
        refine ⟨m * l - (3 * l * (k + 1) + 1), ?_, fun j => ?_⟩
        · have := hd ⟨0, hM⟩
          omega
        · have := hd j
          omega
      refine lt_of_le_of_lt ?_ (mul_choose_lt (M := M) hl hkm hlog hd0)
      calc ∑ j, (d j + k).choose k ≤ ∑ _j : Fin M, (d0 + k).choose k :=
            Finset.sum_le_sum fun j _ => Nat.choose_le_choose k (by have := hmax j; omega)
        _ = M * (d0 + k).choose k := by simp
  obtain ⟨v, hv, hzero⟩ := exists_ne_zero_forall_eq_zero
    (fun j => (aeval (φ j)).toLinearMap ∘ₗ (rowLinear m l k).subtype)
    (fun j => (d j + k).choose k)
    (fun j => finrank_range_aeval_rowLinear_le (φ j) (hφ j)) hsum
  exact ⟨v.1, v.2, fun h => hv (Subtype.ext h), fun j => hzero j⟩
theorem exists_rowLinear_eq_sum_mul {m l k M : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (d : Fin M → ℕ) (hd : ∀ j, d j + 3 * l * (k + 1) + 1 ≤ m * l)
    (φ : ∀ j, Fin m × Fin l → MvPolynomial (Fin (d j)) (ZMod 2))
    (hφ : ∀ j x, (φ j x).totalDegree ≤ 1)
    (ι : ∀ j, Fin (d j) → Fin m × Fin l) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2),
      f ∈ rowLinear m l k ∧ f ≠ 0 ∧ ∀ j,
        ∃ a : Fin m × Fin l → MvPolynomial (Fin m × Fin l) (ZMod 2),
          f = ∑ x, a x * (X x - rename (ι j) (φ j x)) ∧ ∀ x, (a x).totalDegree ≤ k - 1 := by
  obtain ⟨f, hf, hf0, hzero⟩ := exists_rowLinear_aeval_eq_zero hl hkm hlog d hd φ hφ
  refine ⟨f, hf, hf0, fun j => ?_⟩
  have hcomp : aeval (fun x => rename (ι j) (φ j x))
      = ((rename (ι j)).comp (aeval (φ j)) :
          MvPolynomial (Fin m × Fin l) (ZMod 2) →ₐ[ZMod 2] _) := by
    apply algHom_ext
    intro x
    simp
  have hker : aeval (fun x => rename (ι j) (φ j x)) f = 0 := by
    rw [hcomp, AlgHom.comp_apply, hzero j, map_zero]
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun x => rename (ι j) (φ j x))
    (fun x => (totalDegree_rename_le _ _).trans (hφ j x)) f k
    (totalDegree_le_of_mem_rowLinear hf)
  rw [hker, sub_zero] at ha
  exact ⟨a, ha, hdeg⟩
end C.Helpers
namespace C.Helpers.BoolVanish
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
variable {σ : Type}
noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v
noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a
theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]
theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this
theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]
theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v
end C.Helpers.BoolVanish
namespace C.Helpers.LowRankBlock
open MvPolynomial
theorem prod_one_add_telescope {R : Type*} [CommRing R] (G : ℕ → R) (n : ℕ) :
    ∏ a ∈ Finset.range n, (1 + G a) =
      1 + ∑ a ∈ Finset.range n, G a * ∏ b ∈ Finset.range a, (1 + G b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
    ring
theorem totalDegree_prod_one_add_le {σ : Type} (G : ℕ → MvPolynomial σ (ZMod 2))
    (hG : ∀ a, (G a).totalDegree ≤ 1) (n : ℕ) :
    (∏ a ∈ Finset.range n, (1 + G a)).totalDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (1 + G n).totalDegree ≤ 1 := by
      refine (totalDegree_add _ _).trans ?_
      simp [hG n]
    omega
theorem zmod_two_eq_one_of_ne_zero {y : ZMod 2} (hy : y ≠ 0) : y = 1 := by
  revert y
  decide
theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide
theorem low_rank : ∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0 := by
  intro σ s h k g hg _ _ hr
  set V := Submodule.span (ZMod 2) (Set.range g) with hV
  have : Module.Finite (ZMod 2) V := Module.Finite.span_of_finite (ZMod 2) (Set.finite_range g)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := Module.finrank (ZMod 2) V with hrdef
  let b : Module.Basis (Fin r) (ZMod 2) V := Module.finBasis (ZMod 2) V
  have hVdeg : V ≤ restrictTotalDegree σ (ZMod 2) 1 := by
    rw [hV, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_restrictTotalDegree _ _ _).2 (hg i)
  let G : ℕ → ℕ → MvPolynomial σ (ZMod 2) := fun u a =>
    if hl : u * (k + 1) + a < r then (b ⟨_, hl⟩ : MvPolynomial σ (ZMod 2)) else 0
  have hGV : ∀ u a, G u a ∈ V := by
    intro u a
    simp only [G]
    split_ifs
    · exact (b _).2
    · exact V.zero_mem
  have hGdeg : ∀ u a, (G u a).totalDegree ≤ 1 := fun u a =>
    (mem_restrictTotalDegree _ _ _).1 (hVdeg (hGV u a))
  have hμ : ∀ u a, ∃ μ : Fin s → ZMod 2, ∑ i, μ i • g i = G u a := fun u a =>
    (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hGV u a)
  choose μ hμ using hμ
  let P : ℕ → ℕ → MvPolynomial σ (ZMod 2) := fun u n =>
    ∏ a ∈ Finset.range n, (1 + G u a)
  refine ⟨fun u i => ∑ a ∈ Finset.range (k + 1), μ u a i • P u a, ?_, ?_⟩
  · intro u i
    refine (totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun a ha => ?_
    refine (totalDegree_smul_le _ _).trans ?_
    have : (P u a).totalDegree ≤ a := totalDegree_prod_one_add_le (G u) (hGdeg u) a
    have := Finset.mem_range.1 ha
    omega
  have hfac : ∀ u : Fin h,
      1 + ∑ i' : Fin s, (∑ a ∈ Finset.range (k + 1), μ u a i' • P u a) * g i' = P u (k + 1) := by
    intro u
    rw [show P u (k + 1) = _ from prod_one_add_telescope (G u) (k + 1)]
    congr 1
    simp_rw [Finset.sum_mul, smul_mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hμ u a, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_comm]
  simp_rw [hfac]
  intro i
  refine ⟨?_, ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    have h1 : (∏ u : Fin h, P u (k + 1)).totalDegree ≤ h * (k + 1) := by
      refine (totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_sum fun (u : Fin h) _ =>
        totalDegree_prod_one_add_le (G u) (hGdeg u) (k + 1)).trans ?_
      simp
    have := hg i
    omega
  · intro x
    rw [map_mul, map_prod]
    by_cases hall : ∀ (u : Fin h) a, a < k + 1 → eval x (G u a) = 0
    ·
      have hF : ∀ j : Fin r, eval x (b j : MvPolynomial σ (ZMod 2)) = 0 := by
        intro j
        have hj : (j : ℕ) / (k + 1) < h := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          exact lt_of_lt_of_le j.2 hr
        have ha : (j : ℕ) % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
        have := hall ⟨_, hj⟩ _ ha
        have hidx : (j : ℕ) / (k + 1) * (k + 1) + (j : ℕ) % (k + 1) = j := by
          rw [mul_comm]; exact Nat.div_add_mod _ _
        simp only [G] at this
        rw [dite_eq_left (by rw [hidx]; exact j.2)] at this
        convert this using 4
        exact Fin.ext hidx.symm
      have hgi : g i ∈ V := Submodule.subset_span ⟨i, rfl⟩
      have hsum := b.sum_repr ⟨g i, hgi⟩
      have hsum' : g i = ∑ j, (b.repr ⟨g i, hgi⟩ j) • (b j : MvPolynomial σ (ZMod 2)) := by
        have := congrArg Subtype.val hsum
        rw [Submodule.coe_sum] at this
        simpa using this.symm
      rw [hsum', map_sum]
      simp [hF]
    · push Not at hall
      obtain ⟨u, a, ha, hne⟩ := hall
      have h1 : eval x (G u a) = 1 := by
        exact zmod_two_eq_one_of_ne_zero hne
      apply mul_eq_zero_of_right
      refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
      simp only [P]
      rw [map_prod]
      refine Finset.prod_eq_zero (Finset.mem_range.2 ha) ?_
      rw [map_add, map_one, h1]
      exact zmod_two_one_add_one
end C.Helpers.LowRankBlock
namespace C.Helpers.BlockRemoval
open MvPolynomial
theorem block_exists
    (H1 : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p)
    (H2 : ∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0)
    {σ : Type} {s h k D : ℕ} (F : Set (MvPolynomial σ (ZMod 2)))
    (g : Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2))
    (hBool : ∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (hh : 1 ≤ h) (hk : 1 ≤ k) (hD : 2 * h + 1 ≤ D)
    (hf : f.totalDegree ≤ k)
    (hblock : h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) →
      (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range g) ∨
        ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧
          f = ∑ i, a i * g i) :
    ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧
      ∀ i, PCDerivable F (k * D + k)
        (f * (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i'))) := by
  classical
  have hkD : k * (2 * h + 1) ≤ k * D := Nat.mul_le_mul_left _ hD
  let u0 : Fin h := ⟨0, by omega⟩
  by_cases hlow : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1)
  · obtain ⟨c, hc, hP⟩ := H2 σ s h k g hg hh hk hlow
    refine ⟨c, hc, fun i => H1 σ F _ _ hBool ?_ ?_⟩
    · refine (totalDegree_mul _ _).trans ?_
      have := (hP i).1
      have : h * (k + 1) + 1 ≤ k * D := by nlinarith
      omega
    · intro x
      rw [map_mul, (hP i).2 x, mul_zero]
  · rcases hblock (by omega) with hone | ⟨a, ha, hfa⟩
    · obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hone
      refine ⟨fun u i => if u = u0 then C (l i) else 0, ?_, fun i => ?_⟩
      · intro u i
        dsimp only; split_ifs
        · rw [totalDegree_C]; omega
        · rw [totalDegree_zero]; omega
      · have hprod : ∏ u : Fin h, (1 + ∑ i' : Fin s,
            (fun u i => if u = u0 then C (l i) else 0) u i' * g i') = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ u0) ?_
          simp only [ite_true]
          have : ∑ i' : Fin s, C (l i') * g i' = 1 := by
            rw [← hl]
            exact Finset.sum_congr rfl fun i' _ => (smul_eq_C_mul _ _).symm
          rw [this]
          exact CharTwo.add_self_eq_zero 1
        rw [hprod, mul_zero, mul_zero]
        exact .zero
    · refine ⟨fun u i => if u = u0 then a i else 0, ?_, fun i => ?_⟩
      · intro u i
        dsimp only; split_ifs
        · exact (ha i).trans (Nat.sub_le _ _)
        · rw [totalDegree_zero]; omega
      · have hprod : ∏ u : Fin h, (1 + ∑ i' : Fin s,
            (fun u i => if u = u0 then a i else 0) u i' * g i') = 1 + f := by
          rw [Finset.prod_eq_single u0]
          · simp only [ite_true]
            rw [hfa]
          · intro u _ hu
            simp [hu]
          · intro hu
            exact absurd (Finset.mem_univ u0) hu
        rw [hprod]
        refine H1 σ F _ _ hBool ?_ ?_
        · have h1f : (1 + f).totalDegree ≤ k := by
            refine (totalDegree_add _ _).trans ?_
            rw [totalDegree_one]
            exact max_le (Nat.zero_le _) hf
          have h2 : (g i * (1 + f)).totalDegree ≤ 1 + k :=
            (totalDegree_mul _ _).trans (Nat.add_le_add (hg i) h1f)
          have h3 : (f * (g i * (1 + f))).totalDegree ≤ k + (1 + k) :=
            (totalDegree_mul _ _).trans (Nat.add_le_add hf h2)
          refine h3.trans ?_
          nlinarith
        · intro x
          simp only [map_mul, map_add, map_one]
          generalize eval x f = y
          generalize eval x (g i) = z
          revert y z
          decide
theorem of_lemmas : (∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p
) → (∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0
) → ∀ (σ β : Type) (s h k D : ℕ) (F : Set (MvPolynomial σ (ZMod 2))) (g : β → Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → (∀ b i, (g b i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → 2 * h + 1 ≤ D → f.totalDegree ≤ k → (∀ b : β, h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g b))) → (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b)) ∨ ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g b i) → PEqualNP.ProofComplexity.PCRefutable ((MvPolynomial.rename (Sum.inl : σ → σ ⊕ (β × Fin h × Fin s))) '' F ∪ {p | ∃ (b : β) (i : Fin s), p = MvPolynomial.rename Sum.inl (g b i) * ∏ u : Fin h, (1 + ∑ i' : Fin s, MvPolynomial.X (Sum.inr (b, u, i')) * MvPolynomial.rename Sum.inl (g b i'))} ∪ {p | ∃ t : β × Fin h × Fin s, p = MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t) + MvPolynomial.X (Sum.inr t)}) D → PEqualNP.ProofComplexity.PCDerivable F (k * (D + 1)) f := by
  intro H1 H2 σ β s h k D F g f hBool hg hh hk hD hf hblock hRef
  classical
  have hex := fun b => block_exists H1 H2 F (g b) f hBool (hg b) hh hk hD hf (hblock b)
  choose c hc hcomp using hex
  let φ : σ ⊕ (β × Fin h × Fin s) → MvPolynomial σ (ZMod 2) :=
    Sum.elim X (fun t => c t.1 t.2.1 t.2.2)
  have hφ : ∀ j, (φ j).totalDegree ≤ k := by
    rintro (v | ⟨b, u, i⟩)
    · simp only [φ, Sum.elim_inl, totalDegree_X]; exact hk
    · exact hc b u i
  have hinl : ∀ q : MvPolynomial σ (ZMod 2), bind₁ φ (rename Sum.inl q) = q := by
    intro q
    rw [bind₁_rename]
    have : φ ∘ Sum.inl = X := rfl
    rw [this, bind₁_X_left]
    rfl
  have hkD : k * (2 * h + 1) ≤ k * D := Nat.mul_le_mul_left _ hD
  have hmain := pcDerivable_replay (G := F) (T := k) (s := k) φ hφ f hf ?_ hRef
  · rw [map_one, mul_one] at hmain
    have : k * (D + 1) = k * D + k := by ring
    rw [this]
    exact hmain
  intro a ha hdeg
  rcases ha with (⟨q, hq, rfl⟩ | ⟨b, i, rfl⟩) | ⟨t, rfl⟩
  · rw [hinl]
    have hq' : q.totalDegree ≤ k * D := by
      have := totalDegree_bind₁_le φ hφ (rename Sum.inl q)
      rw [hinl] at this
      exact this.trans (Nat.mul_le_mul_left _ hdeg)
    have := pcDerivable_mul_left (PCDerivable.ax (B := k * D) hq hq') f
    refine pcDerivable_mono this (max_le (by omega) (by omega)) subset_rfl
  · have himg : bind₁ φ (rename Sum.inl (g b i) * ∏ u : Fin h,
        (1 + ∑ i' : Fin s, X (Sum.inr (b, u, i')) * rename Sum.inl (g b i')))
        = g b i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c b u i' * g b i') := by
      simp only [map_mul, map_prod, map_add, map_one, map_sum, hinl, bind₁_X_right]
      rfl
    rw [himg]
    exact hcomp b i
  · simp only [map_mul, map_add, bind₁_X_right]
    refine H1 σ F _ _ hBool ?_ ?_
    · have h1 := hφ (Sum.inr t)
      have h2 : (φ (Sum.inr t) * φ (Sum.inr t) + φ (Sum.inr t)).totalDegree ≤ k + k :=
        (totalDegree_add _ _).trans (max_le
          ((totalDegree_mul _ _).trans (Nat.add_le_add h1 h1)) (h1.trans (by omega)))
      have h3 : (f * (φ (Sum.inr t) * φ (Sum.inr t) + φ (Sum.inr t))).totalDegree
          ≤ k + (k + k) := (totalDegree_mul _ _).trans (Nat.add_le_add hf h2)
      refine h3.trans ?_
      nlinarith
    · intro x
      simp only [map_mul, map_add]
      generalize eval x f = y
      generalize eval x (φ (Sum.inr t)) = z
      revert y z
      decide
end C.Helpers.BlockRemoval
namespace C
theorem L038 : ∀ (σ β : Type) (s h k D : ℕ) (F : Set (MvPolynomial σ (ZMod 2))) (g : β → Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → (∀ b i, (g b i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → 2 * h + 1 ≤ D → f.totalDegree ≤ k → (∀ b : β, h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g b))) → (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b)) ∨ ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g b i) → PEqualNP.ProofComplexity.PCRefutable ((MvPolynomial.rename (Sum.inl : σ → σ ⊕ (β × Fin h × Fin s))) '' F ∪ {p | ∃ (b : β) (i : Fin s), p = MvPolynomial.rename Sum.inl (g b i) * ∏ u : Fin h, (1 + ∑ i' : Fin s, MvPolynomial.X (Sum.inr (b, u, i')) * MvPolynomial.rename Sum.inl (g b i'))} ∪ {p | ∃ t : β × Fin h × Fin s, p = MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t) + MvPolynomial.X (Sum.inr t)}) D → PEqualNP.ProofComplexity.PCDerivable F (k * (D + 1)) f :=
  Helpers.BlockRemoval.of_lemmas Helpers.BoolVanish.vanish_derivable Helpers.LowRankBlock.low_rank
end C
namespace C.Helpers
open MvPolynomial Module
theorem two_eq_zero_mvPolynomial {σ : Type} : (2 : MvPolynomial σ (ZMod 2)) = 0 := by
  calc (2 : MvPolynomial σ (ZMod 2)) = C (1 + 1) := by rw [C_add, C_1, one_add_one_eq_two]
    _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 from rfl, C_0]
theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide
section Param
variable {σ : Type} [Fintype σ] [DecidableEq σ]
noncomputable def affLin (σ : Type) [Fintype σ] :
    (Option σ → ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Fintype.linearCombination (ZMod 2) (fun o : Option σ => o.elim 1 X)
omit [DecidableEq σ] in
theorem affLin_apply (c : Option σ → ZMod 2) :
    affLin σ c = C (c none) + ∑ x, C (c (some x)) * X x := by
  rw [affLin, Fintype.linearCombination_apply, Fintype.sum_option]
  simp [smul_eq_C_mul]
theorem exists_affLin_eq (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ 1) :
    ∃ c, affLin σ c = p := by
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun _ : σ => (0 : MvPolynomial σ (ZMod 2)))
    (fun _ => by simp) p 1 hp
  have ha0 : ∀ x, a x = C ((a x).coeff 0) := fun x =>
    totalDegree_eq_zero_iff_eq_C.1 (by have := hdeg x; omega)
  have h0 : aeval (fun _ : σ => (0 : MvPolynomial σ (ZMod 2))) p = C (constantCoeff p) := by
    simpa using aeval_zero' (S₁ := MvPolynomial σ (ZMod 2)) p
  rw [h0] at ha
  refine ⟨fun o => o.elim (constantCoeff p) (fun x => (a x).coeff 0), ?_⟩
  rw [affLin_apply]
  calc C (constantCoeff p) + ∑ x, C ((a x).coeff 0) * X x
      = C (constantCoeff p) + ∑ x, a x * (X x - 0) := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => by rw [sub_zero, ← ha0 x]
    _ = p := by rw [← ha]; ring
theorem exists_param {W : ℕ} (g : Fin W → MvPolynomial σ (ZMod 2))
    (hg : ∀ i, (g i).totalDegree ≤ 1)
    (h1 : (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range g)) :
    ∃ (d : ℕ) (φ : σ → MvPolynomial (Fin d) (ZMod 2)) (ι : Fin d → σ),
      d + finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ Fintype.card σ ∧
      (∀ x, (φ x).totalDegree ≤ 1) ∧
      ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range g) := by
  classical
  set S := Submodule.span (ZMod 2) (Set.range g) with hS
  set S' := S.comap (affLin σ) with hS'
  let P : Finset σ → Prop := fun Fr => ∀ c ∈ S', (∀ x, x ∉ Fr → c (some x) = 0) → c = 0
  have hP0 : P ∅ := by
    intro c hc h0
    have hlin : affLin σ c = C (c none) := by
      rw [affLin_apply]
      simp [h0]
    rcases zmod2_cases (c none) with hn | hn
    · funext o
      cases o with
      | none => exact hn
      | some x => exact h0 x (Finset.notMem_empty x)
    · exfalso
      apply h1
      have : affLin σ c ∈ S := hc
      rwa [hlin, hn, C_1] at this
  obtain ⟨Fr, hFr, hmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, by simp [hP0]⟩
  have hPFr : P Fr := (Finset.mem_filter.1 hFr).2
  have hstep : ∀ x, ∃ c' : Option σ → ZMod 2,
      (∀ y, y ∉ Fr → c' (some y) = 0) ∧ X x - affLin σ c' ∈ S := by
    intro x
    by_cases hx : x ∈ Fr
    · refine ⟨Pi.single (some x) 1, fun y hy => ?_, ?_⟩
      · have hne : some y ≠ some x := fun h => hy (Option.some.inj h ▸ hx)
        exact Pi.single_eq_of_ne hne 1
      · have : affLin σ (Pi.single (some x) 1) = X x := by
          rw [affLin, Fintype.linearCombination_apply_single]
          simp
        rw [this, sub_self]
        exact S.zero_mem
    · have hnP : ¬ P (insert x Fr) := by
        intro hP
        have := hmax (insert x Fr) (by simp [hP])
        rw [Finset.card_insert_of_notMem hx] at this
        omega
      simp only [P] at hnP
      push Not at hnP
      obtain ⟨c, hcS, hc0, hcne⟩ := hnP
      have hcx : c (some x) = 1 := by
        rcases zmod2_cases (c (some x)) with h0 | h0
        · exfalso
          apply hcne
          refine hPFr c hcS fun y hy => ?_
          by_cases hyx : y = x
          · rw [hyx]; exact h0
          · exact hc0 y (by simp [hyx, hy])
        · exact h0
      refine ⟨Function.update c (some x) 0, fun y hy => ?_, ?_⟩
      · by_cases hyx : y = x
        · subst hyx; simp
        · have hne : some y ≠ some x := fun h => hyx (Option.some.inj h)
          rw [Function.update_of_ne hne]
          exact hc0 y (by simp [hyx, hy])
      · have hsum : c = Function.update c (some x) 0 + Pi.single (some x) 1 := by
          funext o
          by_cases ho : o = some x
          · subst ho; simp [hcx]
          · simp [Function.update_of_ne ho, Pi.single_eq_of_ne ho]
        have hX : affLin σ (Pi.single (some x) 1) = X x := by
          rw [affLin, Fintype.linearCombination_apply_single]
          simp
        have hlin : affLin σ c = affLin σ (Function.update c (some x) 0) + X x := by
          conv_lhs => rw [hsum]
          rw [map_add, hX]
        have hmem : affLin σ c ∈ S := hcS
        have h2 := two_eq_zero_mvPolynomial (σ := σ)
        have : X x - affLin σ (Function.update c (some x) 0) = affLin σ c := by
          rw [hlin]
          linear_combination (-(affLin σ (Function.update c (some x) 0))) * h2
        rw [this]
        exact hmem
  choose c' hc'0 hc'S using hstep
  let e : Fin Fr.card ≃ Fr := Fr.equivFin.symm
  refine ⟨Fr.card, fun x => C (c' x none) + ∑ t, C (c' x (some (e t).1)) * X t,
    fun t => (e t).1, ?_, fun x => ?_, fun x => ?_⟩
  · have hSle : S ≤ LinearMap.range (affLin σ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_range.2 (exists_affLin_eq _ (hg i))
    have hmap : S'.map (affLin σ) = S := Submodule.map_comap_eq_of_le hSle
    have hr1 : finrank (ZMod 2) S ≤ finrank (ZMod 2) S' := by
      rw [← hmap]
      exact Submodule.finrank_map_le _ _
    let π : S' →ₗ[ZMod 2] ({x : σ // x ∉ Fr} → ZMod 2) :=
      LinearMap.pi fun x => (LinearMap.proj (some x.1)) ∘ₗ S'.subtype
    have hπ : Function.Injective π := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      apply Subtype.ext
      exact hPFr c.1 c.2 fun x hx => congrFun hc ⟨x, hx⟩
    have hr2 := LinearMap.finrank_le_finrank_of_injective hπ
    have hcard : Fintype.card {x : σ // x ∉ Fr} = Fintype.card σ - Fr.card := by
      simp [Fintype.card_subtype_compl]
    rw [Module.finrank_fintype_fun_eq_card, hcard] at hr2
    have := Finset.card_le_univ Fr
    omega
  · refine (totalDegree_add _ _).trans (max_le (by simp) (totalDegree_finsetSum_le fun t _ => ?_))
    refine (totalDegree_mul _ _).trans ?_
    simp
  · have hren : rename (fun t => (e t).1) (C (c' x none) + ∑ t, C (c' x (some (e t).1)) * X t)
        = affLin σ (c' x) := by
      rw [affLin_apply]
      simp only [map_add, map_sum, map_mul, rename_C, rename_X]
      congr 1
      calc ∑ t, C (c' x (some (e t).1)) * X (e t).1
          = ∑ y : Fr, C (c' x (some y.1)) * X y.1 :=
            Equiv.sum_comp e
              (fun y : Fr => C (c' x (some y.1)) * (X y.1 : MvPolynomial σ (ZMod 2)))
        _ = ∑ y ∈ Fr, C (c' x (some y)) * X y :=
            Finset.sum_coe_sort Fr
              (fun y => C (c' x (some y)) * (X y : MvPolynomial σ (ZMod 2)))
        _ = ∑ y, C (c' x (some y)) * X y :=
            Finset.sum_subset (Finset.subset_univ Fr)
              (fun y _ hy => by rw [hc'0 x y hy, C_0, zero_mul])
    rw [hren]
    exact hc'S x
end Param
theorem exists_weight {m l k M W : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2))
    (hg : ∀ j i, (g j i).totalDegree ≤ 1) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ f ∈ rowLinear m l k ∧
      ∀ j, (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
          ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∃ a : Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2),
          (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g j i := by
  classical
  have hpar : ∀ j, (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
        ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
      3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
      ∃ (d : ℕ) (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2))
        (ι : Fin d → Fin m × Fin l), d + 3 * l * (k + 1) + 1 ≤ m * l ∧
        (∀ x, (φ x).totalDegree ≤ 1) ∧
        ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j)) := by
    intro j h1 hr
    obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := exists_param (g j) (hg j) h1
    refine ⟨d, φ, ι, ?_, hφ, hmem⟩
    simp only [Fintype.card_prod, Fintype.card_fin] at hd
    omega
  by_cases hsmall : 3 * l * (k + 1) + 1 ≤ m * l
  · have hall : ∀ j, ∃ (d : ℕ) (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2))
        (ι : Fin d → Fin m × Fin l), d + 3 * l * (k + 1) + 1 ≤ m * l ∧
        (∀ x, (φ x).totalDegree ≤ 1) ∧
        ((1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
            ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
          3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
          ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j))) := by
      intro j
      by_cases hj : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
            ∉ Submodule.span (ZMod 2) (Set.range (g j)) ∧
          3 * l * (k + 1) < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j)))
      · obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := hpar j hj.1 hj.2
        exact ⟨d, φ, ι, hd, hφ, fun _ _ => hmem⟩
      · exact ⟨0, fun _ => 0, Fin.elim0, by omega, fun _ => by simp,
          fun h1 hr => absurd ⟨h1, hr⟩ hj⟩
    choose d φ ι hd hφ hmem using hall
    obtain ⟨f, hf, hf0, hcomb⟩ := exists_rowLinear_eq_sum_mul hl hkm hlog d hd φ hφ ι
    refine ⟨f, hf0, hf, fun j h1 hr => ?_⟩
    obtain ⟨a, ha, hdeg⟩ := hcomb j
    have hc : ∀ x, ∃ c : Fin W → ZMod 2,
        ∑ i, c i • g j i = X x - rename (ι j) (φ j x) := fun x =>
      (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hmem j h1 hr x)
    choose c hc using hc
    refine ⟨fun i => ∑ x, C (c x i) * a x, fun i => ?_, ?_⟩
    · refine totalDegree_finsetSum_le fun x _ => ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact hdeg x
    · rw [ha]
      simp_rw [← hc, Finset.mul_sum, Finset.sum_mul, smul_eq_C_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
  · refine ⟨1, one_ne_zero, ?_, fun j h1 hr => ?_⟩
    · intro u hu
      have hu' : u ∈ (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)).support := hu
      have h1 : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2)) = monomial 0 1 := rfl
      rw [h1, support_monomial] at hu'
      have : u = 0 := by simpa using hu'
      subst this
      exact ⟨by simp, fun i => by simp⟩
    · obtain ⟨d, φ, ι, hd, -, -⟩ := hpar j h1 hr
      omega
theorem chainD : ∀ (m l k D M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), 0 < m → 1 ≤ l → 1 ≤ k → 1 ≤ M → k ≤ m → (m : ℝ) * Real.log (4 * (M : ℝ)) ≤ (k : ℝ) ^ 2 → 2 * (3 * l) + 1 ≤ D → (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) (3 * l) M W g) D → ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ PEqualNP.ProofComplexity.IsRowLinear m l k f ∧ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) (k * (D + 1)) f := by
  intro m l k D M W g _hm hl hk _hM hkm hlog hD hg href
  classical
  obtain ⟨f, hf0, hfmem, hfw⟩ := exists_weight hl hkm hlog g hg
  refine ⟨f, hf0, fun u hu => hfmem (Finset.mem_coe.2 hu), ?_⟩
  refine L038 (Fin m × Fin l) (Fin M) W (3 * l) k D (bitPHPSystem m l) g f
    (fun v => Or.inl ⟨v, rfl⟩) hg (by omega) hk hD (totalDegree_le_of_mem_rowLinear hfmem)
    (fun b hb => ?_) ?_
  · by_cases h1 : (1 : MvPolynomial (Fin m × Fin l) (ZMod 2))
        ∈ Submodule.span (ZMod 2) (Set.range (g b))
    · exact Or.inl h1
    · exact Or.inr (hfw b h1 hb)
  · refine pcDerivable_mono href le_rfl ?_
    rintro p (⟨q, hq, rfl⟩ | ⟨r, rfl⟩ | ⟨j, i, rfl⟩)
    · exact Or.inl (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inl (Or.inr ⟨j, i, rfl⟩)
end C.Helpers
namespace C.Helpers
open MvPolynomial Module PEqualNP.ProofComplexity
section Axiom
variable {V : Type} [DecidableEq V] {h M W : ℕ} {e : Fin W → LinEq V}
  {cl : Fin M → LinClause V}
omit [DecidableEq V] in
theorem clausePoly_eq_prod (A : Clause V) :
    clausePoly A = ∏ l ∈ A, (1 + eqPoly ((({l.1} : Finset V), l.2) : LinEq V)) := by
  unfold clausePoly
  refine Finset.prod_congr rfl fun l _ => ?_
  rcases l with ⟨v, b⟩
  cases b
  · simp only [eqPoly, Finset.sum_singleton, Bool.false_eq_true, ite_false, C_1]
    linear_combination (-(1 : MvPolynomial V (ZMod 2))) * two_eq_zero_mvPolynomial (σ := V)
  · simp [eqPoly]
theorem block_ax_cnf {F : Set (Clause V)} {w : ℕ} (hw : ∀ A ∈ F, A.card ≤ w)
    (he : Function.Surjective e) (j : Fin M) {B : ℕ}
    (hB1 : 2 * h + w ≤ B) (hB2 : 2 * h + 1 ≤ B)
    (hax : cl j ∈ (fun A => linOfClause A) '' F) :
    PCDerivable (blockSystem (cnfSystem F) h M W (clauseInputs e cl)) B
      (blockProduct h M W (clauseInputs e cl) j) := by
  classical
  obtain ⟨A, hAF, hA⟩ := hax
  have hAw := hw A hAF
  have hdP := totalDegree_blockProduct_le (h := h) j (totalDegree_clauseInputs_le e cl j)
  set S := blockSystem (cnfSystem F) h M W (clauseInputs e cl) with hS
  set P := blockProduct h M W (clauseInputs e cl) j with hPdef
  let a : Literal V → MvPolynomial (BlockVar V h M W) (ZMod 2) :=
    fun l => rename Sum.inl (eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
  have hda : ∀ l ∈ A, (a l).totalDegree ≤ 1 := fun l _ =>
    totalDegree_rename_inl_le _ (totalDegree_eqPoly_le _)
  have ha : ∀ l ∈ A, PCDerivable S B (a l * P) := by
    intro l hl
    refine block_companion (F := cnfSystem F) (h := h) he j ?_ (B := B) hB2
    rw [← hA]
    exact Finset.mem_image.2 ⟨l, hl, rfl⟩
  have h1 := pcDerivable_prod_absorb A a P hdP ha hda (by omega)
  have hprod : rename (Sum.inl : V → BlockVar V h M W) (clausePoly A)
      = ∏ l ∈ A, (1 + a l) := by
    rw [clausePoly_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun l _ => by simp [a]
  have hdE : (∏ l ∈ A, (1 + a l)).totalDegree ≤ A.card := by
    have := totalDegree_prod_one_add_le A a hda
    omega
  have hE : PCDerivable S B (∏ l ∈ A, (1 + a l)) := by
    refine .ax (Or.inl ⟨clausePoly A, Or.inr ⟨A, hAF, rfl⟩, hprod.symm⟩) ?_
    omega
  have h2 := pcDerivable_mul_le hE P hdP hdE le_rfl (by omega)
  have h3 := h1.add h2
  have hEq : (∏ l ∈ A, (1 + a l)) * P + P + P * ∏ l ∈ A, (1 + a l) = P := by
    linear_combination char2_add_self ((∏ l ∈ A, (1 + a l)) * P)
  rw [hEq] at h3
  exact h3
end Axiom
theorem chainC_cnf {V : Type} [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V)) (w h : ℕ) (hh : 1 ≤ h) (hw : ∀ A ∈ F, A.card ≤ w)
    (href : IsLinRefutation F π) :
    ∃ (W : ℕ) (g : Fin π.length → Fin W → MvPolynomial V (ZMod 2)),
      (∀ (j : Fin π.length) (i : Fin W), (g j i).totalDegree ≤ 1) ∧
      PCRefutable (blockSystem (cnfSystem F) h π.length W g)
        (max (2 * h + w) (4 * h + 1)) := by
  obtain ⟨hder, hemp⟩ := href
  classical
  let e : Fin (Fintype.card (LinEq V)) → LinEq V := (Fintype.equivFin _).symm
  have he : Function.Surjective e := (Fintype.equivFin _).symm.surjective
  refine ⟨_, clauseInputs e π.get, totalDegree_clauseInputs_le e π.get, ?_⟩
  have hbool : ∀ v : V, X v * X v + X v ∈ cnfSystem F := fun v => Or.inl ⟨v, rfl⟩
  have inv : ∀ σ, IsLinDerivation ((fun C => linOfClause C) '' F) σ →
      (∀ C ∈ σ, C ∈ π) → ∀ C ∈ σ, ∀ j : Fin π.length, π.get j = C →
      PCDerivable (blockSystem (cnfSystem F) h π.length _ (clauseInputs e π.get))
        (max (2 * h + w) (4 * h + 1))
        (blockProduct h π.length _ (clauseInputs e π.get) j) := by
    intro σ hσ
    induction hσ with
    | nil =>
      intro _ C hC
      simp at hC
    | @ax σ A _ hA ih =>
      intro hsub C hC j hj
      rcases List.mem_cons.mp hC with rfl | hC'
      · exact block_ax_cnf hw he j (le_max_left _ _) (le_max_of_le_right (by omega))
          (by rw [hj]; exact hA)
      · exact ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC)) C hC' j hj
    | @res σ C D R _ hC hD hres ih =>
      intro hsub C' hC' j hj
      have ih' := ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC))
      rcases List.mem_cons.mp hC' with rfl | hC''
      · obtain ⟨jC, hjC⟩ := List.mem_iff_get.mp (hsub C (List.mem_cons_of_mem _ hC))
        obtain ⟨jD, hjD⟩ := List.mem_iff_get.mp (hsub D (List.mem_cons_of_mem _ hD))
        exact block_res he hbool jC jD j (le_max_right _ _) hh
          (by rw [hjC, hjD, hj]; exact hres) (ih' C hC jC hjC) (ih' D hD jD hjD)
      · exact ih' C' hC'' j hj
    | @weak σ C D _ hC himp ih =>
      intro hsub C' hC' j hj
      have ih' := ih (fun C hC => hsub C (List.mem_cons_of_mem _ hC))
      rcases List.mem_cons.mp hC' with rfl | hC''
      · obtain ⟨jC, hjC⟩ := List.mem_iff_get.mp (hsub C (List.mem_cons_of_mem _ hC))
        refine block_weak he jC j (le_max_right _ _) hh ?_ (ih' C hC jC hjC)
        intro q hq
        rw [hjC] at hq
        rw [hj]
        exact lin_choice q _ fun a ha => himp a ⟨q, hq, ha⟩
      · exact ih' C' hC'' j hj
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hemp
  have hfin := inv π hder (fun C hC => hC) ∅ hemp j hj
  have hone : blockProduct h π.length _ (clauseInputs e π.get) j = 1 := by
    have hj' : π[(j : ℕ)] = ∅ := hj
    simp [blockProduct, clauseInputs, hj']
  rw [hone] at hfin
  exact hfin
theorem exists_weight_general {σ : Type} [Fintype σ] [DecidableEq σ] {k r M W : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (g : Fin M → Fin W → MvPolynomial σ (ZMod 2))
    (hg : ∀ j i, (g j i).totalDegree ≤ 1)
    (hcount : M * (Fintype.card σ - (r + 1) + k).choose k < finrank (ZMod 2) U) :
    ∃ f ∈ U, f ≠ 0 ∧
      ∀ j, (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∃ a : Fin W → MvPolynomial σ (ZMod 2),
          (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g j i := by
  classical
  have hall : ∀ j, ∃ (d : ℕ) (φ : σ → MvPolynomial (Fin d) (ZMod 2)) (ι : Fin d → σ),
      d ≤ Fintype.card σ - (r + 1) ∧ (∀ x, (φ x).totalDegree ≤ 1) ∧
      ((1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) →
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j))) →
        ∀ x, X x - rename ι (φ x) ∈ Submodule.span (ZMod 2) (Set.range (g j))) := by
    intro j
    by_cases hj : (1 : MvPolynomial σ (ZMod 2)) ∉ Submodule.span (ZMod 2) (Set.range (g j)) ∧
        r < finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g j)))
    · obtain ⟨d, φ, ι, hd, hφ, hmem⟩ := exists_param (g j) (hg j) hj.1
      exact ⟨d, φ, ι, by omega, hφ, fun _ _ => hmem⟩
    · exact ⟨0, fun _ => 0, Fin.elim0, Nat.zero_le _, fun _ => by simp,
        fun h1 hr => absurd ⟨h1, hr⟩ hj⟩
  choose d φ ι hd hφ hmem using hall
  have hrange : ∀ j, finrank (ZMod 2)
      (LinearMap.range ((aeval (φ j)).toLinearMap ∘ₗ U.subtype))
      ≤ (Fintype.card σ - (r + 1) + k).choose k := by
    intro j
    refine le_trans (le_trans (Submodule.finrank_mono ?_)
      (finrank_restrictTotalDegree_le (ZMod 2) (d j) k))
      (Nat.choose_le_choose k (Nat.add_le_add_right (hd j) k))
    rintro _ ⟨f, rfl⟩
    rw [mem_restrictTotalDegree]
    exact (totalDegree_aeval_le (φ j) (hφ j) f.1).trans (hU f.1 f.2)
  obtain ⟨v, hv, hzero⟩ := exists_ne_zero_forall_eq_zero
    (fun j => (aeval (φ j)).toLinearMap ∘ₗ U.subtype)
    (fun _ => (Fintype.card σ - (r + 1) + k).choose k) hrange
    (by simpa using hcount)
  refine ⟨v.1, v.2, fun h0 => hv (Subtype.ext h0), fun j h1 hr => ?_⟩
  have hcomp : aeval (fun x => rename (ι j) (φ j x))
      = ((rename (ι j)).comp (aeval (φ j)) : MvPolynomial σ (ZMod 2) →ₐ[ZMod 2] _) := by
    apply algHom_ext
    intro x
    simp
  have hker : aeval (fun x => rename (ι j) (φ j x)) v.1 = 0 := by
    have hz : aeval (φ j) v.1 = 0 := hzero j
    rw [hcomp, AlgHom.comp_apply, hz, map_zero]
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun x => rename (ι j) (φ j x))
    (fun x => (totalDegree_rename_le _ _).trans (hφ j x)) v.1 k (hU v.1 v.2)
  rw [hker, sub_zero] at ha
  have hc : ∀ x, ∃ c : Fin W → ZMod 2,
      ∑ i, c i • g j i = X x - rename (ι j) (φ j x) := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hmem j h1 hr x)
  choose c hc using hc
  refine ⟨fun i => ∑ x, C (c x i) * a x, fun i => ?_, ?_⟩
  · refine totalDegree_finsetSum_le fun x _ => ?_
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hdeg x
  · rw [ha]
    simp_rw [← hc, Finset.mul_sum, Finset.sum_mul, smul_eq_C_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => by ring
theorem generalCriterion : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w h k : ℕ) (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))), 1 ≤ h → 1 ≤ k → (∀ C ∈ F, C.card ≤ w) → PEqualNP.ProofComplexity.IsLinRefutation F π → (∀ f ∈ U, f.totalDegree ≤ k) → (∀ f ∈ U, f ≠ 0 → ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) (k * (max (2 * h + w) (4 * h + 1) + 1)) f) → Module.finrank (ZMod 2) U ≤ π.length * (Fintype.card V - (h * (k + 1) + 1) + k).choose k := by
  intro V _ _ F π w h k U hh hk hw href hU hnot
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨W, g, hg, hrefut⟩ := chainC_cnf F π w h hh hw href
  obtain ⟨f, hfU, hf0, hfw⟩ := exists_weight_general (r := h * (k + 1)) U hU g hg hlt
  refine hnot f hfU hf0 ?_
  refine L038 V (Fin π.length) W h k (max (2 * h + w) (4 * h + 1)) (cnfSystem F) g f
    (fun v => Or.inl ⟨v, rfl⟩) hg hh hk (le_max_of_le_right (by omega)) (hU f hfU)
    (fun b hb => ?_) ?_
  · by_cases h1 : (1 : MvPolynomial V (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b))
    · exact Or.inl h1
    · exact Or.inr (hfw b h1 hb)
  · refine pcDerivable_mono hrefut le_rfl ?_
    rintro p (⟨q, hq, rfl⟩ | ⟨r, rfl⟩ | ⟨j, i, rfl⟩)
    · exact Or.inl (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr ⟨r, rfl⟩
    · exact Or.inl (Or.inr ⟨j, i, rfl⟩)
end C.Helpers
namespace C.DegSizePlan
open MvPolynomial Module PEqualNP.ProofComplexity C.Helpers
section Abstract
variable {σ : Type}
def pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) where
  carrier := {p | PCDerivable A D p}; add_mem' := fun hp hq => PCDerivable.add hp hq
  zero_mem' := PCDerivable.zero
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa using (PCDerivable.zero : PCDerivable A D 0)
    · simpa using hp
theorem mem_pcClosure {A : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    {p : MvPolynomial σ (ZMod 2)} : p ∈ pcClosure A D ↔ PCDerivable A D p := Iff.rfl
structure DegClosed (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ) : Prop where
  two_le : 2 ≤ D
  mulX : ∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ C → f.totalDegree + 1 ≤ D → X v * f ∈ C
  bool : ∀ v : σ, X v * X v + X v ∈ C
theorem degClosed_pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) (hD : 2 ≤ D)
    (hA : ∀ v : σ, X v * X v + X v ∈ A) : DegClosed (pcClosure A D) D where
  two_le := hD
  mulX := fun v f hf hdeg => PCDerivable.mulX v hf
    ((totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega))
  bool := fun v => PCDerivable.ax (hA v) (by
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · rw [totalDegree_X]; omega
    · rw [totalDegree_X]; omega)
noncomputable abbrev polyLE (σ : Type) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictTotalDegree σ (ZMod 2) k
noncomputable def errKer (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  polyLE σ k ⊓ ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_errKer {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C M k ↔ f.totalDegree ≤ k ∧ ∀ m ∈ M, m * f ∈ C := by
  simp [errKer, polyLE, mem_restrictTotalDegree]
noncomputable def errRank (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) (errKer C M k)
noncomputable def zMul (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))) :
    Set (MvPolynomial σ (ZMod 2)) := (fun g => P * g) '' G
def numMono (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j
noncomputable def hCodim (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ K) - finrank (ZMod 2) ↥(C ⊓ polyLE σ K)
noncomputable def eta (n K : ℕ) : ℝ := (numMono n (K - 1) : ℝ) / (2 * numMono n K)
end Abstract
end C.DegSizePlan
namespace C.DegSizeSim
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem monomial_mul_mem (hC : DegClosed C D) (a : σ →₀ ℕ) :
    ∀ {g : MvPolynomial σ (ZMod 2)}, g ∈ C → (a.sum fun _ e => e) + g.totalDegree ≤ D →
      monomial a 1 * g ∈ C := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      exact hC.mulX j _ (ih hg (by omega)) (by omega)
theorem absorb_le (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ C) {a b : ℕ} (hg : g.totalDegree ≤ a)
    (hfd : f.totalDegree ≤ b) (hB : a + b ≤ D) : g * f ∈ C := by
  have hq : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine Submodule.sum_mem _ fun u hu => ?_
  have hc : g.coeff u = 1 := by
    have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
    generalize g.coeff u = c at h0
    revert h0; revert c; decide
  rw [hc]
  have : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact monomial_mul_mem hC u hf (by omega)
theorem absorb : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C :=
  fun _ _ _ hC _ g hf hdeg => absorb_le hC g hf le_rfl le_rfl hdeg
theorem idem_sum {ι : Type} (s : Finset ι) (h : ι → MvPolynomial σ (ZMod 2))
    (hh : ∀ i ∈ s, h i * h i + h i ∈ C) :
    (∑ i ∈ s, h i) * (∑ i ∈ s, h i) + ∑ i ∈ s, h i ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have e : (h i + ∑ x ∈ s, h x) * (h i + ∑ x ∈ s, h x) + (h i + ∑ x ∈ s, h x)
        = (h i * h i + h i) + ((∑ x ∈ s, h x) * (∑ x ∈ s, h x) + ∑ x ∈ s, h x) := by
      linear_combination char2_add_self (h i * ∑ x ∈ s, h x)
    rw [e]
    exact C.add_mem (hh i (Finset.mem_insert_self i s))
      (ih fun k hk => hh k (Finset.mem_insert_of_mem hk))
theorem exponent_le_one (u : σ →₀ ℕ) (hu : (u.sum fun _ e => e) ≤ 1) :
    u = 0 ∨ ∃ v, u = Finsupp.single v 1 := by
  classical
  by_cases h0 : u = 0
  · exact Or.inl h0
  right
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr h0
  refine ⟨v, ?_⟩
  have hsum : u v + ∑ x ∈ u.support.erase v, u x ≤ 1 := by
    rw [Finset.add_sum_erase _ _ hv]
    exact hu
  have hv1 : u v ≠ 0 := Finsupp.mem_support_iff.mp hv
  have hrest : ∑ x ∈ u.support.erase v, u x = 0 := by omega
  ext x
  by_cases hx : x = v
  · subst hx
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_eq_of_ne hx]
    by_contra hne
    have hmem : x ∈ u.support.erase v :=
      Finset.mem_erase.mpr ⟨hx, Finsupp.mem_support_iff.mpr hne⟩
    exact hne ((Finset.sum_eq_zero_iff.mp hrest) x hmem)
theorem affine_idem' (hC : DegClosed C D) {g : MvPolynomial σ (ZMod 2)}
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  have hsum : g = ∑ u ∈ g.support, monomial u (g.coeff u) := g.as_sum
  have key := idem_sum (C := C) g.support (fun u => monomial u (g.coeff u)) (fun u hu => by
    have hc : g.coeff u = 1 := by
      have h0 : g.coeff u ≠ 0 := mem_support_iff.mp hu
      generalize g.coeff u = c at h0
      revert h0; revert c; decide
    rw [hc]
    have hdu : (u.sum fun _ e => e) ≤ 1 := (le_totalDegree hu).trans hg
    rcases exponent_le_one u hdu with rfl | ⟨v, rfl⟩
    · have h1 : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [h1, one_mul, char2_add_self]
      exact C.zero_mem
    · exact hC.bool v)
  rw [← hsum] at key
  exact key
theorem affine_idem : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ),
    DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C :=
  fun _ _ _ hC _ hg => affine_idem' hC hg
theorem totalDegree_one_add_le {p : MvPolynomial σ (ZMod 2)} (h : p.totalDegree ≤ 1) :
    (1 + p).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    (ha : ∀ u ∈ s, (a u).totalDegree ≤ 1) : (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := 1) ha
  omega
theorem prod_absorb (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ 1) (hB : s.card + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ 1 := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ 1 :=
      totalDegree_one_add_le (hdeg u (Finset.mem_insert_self u s))
    have h2 := absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  have := totalDegree_prod_le Finset.univ qs (fun j _ => h j)
  simpa using this
theorem transfer' (hC : DegClosed C D) {K t r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem g hg' =>
      rw [← mul_assoc]
      exact hg g hg'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [add_mul]
      exact C.add_mem hx hy
    | smul c x _ hx =>
      rcases zmod2_cases c with rfl | rfl
      · simp
      · simpa using hx
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j => totalDegree_span_le hG (hqs j)
  have h1 := prod_absorb hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h2 := absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer : ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg => transfer' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} [Fintype V] [DecidableEq V]
  {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t : ℕ}
  {f : MvPolynomial V (ZMod 2)}
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_eqImage_le (L : LinClause V) :
    ∀ g ∈ (fun q => eqPoly q) '' (↑L : Set (LinEq V)), g.totalDegree ≤ 1 := by
  rintro _ ⟨q, _, rfl⟩
  exact totalDegree_eqPoly_le q
omit [Fintype V] [DecidableEq V] in
theorem totalDegree_clausePoly_le (A : Clause V) : (clausePoly A).totalDegree ≤ A.card := by
  rw [clausePoly_eq_prod]
  exact totalDegree_prod_le A _ fun l _ => totalDegree_eqPoly_le _
omit [Fintype V] in
theorem step_ax (hC : DegClosed C D) (A : Clause V) {w : ℕ} (hA : clausePoly A ∈ C)
    (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2)
      ((fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ q ∈ linOfClause A, (∏ j, (1 + qs j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  have hdq : ∀ j, (qs j).totalDegree ≤ 1 := fun j =>
    totalDegree_span_le (totalDegree_eqImage_le _) (hqs j)
  have hQ : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t + K :=
    totalDegree_mul_le' (totalDegree_appr_le qs hdq) hf
  have h1 := prod_absorb hC A
    (fun l : Literal V => eqPoly ((({l.1} : Finset V), l.2) : LinEq V))
    ((∏ j, (1 + qs j)) * f) hQ
    (fun l hl => by
      have := hH _ (Finset.mem_image.2 ⟨l, hl, rfl⟩)
      have e : eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * ((∏ j, (1 + qs j)) * f)
          = (∏ j, (1 + qs j)) * eqPoly ((({l.1} : Finset V), l.2) : LinEq V) * f := by ring
      rw [e]
      exact this)
    (fun l _ => totalDegree_eqPoly_le _) (by omega)
  rw [← clausePoly_eq_prod] at h1
  have h2 := absorb_le hC ((∏ j, (1 + qs j)) * f) hA hQ (totalDegree_clausePoly_le A)
    (by omega)
  have h3 := C.add_mem h1 h2
  have e : clausePoly A * ((∏ j, (1 + qs j)) * f) + (∏ j, (1 + qs j)) * f
      + (∏ j, (1 + qs j)) * f * clausePoly A = (∏ j, (1 + qs j)) * f := by
    linear_combination char2_add_self (clausePoly A * ((∏ j, (1 + qs j)) * f))
  rwa [e] at h3
theorem step_weak (hC : DegClosed C D) (L M : LinClause V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB1 : K + 2 * t ≤ D) (hB2 : K + t + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinClauseSat a L → LinClauseSat a M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨J, hJ, hcase⟩ := lin_choice q M fun a ha => himp a ⟨q, hq, ha⟩
  have hsum : (∑ d ∈ J, eqPoly d) * (∏ j, (1 + qM j)) * f ∈ C := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun d hd => ?_
    have e : eqPoly d * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * eqPoly d * f := by ring
    rw [e]
    exact hHM d (hJ hd)
  rcases hcase with h1 | h2
  · rw [h1, one_mul] at hsum
    have := absorb_le hC (eqPoly q) hsum (totalDegree_eqPoly_le q)
      (totalDegree_mul_le' hdM hf) (by omega)
    rw [mul_assoc]
    exact this
  · rw [h2] at hsum
    exact hsum
omit [Fintype V] in
theorem step_half (hC : DegClosed C D) (L M : LinClause V) (q0 : LinEq V)
    (e' : MvPolynomial V (ZMod 2)) (qL qM : Fin t → MvPolynomial V (ZMod 2))
    (hqL : ∀ j, qL j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D) (he' : e'.totalDegree ≤ 1)
    (hbad : eqPoly q0 * e' * ((∏ j, (1 + qM j)) * f) ∈ C)
    (hsub : ∀ q ∈ L, q ≠ q0 → q ∈ M)
    (hPL : (∏ j, (1 + qL j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    e' * (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hdR : (e' * ∏ j, (1 + qM j)).totalDegree ≤ 1 + t := totalDegree_mul_le' he' hdM
  refine transfer' hC qL (totalDegree_eqImage_le L) hqL hf hdR (by omega) hPL ?_
  rintro _ ⟨q, hq, rfl⟩
  by_cases hq0 : q = q0
  · subst hq0
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = eqPoly q * e' * ((∏ j, (1 + qM j)) * f) := by ring
    rw [e]
    exact hbad
  · have hmem := hHM q (hsub q hq hq0)
    have hd : ((∏ j, (1 + qM j)) * eqPoly q * f).totalDegree ≤ t + 1 + K :=
      totalDegree_mul_le' (totalDegree_mul_le' hdM (totalDegree_eqPoly_le q)) hf
    have := absorb_le hC e' hmem he' hd (by omega)
    have e : eqPoly q * (e' * ∏ j, (1 + qM j)) * f
        = e' * ((∏ j, (1 + qM j)) * eqPoly q * f) := by ring
    rw [e]
    exact this
omit [Fintype V] in
theorem step_res (hC : DegClosed C D) (L1 L2 M : LinClause V)
    (q1 q2 qM : Fin t → MvPolynomial V (ZMod 2))
    (hq1 : ∀ j, q1 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L1 : Set (LinEq V))))
    (hq2 : ∀ j, q2 j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L2 : Set (LinEq V))))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑M : Set (LinEq V))))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t + 2 ≤ D)
    (hres : IsLinResolvent L1 L2 M)
    (hP1 : (∏ j, (1 + q1 j)) * f ∈ C) (hP2 : (∏ j, (1 + q2 j)) * f ∈ C)
    (hHM : ∀ q ∈ M, (∏ j, (1 + qM j)) * eqPoly q * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  obtain ⟨g, hg1, hg2, rfl⟩ := hres
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t :=
    totalDegree_appr_le qM fun j => totalDegree_span_le (totalDegree_eqImage_le _) (hqM j)
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t + K := totalDegree_mul_le' hdM hf
  have he : eqPoly ((g, false) : LinEq V) = eqPoly ((g, true) : LinEq V) + 1 := by
    simp [eqPoly]
  have hd1 : (eqPoly ((g, true) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hd0 : (eqPoly ((g, false) : LinEq V)).totalDegree ≤ 1 := totalDegree_eqPoly_le _
  have hidem := affine_idem' hC hd1
  have hdi : (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
      + eqPoly ((g, true) : LinEq V)).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hd1 hd1) (by omega))
  have hbad := absorb_le hC ((∏ j, (1 + qM j)) * f) hidem hQ hdi (by omega)
  have hA := step_half hC L1 _ (g, false) (eqPoly ((g, true) : LinEq V)) q1 qM hq1 hqM hf hB
    hd1
    (by
      have e : eqPoly ((g, false) : LinEq V) * eqPoly ((g, true) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP1 hHM
  have hB' := step_half hC L2 _ (g, true) (eqPoly ((g, false) : LinEq V)) q2 qM hq2 hqM hf hB
    hd0
    (by
      have e : eqPoly ((g, true) : LinEq V) * eqPoly ((g, false) : LinEq V)
            * ((∏ j, (1 + qM j)) * f)
          = (∏ j, (1 + qM j)) * f * (eqPoly ((g, true) : LinEq V) * eqPoly ((g, true) : LinEq V)
            + eqPoly ((g, true) : LinEq V)) := by
        rw [he]; ring
      rw [e]
      exact hbad)
    (fun q hq hne => Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hq⟩)) hP2 hHM
  have h3 := C.add_mem hA hB'
  have e : eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f
      + eqPoly ((g, false) : LinEq V) * (∏ j, (1 + qM j)) * f = (∏ j, (1 + qM j)) * f := by
    rw [he]
    linear_combination char2_add_self (eqPoly ((g, true) : LinEq V) * (∏ j, (1 + qM j)) * f)
  rwa [e] at h3
end Lines
theorem simulation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinDerivation ((fun A => linOfClause A) '' F) π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f) := by
  intro V _ _ F π w D K t f qs hw hder hB hf
  have hB1 : K + (2 * t + 2) ≤ D := (Nat.add_le_add_left (le_max_left _ _) K).trans hB
  have hB2 : K + (t + w) ≤ D := (Nat.add_le_add_left (le_max_right _ _) K).trans hB
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ (by omega) fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinClause V), IsLinDerivation ((fun A => linOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2)
        ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
      (∀ L ∈ ρ, ∀ q ∈ L, (∏ j, (1 + qs L j)) * eqPoly q * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((totalDegree_clausePoly_le A).trans (by omega))
        exact step_ax hC A hmem hAw (qs (linOfClause A))
          (hs _ List.mem_cons_self) hf (by omega) (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @res ρ L1 L2 M _ h1 h2 hres ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_res hC L1 L2 L (qs L1) (qs L2) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf (by omega) hres (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M _ h1 himp ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact step_weak hC L1 L (qs L1) (qs L)
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf (by omega)
          (by omega) himp (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH
theorem simulation_refutation : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V))
    (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    PCDerivable (cnfSystem F) D f := by
  intro V _ _ F π w D K t f qs hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation V F π w D K t f qs hw hder hB hf hs hH ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa using this
  simpa [hq] using h
end C.DegSizeSim
namespace C.LinKPlan
open MvPolynomial Module PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
section Vanish
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem mem_of_boolDerivable (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hp : PCDerivable (BoolVanish.boolAxioms σ) D p) : p ∈ C := by
  induction hp with
  | ax hp _ =>
    obtain ⟨v, rfl⟩ := hp
    exact hC.bool v
  | zero => exact C.zero_mem
  | add _ _ ih1 ih2 => exact C.add_mem ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases h0 : p = 0
    · subst h0
      simp
    · refine hC.mulX j p ih ?_
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) h0, totalDegree_X] at hdeg
      omega
theorem vanish_mem (hC : DegClosed C D) {p : MvPolynomial σ (ZMod 2)}
    (hd : p.totalDegree ≤ D) (hv : ∀ x : σ → ZMod 2, eval x p = 0) : p ∈ C :=
  mem_of_boolDerivable hC
    (BoolVanish.vanish_derivable σ (BoolVanish.boolAxioms σ) D p (fun v => ⟨v, rfl⟩) hd hv)
theorem idem_mul (hC : DegClosed C D) (g h : MvPolynomial σ (ZMod 2)) {b e : ℕ}
    (hh : h.totalDegree ≤ b) (hg : g.totalDegree ≤ e) (hB : b + 2 * e ≤ D) :
    h * (g * g + g) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 : (g * g + g).totalDegree ≤ e + e :=
      (totalDegree_add _ _).trans (max_le (totalDegree_mul_le' hg hg) (by omega))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have : ∀ c : ZMod 2, c * c + c = 0 := by decide
    rw [this, mul_zero]
end Vanish
noncomputable def termPoly {V : Type} (T : LinTerm V) : MvPolynomial V (ZMod 2) :=
  ∏ e ∈ T, eqPoly e
section Terms
variable {V : Type}
theorem termPoly_empty : termPoly (∅ : LinTerm V) = 1 := by
  simp [termPoly]
theorem termPoly_singleton (q : LinEq V) : termPoly ({q} : LinTerm V) = eqPoly q := by
  simp [termPoly]
theorem totalDegree_termPoly_le (T : LinTerm V) : (termPoly T).totalDegree ≤ T.card := by
  unfold termPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ e ∈ T, (eqPoly e).totalDegree ≤ ∑ _e ∈ T, 1 :=
        Finset.sum_le_sum fun e _ => totalDegree_eqPoly_le e
    _ = T.card := by simp
theorem eval_eqPoly (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = ∑ v ∈ q.1, x v + (if q.2 = true then 0 else 1) := by
  unfold eqPoly
  rw [map_add, map_sum, eval_C]
  simp only [eval_X]
theorem eval_eqPoly_eq_one_iff (x : V → ZMod 2) (q : LinEq V) :
    eval x (eqPoly q) = 1 ↔ LinEqSat (fun v => decide (x v = 1)) q := by
  rw [eval_eqPoly, linEqSat_iff_sum]
theorem eval_eqPoly_neg (x : V → ZMod 2) (e : LinEq V) :
    eval x (eqPoly (negLinEq e)) = eval x (eqPoly e) + 1 := by
  rw [eval_eqPoly, eval_eqPoly]
  rcases e with ⟨f, b⟩
  show ∑ v ∈ f, x v + (if (!b) = true then 0 else 1)
    = ∑ v ∈ f, x v + (if b = true then 0 else 1) + 1
  generalize ∑ v ∈ f, x v = s
  cases b
  · revert s
    decide
  · revert s
    decide
theorem eval_termPoly_of_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 1 := by
  unfold termPoly
  rw [map_prod]
  exact Finset.prod_eq_one fun e he => (eval_eqPoly_eq_one_iff x e).mpr (h e he)
theorem eval_termPoly_of_not_sat (x : V → ZMod 2) (T : LinTerm V)
    (h : ¬ LinTermSat (fun v => decide (x v = 1)) T) : eval x (termPoly T) = 0 := by
  obtain ⟨e, he, hne⟩ : ∃ e ∈ T, ¬ LinEqSat (fun v => decide (x v = 1)) e := by
    by_contra hcon
    exact h fun e he => by_contra fun hn => hcon ⟨e, he, hn⟩
  unfold termPoly
  rw [map_prod]
  refine Finset.prod_eq_zero he ?_
  rcases zmod2_cases (eval x (eqPoly e)) with h0 | h1
  · exact h0
  · exact absurd ((eval_eqPoly_eq_one_iff x e).mp h1) hne
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_term_mul (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T.card + S.card ≤ D) :
    h * (termPoly T + termPoly T * termPoly S) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have hT := totalDegree_termPoly_le T
    have hS := totalDegree_termPoly_le S
    have h1 : (termPoly T + termPoly T * termPoly S).totalDegree ≤ T.card + S.card :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hS))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [eval_termPoly_of_sat x T hT, eval_termPoly_of_sat x S (himp _ hT)]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem weak_term (hC : DegClosed C D) (T S : LinTerm V)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S) (hB : T.card + S.card ≤ D) :
    termPoly T + termPoly T * termPoly S ∈ C := by
  have h := weak_term_mul hC T S himp 1 (b := 0) (by simp) (by omega)
  rwa [one_mul] at h
theorem unsat_term_mul (hC : DegClosed C D) (T : LinTerm V)
    (hT : ∀ a : V → Bool, ¬ LinTermSat a T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card ≤ D) :
    h * termPoly T ∈ C := by
  refine vanish_mem hC ((totalDegree_mul_le' hh (totalDegree_termPoly_le T)).trans hB) ?_
  intro x
  rw [map_mul, eval_termPoly_of_not_sat x T (hT _), mul_zero]
theorem term_neg_mul (hC : DegClosed C D) (T : LinTerm V) (e : LinEq V) (he : e ∈ T)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b) (hB : b + T.card + 1 ≤ D) :
    h * (termPoly T * eqPoly (negLinEq e)) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_mul_le' (totalDegree_termPoly_le T)
      (totalDegree_eqPoly_le (negLinEq e))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_mul, eval_eqPoly_neg]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · rw [(eval_eqPoly_eq_one_iff x e).mpr (hT e he)]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, mul_zero, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem term_union_mul [DecidableEq V] (hC : DegClosed C D) (T₁ T₂ : LinTerm V)
    (h : MvPolynomial V (ZMod 2)) {b : ℕ} (hh : h.totalDegree ≤ b)
    (hB : b + T₁.card + T₂.card ≤ D) :
    h * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂) ∈ C := by
  refine vanish_mem hC ?_ ?_
  · have h1 := totalDegree_termPoly_le T₁
    have h2 := totalDegree_termPoly_le T₂
    have h3 := (totalDegree_termPoly_le (T₁ ∪ T₂)).trans (Finset.card_union_le T₁ T₂)
    have h4 : (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂).totalDegree
        ≤ T₁.card + T₂.card :=
      (totalDegree_add _ _).trans (max_le h3 (totalDegree_mul_le' h1 h2))
    exact (totalDegree_mul_le' hh h4).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    have h11 : (1 : ZMod 2) + 1 * 1 = 0 := by decide
    by_cases h1 : LinTermSat (fun v => decide (x v = 1)) T₁
    · by_cases h2 : LinTermSat (fun v => decide (x v = 1)) T₂
      · have hu : LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := by
          intro q hq
          rcases Finset.mem_union.mp hq with hq | hq
          · exact h1 q hq
          · exact h2 q hq
        rw [eval_termPoly_of_sat x _ hu, eval_termPoly_of_sat x _ h1,
          eval_termPoly_of_sat x _ h2, h11, mul_zero]
      · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
          h2 fun q hq => hu q (Finset.mem_union_right _ hq)
        rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h2]
        simp
    · have hu : ¬ LinTermSat (fun v => decide (x v = 1)) (T₁ ∪ T₂) := fun hu =>
        h1 fun q hq => hu q (Finset.mem_union_left _ hq)
      rw [eval_termPoly_of_not_sat x _ hu, eval_termPoly_of_not_sat x _ h1]
      simp
end Terms
section ChoiceSec
theorem span_image_sum {ι M : Type} [AddCommGroup M] [Module (ZMod 2) M] (w : ι → M)
    (s : Finset ι) {y : M} (hy : y ∈ Submodule.span (ZMod 2) (w '' (↑s : Set ι))) :
    ∃ I : Finset ι, I ⊆ s ∧ y = ∑ i ∈ I, w i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hy
  obtain ⟨lc, hlc, rfl⟩ := hy
  refine ⟨lc.support, fun d hd => Finset.mem_coe.mp ((Finsupp.mem_supported _ _).mp hlc hd), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h0 : lc d ≠ 0 := Finsupp.mem_support_iff.mp hd
  have h1 : lc d = 1 := by
    generalize lc d = x at h0
    revert x
    decide
  rw [h1, one_smul]
variable {V : Type} [Fintype V] [DecidableEq V]
theorem term_choice (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ ∃ I : Finset (LinEq V), I ⊆ T ∧
      ∑ e ∈ I, (eqPoly e + 1) + ∑ d ∈ J, eqPoly d = 1 := by
  have hmem : ((0, 1) : (V → ZMod 2) × ZMod 2) ∈ Submodule.span (ZMod 2)
      (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
        ∪ (eqVec '' (↑Q : Set (LinEq V)))) := by
    by_contra hx
    obtain ⟨φ, hφx, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hvan : ∀ z ∈ Submodule.span (ZMod 2)
        (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
          ∪ (eqVec '' (↑Q : Set (LinEq V)))), φ z = 0 := by
      intro z hz
      have : φ z ∈ Submodule.map φ (Submodule.span (ZMod 2)
          (((fun e : LinEq V => eqVec e + (0, 1)) '' (↑T : Set (LinEq V)))
            ∪ (eqVec '' (↑Q : Set (LinEq V))))) :=
        Submodule.mem_map_of_mem hz
      rw [hφ] at this
      simpa using this
    have h1 : φ (0, 1) = 1 := by
      generalize φ (0, 1) = x at hφx
      revert x
      decide
    have hT : LinTermSat (fun v => decide (φ (fun j => if v = j then 1 else 0, 0) = 1)) T := by
      intro e he
      rw [linEqSat_iff_sum, ← dual_apply φ h1]
      have := hvan _ (Submodule.subset_span (Or.inl ⟨e, Finset.mem_coe.mpr he, rfl⟩))
      rw [map_add, h1] at this
      generalize φ (eqVec e) = x at this
      revert x
      decide
    obtain ⟨d, hd, hsat⟩ := himp _ hT
    rw [linEqSat_iff_sum, ← dual_apply φ h1] at hsat
    have := hvan _ (Submodule.subset_span (Or.inr ⟨d, Finset.mem_coe.mpr hd, rfl⟩))
    rw [this] at hsat
    exact zero_ne_one hsat
  rw [Submodule.span_union, Submodule.mem_sup] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨I, hI, rfl⟩ := span_image_sum (fun e : LinEq V => eqVec e + (0, 1)) T hy
  obtain ⟨J, hJ, rfl⟩ := span_image_sum eqVec Q hz
  refine ⟨J, hJ, I, hI, ?_⟩
  have hP := congrArg affPoly hyz
  simp only [map_add, map_sum, affPoly_eqVec, affPoly_one] at hP
  exact hP
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_disj_mul (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, I, hI, hid⟩ := term_choice T Q himp
  refine ⟨J, hJ, fun h b hh hB => vanish_mem hC ?_ ?_⟩
  · have hT := totalDegree_termPoly_le T
    have hs : (∑ d ∈ J, eqPoly d).totalDegree ≤ 1 :=
      totalDegree_finsetSum_le fun d _ => totalDegree_eqPoly_le d
    have h1 : (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d).totalDegree ≤ T.card + 1 :=
      (totalDegree_add _ _).trans (max_le (by omega) (totalDegree_mul_le' hT hs))
    exact (totalDegree_mul_le' hh h1).trans (by omega)
  · intro x
    rw [map_mul, map_add, map_mul]
    by_cases hT : LinTermSat (fun v => decide (x v = 1)) T
    · have h0 : eval x (∑ e ∈ I, (eqPoly e + 1)) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun e he => ?_
        rw [map_add, map_one, (eval_eqPoly_eq_one_iff x e).mpr (hT e (hI he))]
        decide
      have h1 : eval x (∑ d ∈ J, eqPoly d) = 1 := by
        have := congrArg (eval x) hid
        rw [map_add, h0, zero_add, map_one] at this
        exact this
      rw [eval_termPoly_of_sat x T hT, h1]
      have : (1 : ZMod 2) + 1 * 1 = 0 := by decide
      rw [this, mul_zero]
    · rw [eval_termPoly_of_not_sat x T hT]
      simp
theorem weak_disj (hC : DegClosed C D) (T : LinTerm V) (Q : Finset (LinEq V))
    (himp : ∀ a : V → Bool, LinTermSat a T → ∃ q ∈ Q, LinEqSat a q) (hB : T.card + 1 ≤ D) :
    ∃ J : Finset (LinEq V), J ⊆ Q ∧ termPoly T + termPoly T * ∑ d ∈ J, eqPoly d ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T Q himp
  refine ⟨J, hJ, ?_⟩
  have h := hmul 1 0 (by simp) (by omega)
  rwa [one_mul] at h
theorem weak_disj_line (hC : DegClosed C D) (T : LinTerm V) (M : LinKLine V)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q) :
    ∃ J : Finset (LinEq V), (∀ d ∈ J, ({d} : LinTerm V) ∈ M) ∧
      ∀ (h : MvPolynomial V (ZMod 2)) (b : ℕ), h.totalDegree ≤ b → b + T.card + 1 ≤ D →
        h * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d) ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_mul hC T
    ((M.biUnion id).filter (fun q => ({q} : LinTerm V) ∈ M))
    (fun a ha => by
      obtain ⟨q, hq, hs⟩ := himp a ha
      exact ⟨q, Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩, hq⟩, hs⟩)
  exact ⟨J, fun d hd => (Finset.mem_filter.mp (hJ hd)).2, hmul⟩
end ChoiceSec
noncomputable def lineInputs {V : Type} (L : LinKLine V) : Set (MvPolynomial V (ZMod 2)) :=
  (fun T => termPoly T) '' (↑L : Set (LinTerm V))
noncomputable def etaK (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
theorem etaK_one (n K : ℕ) : etaK n K 1 = eta n K := rfl
section Abstract
end Abstract
end C.LinKPlan
namespace C.Helpers
namespace MonoRank
open Finset MvPolynomial
open scoped FinsetFamily MonomialOrder
section Combinatorial
variable {σ : Type*} [DecidableEq σ] [Fintype σ]
theorem slice_succ_mul_le (𝒜 : Finset (Finset σ)) (h : IsLowerSet (𝒜 : Set (Finset σ)))
    (j : ℕ) :
    (j + 1) * (Finset.slice 𝒜 (j + 1)).card ≤ (Fintype.card σ - j) * (Finset.slice 𝒜 j).card := by
  rcases Nat.lt_or_ge (Fintype.card σ) (j + 1) with hj | hj
  · have h0 : Finset.slice 𝒜 (j + 1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    simp [h0]
  · have h1 := Finset.local_lubell_yamamoto_meshalkin_inequality_mul
      (Finset.sized_slice (𝒜 := 𝒜) (r := j + 1))
    have hsub : ∂ (Finset.slice 𝒜 (j + 1)) ⊆ Finset.slice 𝒜 j := by
      intro t ht
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.1 ht
      rw [Finset.mem_slice] at hs ⊢
      refine ⟨h (Finset.erase_subset a s) (Finset.mem_coe.2 hs.1), ?_⟩
      rw [Finset.card_erase_of_mem ha, hs.2]
      rfl
    have h2 := Finset.card_le_card hsub
    have h3 : Fintype.card σ - (j + 1) + 1 = Fintype.card σ - j := by omega
    rw [h3] at h1
    calc (j + 1) * (Finset.slice 𝒜 (j + 1)).card = (Finset.slice 𝒜 (j + 1)).card * (j + 1) := Nat.mul_comm _ _
      _ ≤ (∂ (Finset.slice 𝒜 (j + 1))).card * (Fintype.card σ - j) := h1
      _ ≤ (Finset.slice 𝒜 j).card * (Fintype.card σ - j) := Nat.mul_le_mul_right _ h2
      _ = (Fintype.card σ - j) * (Finset.slice 𝒜 j).card := Nat.mul_comm _ _
theorem slice_succ_mul_choose_le (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (j : ℕ) :
    (Finset.slice 𝒜 (j + 1)).card * (Fintype.card σ).choose j
      ≤ (Finset.slice 𝒜 j).card * (Fintype.card σ).choose (j + 1) := by
  have h1 := slice_succ_mul_le 𝒜 h j
  have h2 := Nat.choose_succ_right_eq (Fintype.card σ) j
  refine Nat.le_of_mul_le_mul_left (?_ : (j + 1) * _ ≤ (j + 1) * _) (Nat.succ_pos j)
  calc (j + 1) * ((Finset.slice 𝒜 (j + 1)).card * (Fintype.card σ).choose j)
      = ((j + 1) * (Finset.slice 𝒜 (j + 1)).card) * (Fintype.card σ).choose j := by ring
    _ ≤ ((Fintype.card σ - j) * (Finset.slice 𝒜 j).card) * (Fintype.card σ).choose j :=
        Nat.mul_le_mul_right _ h1
    _ = (Finset.slice 𝒜 j).card * ((Fintype.card σ).choose j * (Fintype.card σ - j)) := by ring
    _ = (Finset.slice 𝒜 j).card * ((Fintype.card σ).choose (j + 1) * (j + 1)) := by rw [h2]
    _ = (j + 1) * ((Finset.slice 𝒜 j).card * (Fintype.card σ).choose (j + 1)) := by ring
omit [DecidableEq σ] [Fintype σ] in
theorem mediant_partial_sums (b c : ℕ → ℕ) (k : ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (h : ∀ j ≤ k, b (j + 1) * c j ≤ b j * c (j + 1)) :
    (∑ j ∈ range (k + 2), b j) * (∑ j ∈ range (k + 1), c j)
      ≤ (∑ j ∈ range (k + 1), b j) * (∑ j ∈ range (k + 2), c j) := by
  have key : ∀ l, l ≤ k + 1 → ∀ j ≤ l, b l * c j ≤ b j * c l := by
    intro l
    induction l with
    | zero =>
      intro _ j hj
      obtain rfl : j = 0 := by omega
      exact le_rfl
    | succ l ih =>
      intro hl j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · exact le_rfl
      have i1 := ih (by omega) j (by omega)
      have i2 := h l (by omega)
      have hp := hc l (by omega)
      refine Nat.le_of_mul_le_mul_left (?_ : c l * _ ≤ c l * _) hp
      calc c l * (b (l + 1) * c j) = (b (l + 1) * c l) * c j := by ring
        _ ≤ (b l * c (l + 1)) * c j := Nat.mul_le_mul_right _ i2
        _ = (b l * c j) * c (l + 1) := by ring
        _ ≤ (b j * c l) * c (l + 1) := Nat.mul_le_mul_right _ i1
        _ = c l * (b j * c (l + 1)) := by ring
  rw [Finset.sum_range_succ b (k + 1), Finset.sum_range_succ c (k + 1)]
  have h1 : b (k + 1) * ∑ j ∈ range (k + 1), c j ≤ (∑ j ∈ range (k + 1), b j) * c (k + 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj =>
      key (k + 1) le_rfl j (by have := Finset.mem_range.1 hj; omega)
  rw [add_mul, mul_add]
  exact Nat.add_le_add_left h1 _
theorem downClosed_partial_sums (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (k : ℕ) :
    (∑ j ∈ range (k + 2), (Finset.slice 𝒜 j).card) * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ (∑ j ∈ range (k + 1), (Finset.slice 𝒜 j).card)
          * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (k + 1) with hk | hk
  · have h0 : (Finset.slice 𝒜 (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    rw [Finset.sum_range_succ (fun j => (Finset.slice 𝒜 j).card) (k + 1), h0, add_zero]
    exact Nat.mul_le_mul_left _
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega)))
  · exact mediant_partial_sums (fun j => (Finset.slice 𝒜 j).card) (fun j => (Fintype.card σ).choose j) k
      (fun j hj => Nat.choose_pos (by omega)) (fun j _ => slice_succ_mul_choose_le 𝒜 h j)
omit [Fintype σ] in
theorem sum_slice_eq_card_filter (𝒜 : Finset (Finset σ)) (k : ℕ) :
    ∑ j ∈ range (k + 1), (Finset.slice 𝒜 j).card = (𝒜.filter (fun s => s.card ≤ k)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))
    (fun s hs => Finset.mem_range.2 (by have := (Finset.mem_filter.1 hs).2; omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  ext s
  have := Finset.mem_range.1 hj
  simp only [Finset.mem_slice, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
omit [Fintype σ] in
theorem isLowerSet_of_erase (𝒜 : Finset (Finset σ))
    (h : ∀ s ∈ 𝒜, ∀ a ∈ s, s.erase a ∈ 𝒜) : IsLowerSet (𝒜 : Set (Finset σ)) := by
  intro s t hts hs
  have key : ∀ u : Finset σ, u ⊆ s → s \ u ∈ 𝒜 := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro _; simpa using hs
    | insert a u ha ih =>
      intro hu
      rw [Finset.sdiff_insert]
      refine h _ (ih ((Finset.subset_insert a u).trans hu)) a ?_
      exact Finset.mem_sdiff.2 ⟨hu (Finset.mem_insert_self a u), ha⟩
  have h1 := key (s \ t) Finset.sdiff_subset
  rw [Finset.sdiff_sdiff_eq_self hts] at h1
  exact Finset.mem_coe.2 h1
end Combinatorial
section Algebraic
variable {σ : Type*} {F : Type*} [Field F]
def leadSet (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) : Set (σ →₀ ℕ) :=
  {d | ∃ q ∈ Z, q ≠ 0 ∧ m.degree q = d}
theorem degree_sub_lt_of_lead_eq (m : MonomialOrder σ) {f g : MvPolynomial σ F}
    (hd : m.degree f = m.degree g) (hc : m.leadingCoeff f = m.leadingCoeff g)
    (hne : f - g ≠ 0) : m.degree (f - g) ≺[m] m.degree f := by
  apply lt_of_le_of_ne
  · have h1 := m.degree_sub_le (f := f) (g := g)
    rw [← hd, sup_idem] at h1
    exact h1
  · intro h'
    have h'' : m.degree (f - g) = m.degree f := m.toSyn.injective h'
    have h2 := m.degree_mem_support hne
    rw [h'', mem_support_iff, coeff_sub] at h2
    apply h2
    have h3 : g.coeff (m.degree f) = m.leadingCoeff g := by rw [hd]; rfl
    rw [h3, ← hc]
    exact sub_self _
theorem linearIndependent_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) :
    LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
  have hli : LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => monomial (d : σ →₀ ℕ) (1 : F)) := by
    have := (MvPolynomial.basisMonomials σ F).linearIndependent.comp
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => (d : σ →₀ ℕ)) Subtype.val_injective
    simpa [Function.comp_def] using this
  refine hli.map ?_
  rw [Submodule.ker_mkQ, Submodule.disjoint_def]
  intro p hp hZ
  by_contra hne
  have hsupp : p ∈ restrictSupport F ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) := by
    rw [restrictSupport_eq_span, Set.image_eq_range]
    exact hp
  have h1 : m.degree p ∈ ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) :=
    ((mem_restrictSupport_iff F).1 hsupp) (Finset.mem_coe.2 (m.degree_mem_support hne))
  exact h1 ⟨p, hZ, hne, rfl⟩
theorem mkQ_mem_span_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F))
    (p : MvPolynomial σ F) :
    Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
      {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
  suffices H : ∀ a : m.syn, ∀ p : MvPolynomial σ F, m.toSyn (m.degree p) = a →
      Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
        {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) from H _ p rfl
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro p hpa
    by_cases hp : p = 0
    · rw [hp, map_zero]
      exact Submodule.zero_mem _
    have hc : m.leadingCoeff p ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hp
    obtain ⟨g, hgd, hgc, hgmem⟩ : ∃ g : MvPolynomial σ F, m.degree g = m.degree p ∧
        m.leadingCoeff g = m.leadingCoeff p ∧
        Z.mkQ g ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
          {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
      by_cases hd : m.degree p ∈ leadSet m Z
      · obtain ⟨q, hqZ, hq0, hqd⟩ := hd
        have hcq : m.leadingCoeff q ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hq0
        have hr : m.leadingCoeff p / m.leadingCoeff q ≠ 0 := div_ne_zero hc hcq
        have hdeg : m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q) = m.degree p := by
          rw [m.degree_smul_of_isRegular (IsRegular.of_ne_zero hr), hqd]
        refine ⟨(m.leadingCoeff p / m.leadingCoeff q) • q, hdeg, ?_, ?_⟩
        · show ((m.leadingCoeff p / m.leadingCoeff q) • q).coeff
            (m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q)) = _
          rw [hdeg, coeff_smul, smul_eq_mul, ← hqd]
          exact div_mul_cancel₀ _ hcq
        · have : Z.mkQ ((m.leadingCoeff p / m.leadingCoeff q) • q) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Z.smul_mem _ hqZ
          rw [this]
          exact Submodule.zero_mem _
      · classical
        refine ⟨monomial (m.degree p) (m.leadingCoeff p), ?_, ?_, ?_⟩
        · rw [m.degree_monomial, if_neg hc]
        · exact m.leadingCoeff_monomial _
        · have : monomial (m.degree p) (m.leadingCoeff p)
              = m.leadingCoeff p • monomial (m.degree p) (1 : F) := by
            rw [smul_monomial, smul_eq_mul, mul_one]
          rw [this, map_smul]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨m.degree p, ⟨hd, le_rfl⟩, rfl⟩)
    have hsplit : Z.mkQ p = Z.mkQ (p - g) + Z.mkQ g := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ hgmem
    by_cases hpg : p - g = 0
    · rw [hpg, map_zero]
      exact Submodule.zero_mem _
    have hlt : m.degree (p - g) ≺[m] m.degree p :=
      degree_sub_lt_of_lead_eq m hgd.symm hgc.symm hpg
    have h1 := ih (m.toSyn (m.degree (p - g))) (hpa ▸ hlt) (p - g) rfl
    refine Submodule.span_mono (Set.image_mono ?_) h1
    rintro d ⟨hd1, hd2⟩
    exact ⟨hd1, hd2.trans hlt.le⟩
theorem finrank_quotient_comap_eq_finrank_map (Z V : Submodule F (MvPolynomial σ F)) :
    Module.finrank F (V ⧸ Z.comap V.subtype) = Module.finrank F (V.map Z.mkQ) := by
  have h1 : LinearMap.ker (Z.mkQ ∘ₗ V.subtype) = Z.comap V.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h2 : LinearMap.range (Z.mkQ ∘ₗ V.subtype) = V.map Z.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ((Submodule.quotEquivOfEq _ _ h1.symm).trans
    ((Z.mkQ ∘ₗ V.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h2))).finrank_eq
section DegLex
variable [LinearOrder σ] [WellFoundedGT σ]
theorem map_restrictTotalDegree_eq_span (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    (restrictTotalDegree σ F k).map Z.mkQ
      = Submodule.span F (Set.range
          (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
            Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F)))) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ k := (mem_restrictTotalDegree σ k p).1 hp
    refine Submodule.span_mono ?_ (mkQ_mem_span_std MonomialOrder.degLex Z p)
    rintro _ ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have h1 : d.degree ≤ (MonomialOrder.degLex.degree p).degree :=
      Finsupp.DegLex.monotone_degree hd2
    rw [degree_degLexDegree] at h1
    exact ⟨⟨d, hd1, h1.trans hp'⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨d, hd1, hd2⟩, rfl⟩
    refine ⟨monomial d 1, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree, totalDegree_monomial _ one_ne_zero]
    exact hd2
theorem finrank_map_restrictTotalDegree (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
      = Set.ncard {d : σ →₀ ℕ | d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} := by
  have hli : LinearIndependent F
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
    have := (linearIndependent_std MonomialOrder.degLex Z).comp
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        (⟨d.1, d.2.1⟩ : ((leadSet MonomialOrder.degLex Z)ᶜ : Set (σ →₀ ℕ))))
      (by intro a b hab; simp only [Subtype.mk.injEq] at hab; exact Subtype.ext hab)
    simpa [Function.comp_def] using this
  rw [map_restrictTotalDegree_eq_span, Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]
  rfl
noncomputable def ind (s : Finset σ) : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1
omit [WellFoundedGT σ] in
theorem ind_apply (s : Finset σ) (i : σ) : ind s i = if i ∈ s then 1 else 0 := by
  classical
  simp [ind, Finsupp.single_apply]
omit [WellFoundedGT σ] in
theorem ind_degree (s : Finset σ) : (ind s).degree = s.card := by
  simp [ind]
omit [WellFoundedGT σ] in
theorem ind_injective : Function.Injective (ind : Finset σ → σ →₀ ℕ) := by
  intro s t h
  ext i
  have h1 := DFunLike.congr_fun h i
  rw [ind_apply, ind_apply] at h1
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all
omit [WellFoundedGT σ] in
theorem ind_support_of_le_one (d : σ →₀ ℕ) (h : ∀ i, d i ≤ 1) : ind d.support = d := by
  ext i
  rw [ind_apply]
  have := h i
  by_cases hi : i ∈ d.support
  · rw [if_pos hi]
    have := Finsupp.mem_support_iff.1 hi
    omega
  · rw [if_neg hi]
    exact (Finsupp.notMem_support_iff.1 hi).symm
variable (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
theorem std_le_one
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ) :
    d i ≤ 1 := by
  classical
  by_contra hi
  apply hd
  set e : σ →₀ ℕ := d - Finsupp.single i 2 with he
  have hde : d = e + Finsupp.single i 2 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]; omega
    · simp [he, Finsupp.single_apply, Ne.symm hj]
  have hdeg : e.degree + 2 = d.degree := by
    rw [hde, map_add, Finsupp.degree_single]
  have hq : monomial e (1 : F) * (X i ^ 2 - X i)
      = monomial (e + Finsupp.single i 2) (1 : F) - monomial (e + Finsupp.single i 1) (1 : F) := by
    rw [mul_sub, X_pow_eq_monomial, monomial_mul, X, monomial_mul, mul_one]
  have hlt : MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 1) (1 : F))
      ≺[MonomialOrder.degLex]
      MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 2) (1 : F)) := by
    rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial, if_neg one_ne_zero,
      if_neg one_ne_zero]
    apply MonomialOrder.degLex.toSyn_strictMono
    apply lt_of_le_of_ne
    · exact add_le_add le_rfl (Finsupp.single_le_single.2 (show (1 : ℕ) ≤ 2 by omega))
    · intro h
      have := DFunLike.congr_fun h i
      simp at this
  refine ⟨monomial e (1 : F) * (X i ^ 2 - X i), hB e i (by omega), ?_, ?_⟩
  · rw [hq]
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [hq, MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_monomial,
      if_neg one_ne_zero, ← hde]
theorem std_sub_single
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ)
    (hi : 1 ≤ d i) : d - Finsupp.single i 1 ∉ leadSet MonomialOrder.degLex Z := by
  classical
  rintro ⟨q, hqZ, hq0, hqd⟩
  apply hd
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  have hdeg : 1 + (d - Finsupp.single i 1).degree = d.degree := by
    conv_rhs => rw [hde, map_add, Finsupp.degree_single]
  have hqt : q.totalDegree < K := by
    rw [← degree_degLexDegree, hqd]
    omega
  have hXne : (X i : MvPolynomial σ F) ≠ 0 := X_ne_zero i
  refine ⟨X i * q, hX q hqZ hqt i, mul_ne_zero hXne hq0, ?_⟩
  rw [MonomialOrder.degree_mul hXne hq0, MonomialOrder.degree_X, hqd, ← hde]
end DegLex
end Algebraic
section Combined
variable {σ : Type*} [Fintype σ] {F : Type*} [Field F]
theorem exists_downClosed_family [DecidableEq σ] (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z) :
    ∃ 𝒜 : Finset (Finset σ), IsLowerSet (𝒜 : Set (Finset σ)) ∧ ∀ k ≤ K,
      Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        = ∑ j ∈ range (k + 1), (Finset.slice 𝒜 j).card := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  set L := leadSet (F := F) MonomialOrder.degLex Z with hL
  refine ⟨Finset.univ.filter (fun s => ind s ∉ L ∧ s.card ≤ K), ?_, ?_⟩
  · apply isLowerSet_of_erase
    intro s hs a ha
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨-, hs1, hs2⟩ := hs
    refine ⟨Finset.mem_univ _, ?_, (Finset.card_erase_le).trans hs2⟩
    have h1 : ind (s.erase a) = ind s - Finsupp.single a 1 := by
      ext j
      rw [Finsupp.tsub_apply, ind_apply, ind_apply, Finsupp.single_apply]
      by_cases hj : a = j
      · subst hj; simp [ha]
      · simp [hj, Ne.symm hj]
    rw [h1]
    exact std_sub_single Z K hX (ind s) hs1 (by rw [ind_degree]; exact hs2) a
      (by rw [ind_apply, if_pos ha])
  · intro k hk
    rw [finrank_map_restrictTotalDegree, sum_slice_eq_card_filter, ← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective _ ind_injective]
    congr 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd1, hd2⟩
      have h1 : ind d.support = d :=
        ind_support_of_le_one d (std_le_one Z K hB d hd1 (hd2.trans hk))
      have h2 : d.support.card = d.degree := by rw [← ind_degree, h1]
      refine ⟨d.support, ⟨⟨?_, ?_⟩, ?_⟩, h1⟩
      · rw [h1]; exact hd1
      · omega
      · omega
    · rintro ⟨s, ⟨⟨hs1, _⟩, hs3⟩, rfl⟩
      exact ⟨hs1, by rw [ind_degree]; exact hs3⟩
theorem rank_ratio_monotone (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (k : ℕ) (hk : k + 1 ≤ K) :
    Module.finrank F ((restrictTotalDegree σ F (k + 1)).map Z.mkQ)
        * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  classical
  obtain ⟨𝒜, h𝒜, hc⟩ := exists_downClosed_family Z K hX hB
  rw [hc (k + 1) hk, hc k (by omega)]
  exact downClosed_partial_sums 𝒜 h𝒜 k
end Combined
end MonoRank
end C.Helpers
namespace C.Helpers
open Module
section Abstract
variable {F U : Type*} [Field F] [AddCommGroup U] [Module F U]
theorem threeTerm_finrank [FiniteDimensional F U] (I A B L : Submodule F U)
    (h : L ⊓ (A ⊔ B) ≤ A ⊓ B) :
    finrank F ↥(I ⊓ A) + finrank F ↥(I ⊓ B) + finrank F ↥(I ⊓ L)
      ≤ finrank F ↥I + 2 * finrank F ↥(I ⊓ A ⊓ B) := by
  have e1 := Submodule.finrank_sup_add_finrank_inf_eq (I ⊓ A) (I ⊓ B)
  have e2 := Submodule.finrank_sup_add_finrank_inf_eq ((I ⊓ A) ⊔ (I ⊓ B)) (I ⊓ L)
  have hPQ : (I ⊓ A) ⊓ (I ⊓ B) = I ⊓ A ⊓ B := by
    rw [← inf_inf_distrib_left, inf_assoc]
  have hup : ((I ⊓ A) ⊔ (I ⊓ B)) ⊔ (I ⊓ L) ≤ I :=
    sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  have hdown : ((I ⊓ A) ⊔ (I ⊓ B)) ⊓ (I ⊓ L) ≤ I ⊓ A ⊓ B := by
    rw [inf_assoc]
    refine le_inf ?_ ?_
    · exact inf_le_right.trans inf_le_left
    · refine le_trans ?_ h
      exact le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans (sup_le_sup inf_le_right inf_le_right))
  have h1 := Submodule.finrank_mono hup
  have h2 := Submodule.finrank_mono hdown
  rw [hPQ] at e1
  omega
variable {G : Type*}
noncomputable def subDim (S : Submodule F U) : ℕ := finrank F ↥S
theorem subDim_mono [FiniteDimensional F U] {S T : Submodule F U} (h : S ≤ T) :
    subDim S ≤ subDim T := Submodule.finrank_mono h
theorem subDim_top : subDim (⊤ : Submodule F U) = finrank F U := finrank_top F U
noncomputable def kerSum [Add G] (K : G → Submodule F U) : G → List G → ℕ
  | c, [] => subDim (K c)
  | c, b :: bs => kerSum K c bs + kerSum K (c + b) bs
def listInf (K : G → Submodule F U) : List G → Submodule F U
  | [] => ⊤
  | b :: bs => K b ⊓ listInf K bs
theorem listInf_le (K : G → Submodule F U) {b : G} :
    ∀ {bs : List G}, b ∈ bs → listInf K bs ≤ K b
  | [], hb => by simp at hb
  | a :: bs, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact inf_le_left
    · exact inf_le_right.trans (listInf_le K hb)
private theorem arith_step (N S1 S2 dI dU d1 d2 d3 dJ dJ' : ℕ)
    (ih1 : 2 * S1 + N * dI ≤ N * dU + 2 * (N * d1))
    (ih2 : 2 * S2 + N * dI ≤ N * dU + 2 * (N * d2))
    (tt : d1 + d2 + d3 ≤ dI + 2 * dJ) (hJ : dJ ≤ dJ') :
    2 * (S1 + S2) + (2 * N) * d3 ≤ (2 * N) * dU + 2 * ((2 * N) * dJ') := by
  nlinarith [Nat.mul_le_mul_left N tt, Nat.mul_le_mul_left N hJ]
theorem kerSum_le [Add G] [FiniteDimensional F U] (K : G → Submodule F U)
    (hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b)
    (hthree : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b)) :
    ∀ (bs : List G) (c : G),
      2 * kerSum K c bs + 2 ^ bs.length * subDim (listInf K bs)
        ≤ 2 ^ bs.length * finrank F U
          + 2 * (2 ^ bs.length * subDim (listInf K bs ⊓ K c))
  | [], c => by
    have h1 : listInf K ([] : List G) = ⊤ := rfl
    have h2 : kerSum K c [] = subDim (K c) := rfl
    rw [h1, h2, top_inf_eq, subDim_top]
    simp only [List.length_nil, pow_zero, one_mul]
    omega
  | b :: bs, c => by
    have ih1 := kerSum_le K hadd hthree bs c
    have ih2 := kerSum_le K hadd hthree bs (c + b)
    have tt : subDim (listInf K bs ⊓ K c) + subDim (listInf K bs ⊓ K (c + b))
        + subDim (K b ⊓ listInf K bs)
        ≤ subDim (listInf K bs) + 2 * subDim (listInf K bs ⊓ K c ⊓ K (c + b)) := by
      have := threeTerm_finrank (listInf K bs) (K c) (K (c + b)) (K b) (hthree c b)
      rw [inf_comm (listInf K bs) (K b)] at this
      exact this
    have hJ : listInf K bs ⊓ K c ⊓ K (c + b) ≤ K b ⊓ listInf K bs ⊓ K c := by
      refine le_inf (le_inf ?_ (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
      exact le_trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (hadd c b)
    have hJ' := subDim_mono hJ
    have h1 : listInf K (b :: bs) = K b ⊓ listInf K bs := rfl
    have h2 : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [h1, h2, hp]
    have hU := arith_step (2 ^ bs.length) _ _ _ (finrank F U) _ _ _ _ _ ih1 ih2 tt hJ'
    exact hU
theorem exists_le_kerSum [Add G] (K : G → Submodule F U) :
    ∀ (bs : List G) (c : G), ∃ c', 2 ^ bs.length * subDim (K c') ≤ kerSum K c bs
  | [], c => ⟨c, by simp [kerSum]⟩
  | b :: bs, c => by
    obtain ⟨c1, h1⟩ := exists_le_kerSum K bs c
    obtain ⟨c2, h2⟩ := exists_le_kerSum K bs (c + b)
    have e : kerSum K c (b :: bs) = kerSum K c bs + kerSum K (c + b) bs := rfl
    have hp : 2 ^ (b :: bs).length = 2 * 2 ^ bs.length := by
      rw [List.length_cons, pow_succ, mul_comm]
    rw [e, hp]
    rcases le_total (subDim (K c1)) (subDim (K c2)) with h | h
    · refine ⟨c1, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
    · refine ⟨c2, ?_⟩
      have := Nat.mul_le_mul_left (2 ^ bs.length) h
      nlinarith
end Abstract
section Maps
variable {F U W G : Type*} [Field F] [AddCommGroup U] [Module F U] [AddCommGroup W]
  [Module F W] [AddCommGroup G]
theorem exists_two_mul_finrank_ker_le [FiniteDimensional F U] (Φ : G →+ (U →ₗ[F] W))
    (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (bs : List G) :
    ∃ c : G, 2 * finrank F ↥(LinearMap.ker (Φ c))
      ≤ finrank F U + finrank F ↥(listInf (fun c => LinearMap.ker (Φ c)) bs) := by
  set K : G → Submodule F U := fun c => LinearMap.ker (Φ c) with hKdef
  have hcancel : ∀ c b : G, c + (c + b) = b := fun c b => by
    rw [← add_assoc, h2, zero_add]
  have hadd : ∀ c b, K c ⊓ K (c + b) ≤ K b := by
    intro c b f hf
    have h1 : Φ c f = 0 := hf.1
    have h3 : Φ (c + b) f = 0 := hf.2
    have : Φ b f = 0 := by
      rw [map_add, LinearMap.add_apply, h1, zero_add] at h3
      exact h3
    exact this
  have hthree' : ∀ c b, K b ⊓ (K c ⊔ K (c + b)) ≤ K c ⊓ K (c + b) := by
    intro c b f hf
    have hb : Φ b f = 0 := hf.1
    refine ⟨?_, ?_⟩
    · exact hthree c (c + b) f (by rw [hcancel]; exact hb) hf.2
    · refine hthree (c + b) c f ?_ ?_
      · rw [add_comm, hcancel]; exact hb
      · have := hf.2
        rwa [sup_comm] at this
  have key := kerSum_le K hadd hthree' bs 0
  obtain ⟨c, hc⟩ := exists_le_kerSum K bs (0 : G)
  refine ⟨c, ?_⟩
  have hle : subDim (listInf K bs ⊓ K 0) ≤ subDim (listInf K bs) := subDim_mono inf_le_left
  have hpos : 0 < 2 ^ bs.length := by positivity
  have t := Nat.mul_le_mul_left (2 ^ bs.length) hle
  have : 2 ^ bs.length * (2 * subDim (K c))
      ≤ 2 ^ bs.length * (finrank F U + subDim (listInf K bs)) := by nlinarith
  exact Nat.le_of_mul_le_mul_left this hpos
theorem rank_retention [FiniteDimensional F U] {W' : Type*} [AddCommGroup W'] [Module F W']
    (Φ : G →+ (U →ₗ[F] W)) (h2 : ∀ a : G, a + a = 0)
    (hthree : ∀ a b : G, ∀ f : U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0)
    (S : U →ₗ[F] W') (bs : List G)
    (hS : ∀ f : U, (∀ b ∈ bs, Φ b f = 0) → S f = 0) :
    ∃ c : G, finrank F ↥(LinearMap.range S) ≤ 2 * finrank F ↥(LinearMap.range (Φ c)) := by
  obtain ⟨c, hc⟩ := exists_two_mul_finrank_ker_le Φ h2 hthree bs
  refine ⟨c, ?_⟩
  have hI : listInf (fun c => LinearMap.ker (Φ c)) bs ≤ LinearMap.ker S := by
    intro f hf
    exact hS f fun b hb => listInf_le (fun c => LinearMap.ker (Φ c)) hb hf
  have hI' := Submodule.finrank_mono hI
  have r1 := LinearMap.finrank_range_add_finrank_ker S
  have r2 := LinearMap.finrank_range_add_finrank_ker (Φ c)
  omega
theorem rank_retention_pi {ι U W : Type*} [Fintype ι] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (M : ι → U →ₗ[ZMod 2] W)
    (hthree : ∀ a b : ι → ZMod 2, ∀ f : U, (∑ i, (a i + b i) • M i) f = 0 →
      f ∈ LinearMap.ker (∑ i, a i • M i) ⊔ LinearMap.ker (∑ i, b i • M i) →
      (∑ i, a i • M i) f = 0) :
    ∃ c : ι → ZMod 2, finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi M))
      ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (∑ i, c i • M i)) := by
  classical
  let Φ : (ι → ZMod 2) →+ (U →ₗ[ZMod 2] W) :=
    { toFun := fun c => ∑ i, c i • M i
      map_zero' := by simp
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hsingle : ∀ i : ι, Φ (Pi.single i 1) = M i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • M j = M i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  refine rank_retention Φ h2 (fun a b f h1 h3 => hthree a b f h1 h3) (LinearMap.pi M)
    (Finset.univ.toList.map fun i => Pi.single i 1) ?_
  intro f hf
  funext i
  have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
  rw [hsingle] at this
  simpa using this
end Maps
section Multiplication
open MvPolynomial
variable {σ ι τ : Type*}
noncomputable def mulMap (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) :
    ↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C) :=
  LinearMap.pi fun α => C.mkQ ∘ₗ LinearMap.mulRight (ZMod 2) (q * h α) ∘ₗ U.subtype
theorem mulMap_apply_eq_zero (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (h : τ → MvPolynomial σ (ZMod 2)) (q : MvPolynomial σ (ZMod 2)) (f : ↥U) :
    mulMap C U h q f = 0 ↔ ∀ α, (f : MvPolynomial σ (ZMod 2)) * q * h α ∈ C := by
  rw [funext_iff]
  refine forall_congr' fun α => ?_
  simp [mulMap, mul_assoc]
noncomputable def comb [Fintype ι] (g : ι → MvPolynomial σ (ZMod 2)) (c : ι → ZMod 2) :
    MvPolynomial σ (ZMod 2) := ∑ i, c i • g i
theorem rank_retention_mul [Fintype ι]
    (C U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (g : ι → MvPolynomial σ (ZMod 2)) (h : τ → MvPolynomial σ (ZMod 2))
    (hmul : ∀ (c c' : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * comb g c * h α ∈ C → f * comb g c * comb g c' * h α ∈ C)
    (hidem : ∀ (c : ι → ZMod 2) (α : τ), ∀ f ∈ U,
      f * (comb g c * comb g c + comb g c) * h α ∈ C) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi fun i => mulMap C U h (g i)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range (mulMap C U h (comb g c))) := by
  classical
  have hcomb_add : ∀ a b : ι → ZMod 2, comb g (a + b) = comb g a + comb g b := fun a b => by
    simp [comb, add_smul, Finset.sum_add_distrib]
  have hcomb_single : ∀ i : ι, comb g (Pi.single i 1) = g i := fun i => by
    show ∑ j, (Pi.single i (1 : ZMod 2) : ι → ZMod 2) j • g j = g i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  let Φ : (ι → ZMod 2) →+ (↥U →ₗ[ZMod 2] (τ → MvPolynomial σ (ZMod 2) ⧸ C)) :=
    { toFun := fun c => mulMap C U h (comb g c)
      map_zero' := by
        ext f α
        simp [mulMap, comb]
      map_add' := fun a b => by
        ext f α
        simp [mulMap, hcomb_add, add_mul, mul_add, mul_assoc] }
  have h2 : ∀ a : ι → ZMod 2, a + a = 0 := fun a => by
    funext i
    exact CharTwo.add_self_eq_zero (a i)
  have hthree : ∀ a b : ι → ZMod 2, ∀ f : ↥U, Φ (a + b) f = 0 →
      f ∈ LinearMap.ker (Φ a) ⊔ LinearMap.ker (Φ b) → Φ a f = 0 := by
    intro a b f hab hf
    obtain ⟨fa, hfa, fb, hfb, rfl⟩ := Submodule.mem_sup.1 hf
    have hfa' : ∀ α, (fa : MvPolynomial σ (ZMod 2)) * comb g a * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g a) fa).1 hfa
    have hfb' : ∀ α, (fb : MvPolynomial σ (ZMod 2)) * comb g b * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g b) fb).1 hfb
    have hab' : ∀ α, ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * h α ∈ C :=
      (mulMap_apply_eq_zero C U h (comb g (a + b)) (fa + fb)).1 hab
    refine (mulMap_apply_eq_zero C U h (comb g a) (fa + fb)).2 fun α => ?_
    have A1 := hmul a b α fa fa.2 (hfa' α)
    have A2 := hmul b a α fb fb.2 (hfb' α)
    have A3 := hmul (a + b) a α _ (fa + fb).2 (hab' α)
    have A4 := hidem a α _ (fa + fb).2
    have e : ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g a * h α
        = ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * (comb g a * comb g a + comb g a) * h α
          - ((fa + fb : ↥U) : MvPolynomial σ (ZMod 2)) * comb g (a + b) * comb g a * h α
          + ((fa : MvPolynomial σ (ZMod 2)) * comb g a * comb g b * h α
            + (fb : MvPolynomial σ (ZMod 2)) * comb g b * comb g a * h α) := by
      rw [hcomb_add, Submodule.coe_add]
      ring
    rw [e]
    exact C.add_mem (C.sub_mem A4 A3) (C.add_mem A1 A2)
  obtain ⟨c, hc⟩ := rank_retention Φ h2 hthree
    (LinearMap.pi fun i => mulMap C U h (g i))
    (Finset.univ.toList.map fun i => Pi.single i 1) (by
      intro f hf
      funext i
      have := hf (Pi.single i 1) (List.mem_map.2 ⟨i, by simp, rfl⟩)
      have e : Φ (Pi.single i 1) = mulMap C U h (g i) := by
        show mulMap C U h (comb g (Pi.single i 1)) = _
        rw [hcomb_single]
      rw [e] at this
      simpa using this)
  exact ⟨c, hc⟩
noncomputable def affine [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) : MvPolynomial σ (ZMod 2) :=
  C a + ∑ j, C (B j) * X j
theorem comb_affine [Fintype σ] [Fintype ι] (a : ι → ZMod 2) (B : ι → σ → ZMod 2)
    (c : ι → ZMod 2) :
    comb (fun i => affine (a i) (B i)) c
      = affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) := by
  simp only [comb, affine, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · simp [map_sum, smul_eq_C_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [map_sum, Finset.sum_mul, smul_eq_C_mul, mul_assoc]
theorem affine_totalDegree_le [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    (affine a B).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
  refine totalDegree_finsetSum_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X]
theorem affine_idem [Fintype σ] (a : ZMod 2) (B : σ → ZMod 2) :
    affine a B * affine a B + affine a B = ∑ j, C (B j) * (X j * X j + X j) := by
  have ha : ∀ x : ZMod 2, x * x = x := by decide
  have hC : ∀ x : ZMod 2, (C x : MvPolynomial σ (ZMod 2)) * C x = C x := fun x => by
    rw [← C_mul, ha]
  have e1 : (∑ j, (C (B j) : MvPolynomial σ (ZMod 2)) * X j) * (∑ j, C (B j) * X j)
      = ∑ j, C (B j) * (X j * X j) := by
    rw [← sq, CharTwo.sum_sq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sq]
    calc (C (B j) : MvPolynomial σ (ZMod 2)) * X j * (C (B j) * X j)
        = (C (B j) * C (B j)) * (X j * X j) := by ring
      _ = C (B j) * (X j * X j) := by rw [hC]
  rw [affine, CharTwo.add_mul_self, hC, e1]
  have e2 : ∀ u v w : MvPolynomial σ (ZMod 2), u + v + (u + w) = (u + u) + (v + w) :=
    fun u v w => by ring
  rw [e2, CharTwo.add_self_eq_zero, zero_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring
theorem rank_retention_closure [Fintype σ] [Fintype ι]
    (Cl U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) [FiniteDimensional (ZMod 2) ↥U]
    (D k d : ℕ)
    (hX : ∀ p ∈ Cl, p.totalDegree < D → ∀ j, X j * p ∈ Cl)
    (hBool : ∀ p : MvPolynomial σ (ZMod 2), p.totalDegree + 2 ≤ D →
      ∀ j, p * (X j * X j + X j) ∈ Cl)
    (hU : ∀ f ∈ U, f.totalDegree ≤ k)
    (a : ι → ZMod 2) (B : ι → σ → ZMod 2) (h : τ → MvPolynomial σ (ZMod 2))
    (hh : ∀ α, (h α).totalDegree ≤ d) (hD : d + k + 2 ≤ D) :
    ∃ c : ι → ZMod 2,
      finrank (ZMod 2)
          ↥(LinearMap.range (LinearMap.pi fun i => mulMap Cl U h (affine (a i) (B i))))
        ≤ 2 * finrank (ZMod 2)
          ↥(LinearMap.range (mulMap Cl U h (comb (fun i => affine (a i) (B i)) c))) := by
  have hmulaff : ∀ p ∈ Cl, p.totalDegree < D → ∀ (a' : ZMod 2) (B' : σ → ZMod 2),
      p * affine a' B' ∈ Cl := by
    intro p hp hdeg a' B'
    have e : p * affine a' B' = a' • p + ∑ j, B' j • (X j * p) := by
      rw [affine, mul_add, Finset.mul_sum]
      congr 1
      · rw [smul_eq_C_mul, mul_comm]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_C_mul]
        ring
    rw [e]
    exact Cl.add_mem (Cl.smul_mem _ hp)
      (Cl.sum_mem fun j _ => Cl.smul_mem _ (hX p hp hdeg j))
  refine rank_retention_mul Cl U (fun i => affine (a i) (B i)) h ?_ ?_
  · intro c c' α f hf hmem
    rw [comb_affine] at hmem ⊢
    rw [comb_affine]
    have hdeg : (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j) * h α).totalDegree
        < D := by
      have h1 := totalDegree_mul
        (f * affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)) (h α)
      have h2 := totalDegree_mul f (affine (∑ i, c i * a i) (fun j => ∑ i, c i * B i j))
      have h3 := hU f hf
      have h4 := hh α
      have h5 := affine_totalDegree_le (∑ i, c i * a i) (fun j => ∑ i, c i * B i j)
      omega
    have := hmulaff _ hmem hdeg (∑ i, c' i * a i) (fun j => ∑ i, c' i * B i j)
    have e : ∀ u v w x : MvPolynomial σ (ZMod 2), u * v * w * x = u * v * x * w :=
      fun u v w x => by ring
    rw [e]
    exact this
  · intro c α f hf
    rw [comb_affine, affine_idem]
    have e : f * (∑ j, C (∑ i, c i * B i j) * (X j * X j + X j)) * h α
        = ∑ j, (∑ i, c i * B i j) • ((f * h α) * (X j * X j + X j)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_C_mul]
      ring
    rw [e]
    refine Cl.sum_mem fun j _ => Cl.smul_mem _ (hBool _ ?_ j)
    have h1 := totalDegree_mul f (h α)
    have h3 := hU f hf
    have h4 := hh α
    omega
end Multiplication
section Counterexample
theorem coordinate_maps_no_rank_retention :
    ¬ ∃ c : Fin 3 → ZMod 2,
      finrank (ZMod 2) ↥(LinearMap.range (LinearMap.pi
          fun i => (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2)))
        ≤ 2 * finrank (ZMod 2) ↥(LinearMap.range
          (∑ i, c i • (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))) := by
  rintro ⟨c, hc⟩
  have h1 : finrank (ZMod 2) ↥(LinearMap.range
      (∑ i, c i • (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))) ≤ 1 := by
    refine (Submodule.finrank_le _).trans ?_
    simp
  have hid : (LinearMap.pi fun i => (LinearMap.proj i : (Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
      = LinearMap.id := by
    ext u i
    simp
  rw [hid, LinearMap.range_id, finrank_top] at hc
  have h3 : finrank (ZMod 2) (Fin 3 → ZMod 2) = 3 := by simp
  omega
end Counterexample
end C.Helpers
namespace C.DegSizeRank
open MvPolynomial Module PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
section Glue
variable {σ : Type}
theorem exists_single_add (d : σ →₀ ℕ) (hd : d ≠ 0) :
    ∃ (i : σ) (e : σ →₀ ℕ), d = Finsupp.single i 1 + e ∧ e.degree + 1 = d.degree := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finsupp.ext h)
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp [Ne.symm hj]
  refine ⟨i, d - Finsupp.single i 1, hde, ?_⟩
  have h := congrArg Finsupp.degree hde
  rw [map_add, Finsupp.degree_single] at h
  omega
theorem totalDegree_monomial_one (d : σ →₀ ℕ) :
    (monomial d (1 : ZMod 2)).totalDegree = d.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl
theorem bool_totalDegree_le (v : σ) :
    (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_X]
    omega
theorem monomial_mul_mem {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (hC : DegClosed C D) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree = n → ∀ f ∈ C, n + f.totalDegree ≤ D →
      monomial d (1 : ZMod 2) * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro d hd f hf _
    have h0 : d = 0 := by
      by_contra hne
      obtain ⟨i, e, -, he⟩ := exists_single_add d hne
      omega
    subst h0
    simpa using hf
  | succ n ih =>
    intro d hd f hf hdeg
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, e, hde, he⟩ := exists_single_add d hne
    have h1 := ih e (by omega) f hf (by omega)
    have h2 : (monomial e (1 : ZMod 2) * f).totalDegree + 1 ≤ D := by
      have h3 := totalDegree_mul (monomial e (1 : ZMod 2)) f
      have h4 := totalDegree_monomial_one e
      omega
    have h5 := hC.mulX i _ h1 h2
    have e5 : monomial d (1 : ZMod 2) * f = X i * (monomial e 1 * f) := by
      rw [hde, ← mul_assoc]
      congr 1
      rw [X, monomial_mul_monomial, mul_one]
    rw [e5]
    exact h5
theorem absorb {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ} (hC : DegClosed C D)
    (f g : MvPolynomial σ (ZMod 2)) (hf : f ∈ C) (hdeg : g.totalDegree + f.totalDegree ≤ D) :
    g * f ∈ C := by
  have e : g * f = ∑ v ∈ g.support, g.coeff v • (monomial v (1 : ZMod 2) * f) := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine C.sum_mem fun v hv => C.smul_mem _ (monomial_mul_mem hC _ v rfl f hf ?_)
  have h1 : v.degree ≤ g.totalDegree := le_totalDegree hv
  omega
theorem finite_restrictTotalDegree [Finite σ] (k : ℕ) :
    Module.Finite (ZMod 2) ↥(restrictTotalDegree σ (ZMod 2) k) := by
  have hfin : Finite ↥{u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Set.Finite.to_subtype ((Finsupp.finite_of_degree_le k).subset fun u hu => hu)
  exact Module.Finite.of_basis
    (basisRestrictSupport (ZMod 2) {u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k})
theorem errRank_eq_range [Finite σ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (M : Set (MvPolynomial σ (ZMod 2)))
    (k : ℕ) (L : ↥(polyLE σ k) →ₗ[ZMod 2] W)
    (hL : ∀ f : ↥(polyLE σ k), L f = 0 ↔ ∀ m ∈ M, m * (f : MvPolynomial σ (ZMod 2)) ∈ C) :
    finrank (ZMod 2) ↥(LinearMap.range L) = errRank C M k := by
  have hle : errKer C M k ≤ polyLE σ k := inf_le_left
  have hker : LinearMap.ker L = (errKer C M k).comap (polyLE σ k).subtype := by
    ext f
    rw [LinearMap.mem_ker, hL, Submodule.mem_comap, mem_errKer]
    exact ⟨fun h => ⟨(mem_restrictTotalDegree σ k _).1 f.2, h⟩, fun h => h.2⟩
  have r := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at r
  unfold errRank
  omega
noncomputable def annih (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)
theorem mem_annih {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ annih C M ↔ ∀ m ∈ M, m * f ∈ C := by
  simp [annih]
theorem errRank_eq_map [Finite σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errRank C M k = finrank (ZMod 2) ↥((polyLE σ k).map (annih C M).mkQ) := by
  rw [← errRank_eq_range C M k ((annih C M).mkQ ∘ₗ (polyLE σ k).subtype)
    (fun f => by simp [mem_annih]), LinearMap.range_comp, Submodule.range_subtype]
theorem iterate_ratio (c N : ℕ → ℕ) (K : ℕ) (hpos : ∀ j, 0 < N j)
    (step : ∀ j, j + 1 ≤ K → c (j + 1) * N j ≤ c j * N (j + 1)) (k : ℕ) :
    ∀ t, k + t ≤ K → c (k + t) * N k ≤ c k * N (k + t) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro hK
    have h1 := ih (by omega)
    have h2 := step (k + t) (by omega)
    have h3 : c (k + t + 1) * N k * N (k + t) ≤ c k * N (k + t + 1) * N (k + t) := by
      calc c (k + t + 1) * N k * N (k + t) = c (k + t + 1) * N (k + t) * N k := by ring
        _ ≤ c (k + t) * N (k + t + 1) * N k := Nat.mul_le_mul_right _ h2
        _ = c (k + t) * N k * N (k + t + 1) := by ring
        _ ≤ c k * N (k + t) * N (k + t + 1) := Nat.mul_le_mul_right _ h1
        _ = c k * N (k + t + 1) * N (k + t) := by ring
    exact Nat.le_of_mul_le_mul_right h3 (hpos (k + t))
theorem exists_affine [Fintype σ] (g : MvPolynomial σ (ZMod 2)) (hg : g.totalDegree ≤ 1) :
    ∃ (a : ZMod 2) (B : σ → ZMod 2), g = affine a B := by
  classical
  refine ⟨g.coeff 0, fun j => g.coeff (Finsupp.single j 1), ?_⟩
  ext d
  by_cases hd : 1 < d.degree
  · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hg hd),
      coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (affine_totalDegree_le _ _) hd)]
  · by_cases h0 : d = 0
    · subst h0
      simp [affine, coeff_C_mul]
    · obtain ⟨i, e, hde, he⟩ := exists_single_add d h0
      have he0 : e = 0 := by
        by_contra hne
        obtain ⟨_, _, -, he'⟩ := exists_single_add e hne
        omega
      subst he0
      rw [add_zero] at hde
      subst hde
      have h0' : ¬ ((0 : σ →₀ ℕ) = Finsupp.single i 1) := fun h => h0 h.symm
      simp [affine, coeff_C_mul, coeff_X, Finsupp.single_left_inj, h0']
end Glue
theorem monoRank_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
      ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
        errRank C (zMul P G) k' * numMono (Fintype.card σ) k
          ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k' := by
  intro σ _ C D a K P G hC hP hG hD
  have hmdeg : ∀ m ∈ zMul P G, m.totalDegree ≤ a + 1 := by
    rintro _ ⟨g, hg, rfl⟩
    show (P * g).totalDegree ≤ a + 1
    have h1 := totalDegree_mul P g
    have h2 := hG g hg
    omega
  have hX : ∀ p ∈ annih C (zMul P G), p.totalDegree < K → ∀ i : σ,
      X i * p ∈ annih C (zMul P G) := by
    intro p hp hdeg i
    rw [mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ annih C (zMul P G) := by
    intro d i hd
    rw [mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := totalDegree_monomial_one d
    have h3 := bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C (zMul P G) (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C (zMul P G) j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [errRank_eq_map, errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (annih C (zMul P G)) K hX hB j hj
  have hpos : ∀ j, 0 < numMono (Fintype.card σ) j := by
    intro j
    unfold numMono
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  intro k k' hkk' hk'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  exact iterate_ratio (fun j => errRank C (zMul P G) j) (fun j => numMono (Fintype.card σ) j)
    K hpos step k t hk'
theorem rankRetention_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
      (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
      b + k + 2 ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) k
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
  classical
  intro σ _ C D b k H G hC hH hG hD
  have haff : ∀ i : ↥G, ∃ (a : ZMod 2) (B : σ → ZMod 2),
      (i : MvPolynomial σ (ZMod 2)) = affine a B := fun i => exists_affine _ (hG i i.2)
  choose a B hab using haff
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  obtain ⟨c, hc⟩ := rank_retention_closure (ι := ↥G) (τ := ↥H) C (polyLE σ k) D k b
    (fun p hp hdeg j => hC.mulX j p hp (by omega))
    (fun p hp j => absorb hC _ _ (hC.bool j) (by
      have h1 := bool_totalDegree_le (σ := σ) j
      omega))
    (fun f hf => (mem_restrictTotalDegree σ k f).1 hf)
    a B hfun (fun α => hH α α.2) hD
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb (fun i => affine (a i) (B i)) c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • affine (a i) (B i) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    rw [← hab i]
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ k) hfun (affine (a i) (B i))))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ k) hfun (affine (a ⟨g, hg⟩) (B ⟨g, hg⟩)) f = 0 :=
        congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ k) hfun _ f).1 hz' ⟨h, hh⟩
      rw [← hab ⟨g, hg⟩] at h1
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ k) hfun (affine (a i) (B i)) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      rw [← hab i]
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ k) hfun (comb (fun i => affine (a i) (B i)) c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
end C.DegSizeRank
namespace C.DegSizeGain
open MvPolynomial Module PEqualNP.ProofComplexity C.DegSizePlan
def Stmt41 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'
def Stmt35 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k
section LinearAlgebra
variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']
theorem finrank_eq_map_add_inf_ker (g : V →ₗ[ZMod 2] V') (S : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) S] :
    finrank (ZMod 2) S
      = finrank (ZMod 2) ↥(S.map g) + finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
  have h := (g ∘ₗ S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  have e : finrank (ZMod 2) ↥((LinearMap.ker g).comap S.subtype)
      = finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  omega
theorem finrank_add_le (f : V →ₗ[ZMod 2] V) (A W : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) W] :
    finrank (ZMod 2) A + finrank (ZMod 2) W
      ≤ finrank (ZMod 2) ↥(A ⊓ W.comap f) + finrank (ZMod 2) ↥(A.map f ⊔ W) := by
  have h1 := finrank_eq_map_add_inf_ker (W.mkQ ∘ₗ f) A
  have h2 := finrank_eq_map_add_inf_ker W.mkQ (A.map f ⊔ W)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [Submodule.ker_mkQ, inf_eq_right.mpr le_sup_right] at h2
  have h3 : finrank (ZMod 2) ↥(A.map (W.mkQ ∘ₗ f))
      ≤ finrank (ZMod 2) ↥((A.map f ⊔ W).map W.mkQ) := by
    rw [Submodule.map_comp]
    exact Submodule.finrank_mono (Submodule.map_mono le_sup_left)
  omega
theorem codim_iInf {ι : Type} (E : Submodule (ZMod 2) V) [FiniteDimensional (ZMod 2) E]
    (W : ι → Submodule (ZMod 2) V) (hW : ∀ ν, W ν ≤ E) (S : Finset ι) :
    finrank (ZMod 2) E
      ≤ finrank (ZMod 2) ↥(E ⊓ ⨅ ν ∈ S, W ν)
        + ∑ ν ∈ S, (finrank (ZMod 2) E - finrank (ZMod 2) (W ν)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (⨅ ν ∈ (∅ : Finset ι), W ν) = ⊤ := by simp
    rw [h0, inf_top_eq]
    exact Nat.le_add_right _ _
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha, inf_left_comm]
    have : FiniteDimensional (ZMod 2) ↥(W a) := Submodule.finiteDimensional_of_le (hW a)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W a) (E ⊓ ⨅ ν ∈ s, W ν)
    have h2 : finrank (ZMod 2) ↥(W a ⊔ (E ⊓ ⨅ ν ∈ s, W ν)) ≤ finrank (ZMod 2) E :=
      Submodule.finrank_mono (sup_le (hW a) inf_le_left)
    have h3 : finrank (ZMod 2) (W a) ≤ finrank (ZMod 2) E := Submodule.finrank_mono (hW a)
    omega
end LinearAlgebra
section Poly
variable {σ : Type}
theorem mem_polyLE {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ polyLE σ k ↔ f.totalDegree ≤ k := by
  simp [polyLE, mem_restrictTotalDegree]
theorem deg_mul_le {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)
theorem deg_one_add_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (1 + q).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (q * q + q).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans (max_le (deg_mul_le hq hq) (by omega))
theorem deg_le_one_of_mem_span {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 :=
  mem_polyLE.mp (Submodule.span_le.mpr (fun g hg => mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, 1 :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le (h j))
    _ = t := by simp
theorem eq_zero_of_sum_eq_zero (u : σ →₀ ℕ) (h : (u.sum fun _ e => e) = 0) : u = 0 := by
  rw [Finsupp.sum] at h
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hi
  exact hi ((Finset.sum_eq_zero_iff.mp h) i (Finsupp.mem_support_iff.mpr hi))
theorem exists_single_add (u : σ →₀ ℕ) (h : u ≠ 0) :
    ∃ (v : σ) (u' : σ →₀ ℕ), u = Finsupp.single v 1 + u' ∧
      (u.sum fun _ e => e) = 1 + (u'.sum fun _ e => e) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, u v ≠ 0 := by
    by_contra hcon
    refine h (Finsupp.ext (fun a => ?_))
    by_contra ha
    exact hcon ⟨a, ha⟩
  have hu : u = Finsupp.single v 1 + (u - Finsupp.single v 1) := by
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with hvi
    · subst hvi; omega
    · omega
  refine ⟨v, u - Finsupp.single v 1, hu, ?_⟩
  conv_lhs => rw [hu]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem absorb_monomial (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ) (c : ZMod 2) (f : MvPolynomial σ (ZMod 2)),
      (u.sum fun _ e => e) = n → f ∈ C → n + f.totalDegree ≤ D → monomial u c * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u c f hu hf _
    have h0 : u = 0 := eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : monomial (0 : σ →₀ ℕ) c = MvPolynomial.C c := rfl
    rw [hm, C_mul']
    exact C.smul_mem c hf
  | succ n ih =>
    intro u c f hu hf hd
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
    rw [monomial_single_add, pow_one, mul_assoc]
    have hm := ih u' c f (by omega) hf (by omega)
    refine hC.mulX v _ hm ?_
    have h1 := totalDegree_mul (monomial u' c) f
    have h2 : (monomial u' c).totalDegree ≤ (u'.sum fun _ e => e) := totalDegree_monomial_le u' c
    omega
theorem absorb (hC : DegClosed C D) {f g : MvPolynomial σ (ZMod 2)} (hf : f ∈ C)
    (h : g.totalDegree + f.totalDegree ≤ D) : g * f ∈ C := by
  have e : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    rw [← Finset.sum_mul, support_sum_monomial_coeff]
  rw [e]
  refine C.sum_mem fun u hu => ?_
  have h1 : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact absorb_monomial hC _ u _ f rfl hf (by omega)
theorem idem_monomial (hC : DegClosed C D) (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ 1) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · by_cases h0 : u = 0
    · subst h0
      have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [hm, one_mul, CharTwo.add_self_eq_zero]
      exact C.zero_mem
    · obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
      have hu' : u' = 0 := eq_zero_of_sum_eq_zero u' (by omega)
      subst hu'
      rw [add_zero]
      exact hC.bool v
theorem affine_idem (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ 1) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial hC a (c a) (hs a (Finset.mem_insert_self a s)))
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errKer_le (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errKer C M k ≤ polyLE σ k := by
  unfold errKer
  exact inf_le_left
theorem errKer_finite [Fintype σ] (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    FiniteDimensional (ZMod 2) ↥(errKer C M k) :=
  Submodule.finiteDimensional_of_le (errKer_le M k)
theorem mem_errKer_zMul {P : MvPolynomial σ (ZMod 2)} {G : Set (MvPolynomial σ (ZMod 2))}
    {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C (zMul P G) k ↔ f.totalDegree ≤ k ∧ ∀ g ∈ G, P * g * f ∈ C := by
  rw [mem_errKer]
  simp [zMul]
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : ∑ j ∈ Finset.range 1, n.choose j ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have h1 : ∑ j ∈ Finset.range 1, n.choose j = 1 := by simp
  omega
theorem numMono_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : numMono n k ≤ numMono n k' := by
  unfold numMono
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
theorem errRank_one_le [Fintype σ] (hC : DegClosed C D) {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {K : ℕ} (hD : K + 1 ≤ D) :
    errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := mem_polyLE.mp hf.2
    rw [mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact absorb hC hfC (by omega)
  haveI := errKer_finite (C := C) (zMul 1 ↑G) K
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem gain (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := h35 σ C D a (K - 1) {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - 1) ≤ 2 * errRank C {P * q} (K - 1) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ 1 := deg_le_one_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := affine_idem hC q hq1
  have hidem2 := deg_idem_le hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - 1) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - 1) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := deg_mul_le hP hfd
      exact absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - 1)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [mem_errKer_zMul]
      have hd0 := deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact absorb hC hidem (by omega)
    · intro f hf
      rw [mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact absorb hC (hf.2 g hg) (by omega)
  haveI := DegSizeRank.finite_restrictTotalDegree (σ := σ) (K - 1)
  haveI := errKer_finite (C := C) (zMul P ↑G) K
  haveI := errKer_finite (C := C) {P * q} (K - 1)
  haveI := errKer_finite (C := C) (zMul (P * (1 + q)) ↑G) K
  have key := finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - 1))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - 1)) ≤ finrank (ZMod 2) (polyLE σ (K - 1)) :=
    Submodule.finrank_mono (errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith {c c' c1 h n K t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - 1) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta n K) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta n K) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast numMono_pos n K
  have hN1 : (numMono n (K - 1) : ℝ) ≤ numMono n K := by
    exact_mod_cast numMono_mono n (Nat.sub_le K 1)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - 1) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta n K := by
    have hle : eta n K ≤ 1 := by
      unfold eta
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta n K ≤ c1 / 2 := by
    unfold eta
    have e1 : (c : ℝ) * (numMono n (K - 1) / (2 * numMono n K))
        = (c * numMono n (K - 1)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta n K) := by linarith
    _ ≤ (h * (1 - eta n K) ^ t) * (1 - eta n K) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta n K) ^ (t + 1) := by ring
theorem greedy (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le hC hG' (by omega)
  | succ t ih =>
    intro hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t :=
      deg_prod_le qs (fun j => deg_le_one_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain h35 σ C D t K _ G hC hP hG hK (by omega)
    have h41' := h41 σ C D t K _ (↑G) hC hP hG' (by omega) (K - 1) K (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith hgain h41' hb
theorem common (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy h41 h35 σ C D K t (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    codim_iInf (polyLE σ K) (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩, fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
end C.DegSizeGain
namespace C.DegSizeGainK
open MvPolynomial Module PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
noncomputable def eta_k (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)
theorem eta_k_one (n K : ℕ) : eta_k n K 1 = eta n K := rfl
section Poly
variable {σ : Type}
theorem deg_one_add_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (1 + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)
theorem deg_idem_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (q * q + q).totalDegree ≤ 2 * k :=
  (totalDegree_add _ _).trans (max_le ((DegSizeGain.deg_mul_le hq hq).trans (by omega))
    (by omega))
theorem deg_le_of_mem_span {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k :=
  DegSizeGain.mem_polyLE.mp
    (Submodule.span_le.mpr (fun g hg => DegSizeGain.mem_polyLE.mpr (hG g hg)) hq)
theorem deg_prod_le_k {k t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, k :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le_k (h j))
    _ = t * k := by simp
variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem idem_monomial_one (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ), (u.sum fun _ e => e) = n → 2 * n ≤ D →
      monomial u (1 : ZMod 2) * monomial u 1 + monomial u 1 ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    have h0 : u = 0 := DegSizeGain.eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [hm, one_mul, CharTwo.add_self_eq_zero]
    exact C.zero_mem
  | succ n ih =>
    intro u hu hD
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := DegSizeGain.exists_single_add u h0
    have hm' := ih u' (by omega) (by omega)
    have hmd : (monomial u' (1 : ZMod 2)).totalDegree ≤ n := by
      have h2 : (monomial u' (1 : ZMod 2)).totalDegree ≤ (u'.sum fun _ e => e) :=
        totalDegree_monomial_le u' 1
      omega
    have e0 : monomial (Finsupp.single v 1 + u') (1 : ZMod 2) = X v * monomial u' 1 := by
      rw [monomial_single_add, pow_one]
    rw [e0]
    generalize monomial u' (1 : ZMod 2) = m at hm' hmd ⊢
    have e : X v * m * (X v * m) + X v * m
        = (m * m) * (X v * X v + X v) + X v * (m * m + m) := by
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) *
        CharTwo.add_self_eq_zero (X v * (m * m))
    rw [e]
    refine C.add_mem ?_ (hC.mulX v _ hm' ?_)
    · refine DegSizeGain.absorb hC (hC.bool v) ?_
      have h1 := DegSizeGain.deg_mul_le hmd hmd
      have h2 := DegSizeRank.bool_totalDegree_le v
      omega
    · have h1 := deg_idem_le_k hmd
      omega
theorem idem_monomial_k (hC : DegClosed C D) {k : ℕ} (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ k) (hD : 2 * k ≤ D) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · exact idem_monomial_one hC _ u rfl (by omega)
theorem idem_k (hC : DegClosed C D) {k : ℕ} (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ k) (hD : 2 * k ≤ D) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ k) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial_k hC a (c a) (hs a (Finset.mem_insert_self a s)) hD)
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h
theorem errRank_one_le_k [Fintype σ] (hC : DegClosed C D) {k : ℕ}
    {G : Set (MvPolynomial σ (ZMod 2))} (hG : ∀ g ∈ G, g.totalDegree ≤ k) {K : ℕ}
    (hD : K + k ≤ D) : errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := DegSizeGain.mem_polyLE.mp hf.2
    rw [DegSizeGain.mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact DegSizeGain.absorb hC hfC (by omega)
  haveI := DegSizeGain.errKer_finite (C := C) (zMul 1 ↑G) K
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega
end Poly
theorem monoRank_mul :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b K : ℕ)
      (M : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ m ∈ M, m.totalDegree ≤ b) → b + K ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C M l' * numMono (Fintype.card σ) l
          ≤ errRank C M l * numMono (Fintype.card σ) l' := by
  intro σ _ C D b K M hC hmdeg hD
  have hX : ∀ p ∈ DegSizeRank.annih C M, p.totalDegree < K → ∀ i : σ,
      X i * p ∈ DegSizeRank.annih C M := by
    intro p hp hdeg i
    rw [DegSizeRank.mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ DegSizeRank.annih C M := by
    intro d i hd
    rw [DegSizeRank.mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine DegSizeRank.absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := DegSizeRank.totalDegree_monomial_one d
    have h3 := DegSizeRank.bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C M (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C M j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [DegSizeRank.errRank_eq_map, DegSizeRank.errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (DegSizeRank.annih C M) K hX hB j hj
  intro l l' hll' hl'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hll'
  exact DegSizeRank.iterate_ratio (fun j => errRank C M j)
    (fun j => numMono (Fintype.card σ) j) K (fun j => DegSizeGain.numMono_pos _ j) step l t hl'
theorem monoRank_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → a + K + k ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C (zMul P G) l' * numMono (Fintype.card σ) l
          ≤ errRank C (zMul P G) l * numMono (Fintype.card σ) l' := by
  intro σ _ C D a K k P G hC hP hG hD
  refine monoRank_mul σ C D (a + k) K (zMul P G) hC ?_ (by omega)
  rintro _ ⟨g, hg, rfl⟩
  exact DegSizeGain.deg_mul_le hP (hG g hg)
theorem rankRetention_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D b l k : ℕ) (H : Set (MvPolynomial σ (ZMod 2)))
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ k) →
      b + l + 2 * k ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) l
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
  classical
  intro σ _ C D b l k H G hC hH hG hD
  let gfun : ↥G → MvPolynomial σ (ZMod 2) := fun i => i
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  have hcd : ∀ c : ↥G → ZMod 2, (comb gfun c).totalDegree ≤ k := by
    intro c
    refine DegSizeGain.mem_polyLE.mp ?_
    unfold comb
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (DegSizeGain.mem_polyLE.mpr (hG i i.2))
  have hmul : ∀ (c c' : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * comb gfun c * hfun α ∈ C → f * comb gfun c * comb gfun c' * hfun α ∈ C := by
    intro c c' α f hf hmem
    have e : f * comb gfun c * comb gfun c' * hfun α
        = comb gfun c' * (f * comb gfun c * hfun α) := by ring
    rw [e]
    refine DegSizeGain.absorb hC hmem ?_
    have h1 : (f * comb gfun c * hfun α).totalDegree ≤ l + k + b := DegSizeGain.deg_mul_le
      (DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hcd c)) (hH α α.2)
    have h2 := hcd c'
    omega
  have hidem : ∀ (c : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * (comb gfun c * comb gfun c + comb gfun c) * hfun α ∈ C := by
    intro c α f hf
    have e : f * (comb gfun c * comb gfun c + comb gfun c) * hfun α
        = (f * hfun α) * (comb gfun c * comb gfun c + comb gfun c) := by ring
    rw [e]
    refine DegSizeGain.absorb hC (idem_k hC _ (hcd c) (by omega)) ?_
    have h1 : (f * hfun α).totalDegree ≤ l + b :=
      DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hH α α.2)
    have h2 := deg_idem_le_k (hcd c)
    omega
  obtain ⟨c, hc⟩ := rank_retention_mul (ι := ↥G) (τ := ↥H) C (polyLE σ l) gfun hfun
    hmul hidem
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb gfun c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • (i : MvPolynomial σ (ZMod 2)) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ l) hfun (gfun i)))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ l) hfun (gfun ⟨g, hg⟩) f = 0 := congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ l) hfun _ f).1 hz' ⟨h, hh⟩
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ l) hfun (gfun i) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * gfun i * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ l) hfun (comb gfun c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩
theorem gain_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K →
      a + K + 2 * k ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - k)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K k P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := rankRetention_used_k σ C D a (K - k) k {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - k) ≤ 2 * errRank C {P * q} (K - k) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ k := deg_le_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := idem_k hC q hq1 (by omega)
  have hidem2 := deg_idem_le_k hq1
  refine ⟨q, hqs, ?_⟩
  have hi : polyLE σ (K - k) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - k) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [DegSizeGain.mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := DegSizeGain.deg_mul_le hP hfd
      exact DegSizeGain.absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  have hii : (polyLE σ (K - k)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [DegSizeGain.mem_errKer_zMul]
      have hd0 := DegSizeGain.deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact DegSizeGain.absorb hC hidem (by omega)
    · intro f hf
      rw [DegSizeGain.mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le_k hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact DegSizeGain.absorb hC (hf.2 g hg) (by omega)
  haveI := DegSizeRank.finite_restrictTotalDegree (σ := σ) (K - k)
  haveI := DegSizeGain.errKer_finite (C := C) (zMul P ↑G) K
  haveI := DegSizeGain.errKer_finite (C := C) {P * q} (K - k)
  haveI := DegSizeGain.errKer_finite (C := C) (zMul (P * (1 + q)) ↑G) K
  have key := DegSizeGain.finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - k))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - k)) ≤ finrank (ZMod 2) (polyLE σ (K - k)) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega
theorem greedy_arith_k {c c' c1 h n K k t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - k) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta_k n K k) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta_k n K k) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - k) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta_k n K k := by
    have hle : eta_k n K k ≤ 1 := by
      unfold eta_k
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta_k n K k ≤ c1 / 2 := by
    unfold eta_k
    have e1 : (c : ℝ) * (numMono n (K - k) / (2 * numMono n K))
        = (c * numMono n (K - k)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta_k n K k) := by linarith
    _ ≤ (h * (1 - eta_k n K k) ^ t) * (1 - eta_k n K k) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta_k n K k) ^ (t + 1) := by ring
theorem greedy_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t := by
  intro σ _ C D K t k G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le_k hC hG' (by omega)
  | succ t ih =>
    intro hD
    have et : (t + 1) * k = t * k + k := by ring
    rw [et] at hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
      deg_prod_le_k qs (fun j => deg_le_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain_k σ C D (t * k) K k _ G hC hP hG hK (by omega)
    have h41' := monoRank_used_k σ C D (t * k) K k _ (↑G) hC hP hG' (by omega) (K - k) K
      (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith_k hgain h41' hb
theorem common_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      (S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t k ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy_k σ C D K t k (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact DegSizeGain.mem_polyLE.mpr (by simp)
    exact h1 hone.1
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    DegSizeGain.codim_iInf (polyLE σ K)
      (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => DegSizeGain.errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, DegSizeGain.mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩,
    fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (DegSizeGain.mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)
theorem stmt41_of_k : DegSizeGain.Stmt41 := by
  intro σ _ C D a K P G hC hP hG hD
  exact monoRank_used_k σ C D a K 1 P G hC hP hG hD
theorem stmt35_of_k : DegSizeGain.Stmt35 := by
  intro σ _ C D b l H G hC hH hG hD
  exact rankRetention_used_k σ C D b l 1 H G hC hH hG (by omega)
theorem gain_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  exact gain_k σ C D a K 1 P G hC hP hG hK (by omega)
theorem greedy_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK hD
  exact greedy_k σ C D K t 1 G hC hG hK (by omega)
theorem common_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  exact common_k σ C D K t 1 ι S G hC h1 hG hK (by omega) hlt
end C.DegSizeGainK
namespace C.DegSizeArith
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
section Completeness
variable {V : Type}
noncomputable def fac (a : V → Bool) (v : V) : MvPolynomial V (ZMod 2) :=
  if a v = true then X v else 1 + X v
theorem totalDegree_fac_le (a : V → Bool) (v : V) : (fac a v).totalDegree ≤ 1 := by
  unfold fac
  split_ifs
  · rw [totalDegree_X]
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    simp
theorem totalDegree_prod_fac_le (a : V → Bool) (S : Finset V) :
    (∏ v ∈ S, fac a v).totalDegree ≤ S.card := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ v ∈ S, (fac a v).totalDegree ≤ ∑ _v ∈ S, 1 :=
        Finset.sum_le_sum fun v _ => totalDegree_fac_le a v
    _ = S.card := by simp
theorem eval_fac (a : V → Bool) (x : V → ZMod 2) (v : V) :
    eval x (fac a v) = if (x v = 1 ↔ a v = true) then 1 else 0 := by
  unfold fac
  have hx : x v = 0 ∨ x v = 1 := by
    generalize x v = c
    revert c
    decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hx with h | h <;> cases a v <;> simp [h, h11]
theorem complete_deg :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → ¬ Satisfiable F → w ≤ D → Fintype.card V ≤ D →
      PCRefutable (cnfSystem F) D := by
  classical
  intro V _ _ F w D hw hunsat hwD hVD
  have hfals : ∀ a : V → Bool, ∃ A ∈ F, ¬ ClauseSat a A := by
    intro a
    by_contra hb
    exact hunsat ⟨a, fun A hA => by_contra fun hn => hb ⟨A, hA, hn⟩⟩
  have hind : ∀ a : V → Bool, PCDerivable (cnfSystem F) D (∏ v, fac a v) := by
    intro a
    obtain ⟨A, hAF, hA⟩ := hfals a
    have hne : ∀ l ∈ A, a l.1 = !l.2 := by
      intro l hl
      have h0 : ¬ a l.1 = l.2 := fun h => hA ⟨l, hl, h⟩
      revert h0
      cases a l.1 <;> cases l.2 <;> simp
    have hinj : Set.InjOn (fun l : Literal V => l.1) (↑A : Set (Literal V)) := by
      intro l hl l' hl' h
      have h' : l.1 = l'.1 := h
      have h1 := hne l hl
      have h2 := hne l' hl'
      rw [h'] at h1
      have h3 : (!l.2) = !l'.2 := h1.symm.trans h2
      have h4 : l.2 = l'.2 := by simpa using h3
      exact Prod.ext h' h4
    set S : Finset V := A.image (fun l => l.1) with hS
    have hcl : clausePoly A = ∏ v ∈ S, fac a v := by
      rw [hS, Finset.prod_image hinj]
      unfold clausePoly
      refine Finset.prod_congr rfl fun l hl => ?_
      have h1 := hne l hl
      unfold fac
      rw [h1]
      cases l.2 <;> simp
    have hsplit : ∏ v, fac a v = (∏ v ∈ Sᶜ, fac a v) * clausePoly A := by
      rw [hcl, Finset.prod_compl_mul_prod]
    have hdegc : (clausePoly A).totalDegree ≤ S.card := by
      rw [hcl]
      exact totalDegree_prod_fac_le a S
    have hScard : S.card ≤ w := Finset.card_image_le.trans (hw A hAF)
    have hax : PCDerivable (cnfSystem F) D (clausePoly A) :=
      .ax (Or.inr ⟨A, hAF, rfl⟩) (hdegc.trans (hScard.trans hwD))
    rw [hsplit]
    refine pcDerivable_mono (pcDerivable_mul_left hax (∏ v ∈ Sᶜ, fac a v)) ?_ subset_rfl
    refine max_le le_rfl ?_
    have h1 := totalDegree_prod_fac_le a Sᶜ
    have h2 : S.card + Sᶜ.card = Fintype.card V := Finset.card_add_card_compl S
    omega
  set p : MvPolynomial V (ZMod 2) := ∑ a : V → Bool, ∏ v, fac a v with hp
  have hpder : PCDerivable (cnfSystem F) D p := pcDerivable_sum _ _ fun a _ => hind a
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hvan : ∀ x : V → ZMod 2, eval x (1 + p) = 0 := by
    intro x
    have hx : eval x p = 1 := by
      rw [hp, map_sum]
      simp only [map_prod, eval_fac, Finset.prod_boole]
      rw [Finset.sum_eq_single (fun v => decide (x v = 1))]
      · simp
      · intro b _ hb
        split_ifs with h
        · exfalso
          apply hb
          funext v
          have := h v (Finset.mem_univ v)
          cases hbv : b v <;> simp_all
        · rfl
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [map_add, map_one, hx, h11]
  have hdeg : (1 + p).totalDegree ≤ D := by
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · rw [totalDegree_one]
      exact Nat.zero_le _
    · rw [hp]
      refine totalDegree_finsetSum_le fun a _ => ?_
      refine (totalDegree_prod_fac_le a Finset.univ).trans ?_
      rwa [Finset.card_univ]
  have h1 := BoolVanish.vanish_derivable V (cnfSystem F) D (1 + p)
    (fun v => Or.inl ⟨v, rfl⟩) hdeg hvan
  have h2 := PCDerivable.add h1 hpder
  have e : 1 + p + p = 1 := by
    rw [add_assoc, ← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul, add_zero]
  rw [e] at h2
  exact h2
end Completeness
section Binomial
theorem numMono_succ (n k : ℕ) : numMono n (k + 1) = numMono n k + n.choose (k + 1) := by
  unfold numMono
  rw [Finset.sum_range_succ]
theorem choose_le_numMono (n k : ℕ) : n.choose k ≤ numMono n k := by
  unfold numMono
  exact Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
    (Finset.self_mem_range_succ k)
theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : n.choose 0 ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.succ_pos k))
  rw [Nat.choose_zero_right] at h
  exact h
theorem numMono_ratio (n k : ℕ) (hk : k ≤ n) :
    (k + 1) * numMono n (k + 1) ≤ (n + 1) * numMono n k := by
  have h1 : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq n k
  have h2 := choose_le_numMono n k
  have h3 : n.choose k * (n - k) ≤ numMono n k * (n - k) := Nat.mul_le_mul_right _ h2
  have h4 : numMono n k * (k + 1) + numMono n k * (n - k) = numMono n k * (n + 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [numMono_succ]
  calc (k + 1) * (numMono n k + n.choose (k + 1))
      = numMono n k * (k + 1) + n.choose (k + 1) * (k + 1) := by ring
    _ ≤ numMono n k * (k + 1) + numMono n k * (n - k) := by rw [h1]; exact Nat.add_le_add_left h3 _
    _ = (n + 1) * numMono n k := by rw [h4]; ring
theorem eta_le_one (n K : ℕ) (hK : 1 ≤ K) : eta n K ≤ 1 := by
  unfold eta
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hpos : (0 : ℝ) < numMono n (k + 1) := by exact_mod_cast numMono_pos n (k + 1)
  have hle : (numMono n k : ℝ) ≤ numMono n (k + 1) := by
    exact_mod_cast (numMono_succ n k) ▸ Nat.le_add_right _ _
  rw [Nat.add_sub_cancel, div_le_one (by positivity)]
  linarith
theorem eta_ge : ∀ n K : ℕ, 1 ≤ K → K ≤ n + 1 → (K : ℝ) / (2 * (n + 1)) ≤ eta n K := by
  intro n K hK hKn
  unfold eta
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hpos : (0 : ℝ) < numMono n (k + 1) := by exact_mod_cast numMono_pos n (k + 1)
  have hnat : (((k + 1 : ℕ) : ℝ)) * numMono n (k + 1) ≤ ((n : ℝ) + 1) * numMono n k := by
    exact_mod_cast numMono_ratio n k (by omega)
  have hn : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  rw [Nat.add_sub_cancel, div_le_div_iff₀ hn (by positivity)]
  nlinarith
end Binomial
end C.DegSizeArith
namespace C.LinKAsm
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.LinKPlan C.DegSizePlan
def StmtSimRefutation : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
def StmtArith : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t) →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
def StmtAssembly : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π → ¬ PCRefutable (cnfSystem F) D →
    k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - etaK (Fintype.card V) K k) ^ t
def StmtGeneral : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
theorem term_card {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | cut _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
  | weak _ _ _ hk ih =>
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact hk
      · exact ih L hL
theorem etaK_le_one (n K k : ℕ) : etaK n K k ≤ 1 := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  unfold etaK
  exact (div_le_one (by positivity)).mpr (by linarith)
theorem assembly (hSim : StmtSimRefutation) : StmtAssembly := by
  classical
  intro V _ _ F π k w D K t hk hw href hnr hkK hB
  by_contra hlt
  rw [not_le] at hlt
  have hk2 : 2 * k ≤ 2 * t * k + 2 * k := Nat.le_add_left _ _
  have hD2 : 2 ≤ D := by omega
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure (cnfSystem F) D hD2 (fun v => Or.inl ⟨v, rfl⟩)
  have h1 : (1 : MvPolynomial V (ZMod 2)) ∉ pcClosure (cnfSystem F) D := hnr
  have hnn : (0 : ℝ) ≤ (1 - etaK (Fintype.card V) K k) ^ t :=
    pow_nonneg (sub_nonneg.mpr (etaK_le_one _ K k)) t
  have hcard : (π.toFinset.card : ℝ) ≤ (π.length : ℝ) := by
    exact_mod_cast List.toFinset_card_le π
  have hS : (π.toFinset.card : ℝ) * (1 - DegSizeGainK.eta_k (Fintype.card V) K k) ^ t < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcard hnn) hlt
  have htk : t * k + k ≤ 2 * t * k + 2 * k := by nlinarith
  obtain ⟨f, qs, hf, hfC, hspan, hmem⟩ :=
    DegSizeGainK.common_k V (pcClosure (cnfSystem F) D) D K t k (LinKLine V) π.toFinset
      (fun L => L.image (fun T => termPoly T)) hC h1
      (by
        intro L hL g hg
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hg
        exact le_trans (totalDegree_termPoly_le T)
          (term_card href.1 L (List.mem_toFinset.mp hL) T hT))
      hkK (by omega) hS
  apply hfC
  refine hSim V F π k w D K t f qs hk hw href hB hf ?_ ?_
  · intro L hL j
    have := hspan L (List.mem_toFinset.mpr hL) j
    simpa [lineInputs, Finset.coe_image] using this
  · intro L hL T hT
    exact hmem L (List.mem_toFinset.mpr hL) (termPoly T) (Finset.mem_image_of_mem _ hT)
theorem degree_to_size_k (hSim : StmtSimRefutation) (hArith : StmtArith) : StmtGeneral := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href
  exact hArith V F π k w D hw hk hkD hwD hnr href
    (fun K t hkK hB => assembly hSim V F π k w D K t hk hw href hnr hkK hB)
end C.LinKAsm
namespace C.Helpers.LinKOne
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]
def up (C : LinClause V) : LinKLine V := C.image (fun q => ({q} : LinTerm V))
theorem up_card (C : LinClause V) : ∀ T ∈ up C, T.card ≤ 1 := by
  intro T hT
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hT
  simp
theorem up_erase (C : LinClause V) (q : LinEq V) : up (C.erase q) = (up C).erase {q} :=
  Finset.image_erase Finset.singleton_injective C q
theorem forward {F : Set (LinClause V)} {π : List (LinClause V)} (h : IsLinDerivation F π) :
    IsLinKDerivation 1 IsLinKWeakening (up '' F) (π.map up) := by
  induction h with
  | nil => exact IsLinKDerivation.nil
  | ax _ hCF ih => exact IsLinKDerivation.ax ih ⟨_, hCF, rfl⟩ (up_card _)
  | @res π C D R _ hC hD hR ih =>
    obtain ⟨f, hfC, hfD, rfl⟩ := hR
    refine IsLinKDerivation.cut ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD)
      ⟨{(f, false)}, Finset.mem_image_of_mem _ hfC, ?_, ?_⟩ (up_card _)
    · intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact Finset.mem_image_of_mem _ hfD
    · rw [Finset.image_singleton, Finset.sdiff_singleton_eq_erase, ← up_erase, ← up_erase]
      exact Finset.image_union _ _
  | @weak π C D _ hC hw ih =>
    refine IsLinKDerivation.weak ih (List.mem_map_of_mem hC) ?_ (up_card _)
    intro T hT
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
    right
    intro a ha
    obtain ⟨q', hq', hs⟩ := hw a ⟨q, hq, ha q (Finset.mem_singleton_self q)⟩
    exact ⟨q', Finset.mem_image_of_mem _ hq', hs⟩
def down (L : LinKLine V) : LinClause V :=
  if (∅ : LinTerm V) ∈ L then {((∅ : Finset V), false)} else L.biUnion id
theorem mem_biUnion_iff {L : LinKLine V} (hk : ∀ T ∈ L, T.card ≤ 1) (q : LinEq V) :
    q ∈ L.biUnion id ↔ ({q} : LinTerm V) ∈ L := by
  constructor
  · intro hq
    obtain ⟨T, hT, hqT⟩ := Finset.mem_biUnion.mp hq
    have hTq : T = {q} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hqT, fun x hx => Finset.card_le_one.mp (hk T hT) x hx q hqT⟩
    exact hTq ▸ hT
  · intro hq
    exact Finset.mem_biUnion.mpr ⟨{q}, hq, Finset.mem_singleton_self q⟩
theorem down_sat (a : V → Bool) {L : LinKLine V} (hk : ∀ T ∈ L, T.card ≤ 1) :
    LinClauseSat a (down L) ↔ LinKLineSat a L := by
  unfold down
  split_ifs with h0
  · constructor
    · intro _
      exact ⟨∅, h0, fun q hq => absurd hq (Finset.notMem_empty q)⟩
    · intro _
      exact ⟨(∅, false), Finset.mem_singleton_self _, by simp [LinEqSat]⟩
  · constructor
    · rintro ⟨q, hq, hs⟩
      refine ⟨{q}, (mem_biUnion_iff hk q).mp hq, fun q' hq' => ?_⟩
      rw [Finset.mem_singleton.mp hq']
      exact hs
    · rintro ⟨T, hT, hs⟩
      have hne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact h0 hT
      obtain ⟨q, hq⟩ := hne
      exact ⟨q, Finset.mem_biUnion.mpr ⟨T, hT, hq⟩, hs q hq⟩
theorem down_up (C : LinClause V) : down (up C) = C := by
  have h0 : (∅ : LinTerm V) ∉ up C := by
    intro h
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp h
    exact Finset.singleton_ne_empty q hq
  unfold down
  simp only [h0, ↓reduceIte]
  ext q
  rw [mem_biUnion_iff (up_card C)]
  exact ⟨fun h => by
    obtain ⟨q', hq', hqq⟩ := Finset.mem_image.mp h
    exact Finset.singleton_injective hqq ▸ hq', fun h => Finset.mem_image_of_mem _ h⟩
omit [DecidableEq V] in
theorem sat_mono {a : V → Bool} {L M : LinKLine V} (h : L ⊆ M) (hs : LinKLineSat a L) :
    LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  exact ⟨T, h hT, hTs⟩
omit [DecidableEq V] in
theorem weakening_sound {a : V → Bool} {L M : LinKLine V} (h : IsLinKWeakening L M)
    (hs : LinKLineSat a L) : LinKLineSat a M := by
  obtain ⟨T, hT, hTs⟩ := hs
  rcases h T hT with ⟨S, hS, himp⟩ | hb
  · exact ⟨S, hS, himp a hTs⟩
  · obtain ⟨q, hq, hqs⟩ := hb a hTs
    refine ⟨{q}, hq, fun q' hq' => ?_⟩
    rw [Finset.mem_singleton.mp hq']
    exact hqs
theorem lines_card {k : ℕ} {W : LinKLine V → LinKLine V → Prop} {F : Set (LinKLine V)}
    {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil => intro L hL; simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with rfl | hL
    · exact hk
    · exact ih L hL
theorem cut_down {C D R : LinKLine V} (hkC : ∀ T ∈ C, T.card ≤ 1) (hkD : ∀ T ∈ D, T.card ≤ 1)
    (hkR : ∀ T ∈ R, T.card ≤ 1) (hcut : IsLinKCut C D R) :
    IsLinResolvent (down C) (down D) (down R) ∨ IsLinResolvent (down D) (down C) (down R) ∨
      (∀ a : V → Bool, LinClauseSat a (down C) → LinClauseSat a (down R)) ∨
      (∀ a : V → Bool, LinClauseSat a (down D) → LinClauseSat a (down R)) := by
  obtain ⟨T, hT, hneg, hR⟩ := hcut
  by_cases hTe : T = ∅
  · subst hTe
    right; right; right
    intro a hs
    refine (down_sat a hkR).mpr (sat_mono ?_ ((down_sat a hkD).mp hs))
    rw [hR, Finset.image_empty, Finset.sdiff_empty]
    exact Finset.subset_union_right
  · obtain ⟨e, rfl⟩ : ∃ e, T = {e} :=
      Finset.card_eq_one.mp (le_antisymm (hkC T hT)
        (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hTe)))
    have hD : ({negLinEq e} : LinTerm V) ∈ D := hneg e (Finset.mem_singleton_self e)
    rw [Finset.image_singleton, Finset.sdiff_singleton_eq_erase] at hR
    by_cases h0 : (∅ : LinTerm V) ∈ C ∨ (∅ : LinTerm V) ∈ D
    · right; right; left
      intro a _
      refine (down_sat a hkR).mpr ⟨∅, ?_, fun q hq => absurd hq (Finset.notMem_empty q)⟩
      rw [hR]
      rcases h0 with h0 | h0
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨(Finset.singleton_ne_empty e).symm, h0⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_erase.mpr ⟨(Finset.singleton_ne_empty _).symm, h0⟩)
    · have h0C : (∅ : LinTerm V) ∉ C := fun h => h0 (Or.inl h)
      have h0D : (∅ : LinTerm V) ∉ D := fun h => h0 (Or.inr h)
      have h0R : (∅ : LinTerm V) ∉ R := by
        rw [hR]
        intro h
        rcases Finset.mem_union.mp h with h | h
        · exact h0C (Finset.mem_of_mem_erase h)
        · exact h0D (Finset.mem_of_mem_erase h)
      have hdR : down R = (down C).erase e ∪ (down D).erase (negLinEq e) := by
        unfold down
        simp only [h0C, h0D, h0R, ↓reduceIte]
        ext q
        rw [mem_biUnion_iff hkR, Finset.mem_union, Finset.mem_erase, Finset.mem_erase,
          mem_biUnion_iff hkC, mem_biUnion_iff hkD, hR, Finset.mem_union, Finset.mem_erase,
          Finset.mem_erase, Ne, Ne, Finset.singleton_inj, Finset.singleton_inj]
      have heC : e ∈ down C := by
        unfold down
        simp only [h0C, ↓reduceIte]
        exact (mem_biUnion_iff hkC e).mpr hT
      have heD : negLinEq e ∈ down D := by
        unfold down
        simp only [h0D, ↓reduceIte]
        exact (mem_biUnion_iff hkD _).mpr hD
      rcases e with ⟨f, b⟩
      cases b
      · left
        exact ⟨f, heC, heD, hdR⟩
      · right; left
        exact ⟨f, heD, heC, hdR.trans (Finset.union_comm _ _)⟩
theorem andIntro_superset {C D R : LinKLine V} (hkR : ∀ T ∈ R, T.card ≤ 1)
    (h : IsLinKAndIntro C D R) : C ⊆ R ∨ D ⊆ R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  have hcard : (T₁ ∪ T₂).card ≤ 1 :=
    hkR _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  by_cases hT₁ : T₁ = ∅
  · right
    intro T hT
    by_cases hTT : T = T₂
    · subst hTT
      refine Finset.mem_union_right _ (Finset.mem_singleton.mpr ?_)
      rw [hT₁, Finset.empty_union]
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hTT, hT⟩))
  · left
    have heq : T₁ = T₁ ∪ T₂ :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left
        (hcard.trans (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT₁)))
    intro T hT
    by_cases hTT : T = T₁
    · subst hTT
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr heq)
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT⟩))
theorem backward {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation 1 IsLinKWeakening F π) :
    IsLinDerivation (down '' F) (π.map down) := by
  induction h with
  | nil => exact IsLinDerivation.nil
  | ax _ hCF _ ih => exact IsLinDerivation.ax ih ⟨_, hCF, rfl⟩
  | @cut π C D R hπ hC hD hcut hk ih =>
    have hkC := lines_card hπ C hC
    have hkD := lines_card hπ D hD
    rcases cut_down hkC hkD hk hcut with h | h | h | h
    · exact IsLinDerivation.res ih (List.mem_map_of_mem hC) (List.mem_map_of_mem hD) h
    · exact IsLinDerivation.res ih (List.mem_map_of_mem hD) (List.mem_map_of_mem hC) h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hC) h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hD) h
  | @andIntro π C D R hπ hC hD hand hk ih =>
    have hkC := lines_card hπ C hC
    have hkD := lines_card hπ D hD
    rcases andIntro_superset hk hand with h | h
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hC)
        (fun a hs => (down_sat a hk).mpr (sat_mono h ((down_sat a hkC).mp hs)))
    · exact IsLinDerivation.weak ih (List.mem_map_of_mem hD)
        (fun a hs => (down_sat a hk).mpr (sat_mono h ((down_sat a hkD).mp hs)))
  | @weak π C D hπ hC hw hk ih =>
    have hkC := lines_card hπ C hC
    exact IsLinDerivation.weak ih (List.mem_map_of_mem hC)
      (fun a hs => (down_sat a hk).mpr (weakening_sound hw ((down_sat a hkC).mp hs)))
theorem lin_iff_linK_one (F : Set (Clause V)) (n : ℕ) :
    (∃ π : List (LinClause V), IsLinRefutation F π ∧ π.length = n) ↔
      (∃ π : List (LinKLine V), IsLinKRefutation 1 F π ∧ π.length = n) := by
  constructor
  · rintro ⟨π, ⟨hd, he⟩, rfl⟩
    refine ⟨π.map up, ⟨?_, List.mem_map.mpr ⟨∅, he, rfl⟩⟩, List.length_map _⟩
    have h := forward hd
    rw [Set.image_image] at h
    exact h
  · rintro ⟨π, ⟨hd, he⟩, rfl⟩
    refine ⟨π.map down, ⟨?_, List.mem_map.mpr ⟨∅, he, by simp [down]⟩⟩, List.length_map _⟩
    have h := backward hd
    rw [Set.image_image] at h
    have hfun : (fun C : Clause V => down (linKOfClause C)) = fun C => linOfClause C :=
      funext fun C => down_up (linOfClause C)
    rw [hfun] at h
    exact h
end C.Helpers.LinKOne
namespace C.DegSizeArithK
private theorem linEqSat_singleton {V : Type} [DecidableEq V] (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]
open PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan
open C.DegSizeGainK (eta_k)
theorem numMono_ratio_iter (n j k : ℕ) (h : j + k ≤ n + 1) :
    (j + 1) ^ k * numMono n (j + k) ≤ (n + 1) ^ k * numMono n j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have hr := DegSizeArith.numMono_ratio n (j + k) (by omega)
    calc (j + 1) ^ (k + 1) * numMono n (j + (k + 1))
        = (j + 1) ^ k * ((j + 1) * numMono n (j + k + 1)) := by
          rw [show j + (k + 1) = j + k + 1 from rfl]; ring
      _ ≤ (j + 1) ^ k * ((j + k + 1) * numMono n (j + k + 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ ≤ (j + 1) ^ k * ((n + 1) * numMono n (j + k)) := Nat.mul_le_mul_left _ hr
      _ = (n + 1) * ((j + 1) ^ k * numMono n (j + k)) := by ring
      _ ≤ (n + 1) * ((n + 1) ^ k * numMono n j) := Nat.mul_le_mul_left _ ih'
      _ = (n + 1) ^ (k + 1) * numMono n j := by ring
theorem eta_k_nonneg (n K k : ℕ) : 0 ≤ eta_k n K k := by
  unfold eta_k
  positivity
theorem eta_k_le_half (n K k : ℕ) : eta_k n K k ≤ 1 / 2 := by
  unfold eta_k
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeArith.numMono_pos n K
  have hle : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith
theorem eta_k_le_one (n K k : ℕ) : eta_k n K k ≤ 1 :=
  (eta_k_le_half n K k).trans (by norm_num)
theorem one_sub_eta_k_nonneg (n K k : ℕ) : 0 ≤ 1 - eta_k n K k := by
  have := eta_k_le_one n K k
  linarith
theorem eta_k_ge (n K k : ℕ) (hk : k ≤ K) (hK : K ≤ n + 1) :
    (1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k ≤ eta_k n K k := by
  obtain ⟨j, rfl⟩ : ∃ j, K = j + k := ⟨K - k, by omega⟩
  have hnat := numMono_ratio_iter n j k hK
  unfold eta_k
  rw [Nat.add_sub_cancel]
  have hN : (0 : ℝ) < numMono n (j + k) := by
    exact_mod_cast DegSizeArith.numMono_pos n (j + k)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hr : ((j : ℝ) + 1) ^ k * (numMono n (j + k) : ℝ)
      ≤ ((n : ℝ) + 1) ^ k * (numMono n j : ℝ) := by exact_mod_cast hnat
  push_cast
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (pow_pos hn k) (by linarith)]
  nlinarith [hr]
theorem asm_of_max (n k w D : ℕ) (S : ℝ)
    (h : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D → 1 ≤ S * (1 - eta_k n K k) ^ t := by
  intro K t hk hb
  apply h K t hk
  have e : 2 * t * k = t * k + t * k := by ring
  rw [e] at hb ⊢
  rcases max_cases (t * k + t * k + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
    rw [h'] <;> omega
theorem exp_le_of_one_le (S x : ℝ) (t : ℕ) (hx : x ≤ 1) (h : 1 ≤ S * (1 - x) ^ t) :
    Real.exp ((t : ℝ) * x) ≤ S := by
  have hp0 : (0 : ℝ) ≤ (1 - x) ^ t := pow_nonneg (by linarith) t
  have hS : 0 ≤ S := by
    by_contra hc
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hp0
    linarith
  have hpow : (1 - x) ^ t ≤ Real.exp (-((t : ℝ) * x)) := by
    have h1 : 1 - x ≤ Real.exp (-x) := Real.one_sub_le_exp_neg x
    have h2 : (1 - x) ^ t ≤ Real.exp (-x) ^ t := pow_le_pow_left₀ (by linarith) h1 t
    rw [← Real.exp_nat_mul] at h2
    rwa [mul_neg] at h2
  have h3 : 1 ≤ S * Real.exp (-((t : ℝ) * x)) :=
    h.trans (mul_le_mul_of_nonneg_left hpow hS)
  have hpos : 0 < Real.exp ((t : ℝ) * x) := Real.exp_pos _
  calc Real.exp ((t : ℝ) * x) = Real.exp ((t : ℝ) * x) * 1 := (mul_one _).symm
    _ ≤ Real.exp ((t : ℝ) * x) * (S * Real.exp (-((t : ℝ) * x))) :=
        mul_le_mul_of_nonneg_left h3 hpos.le
    _ = S * (Real.exp ((t : ℝ) * x) * Real.exp (-((t : ℝ) * x))) := by ring
    _ = S := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
theorem size_core (n k K t : ℕ) (S : ℝ) (hkK : k ≤ K) (hKn : K ≤ n + 1)
    (h : 1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S := by
  have h1 := exp_le_of_one_le S (eta_k n K k) t (eta_k_le_one n K k) h
  refine le_trans (Real.exp_le_exp.mpr ?_) h1
  exact mul_le_mul_of_nonneg_left (eta_k_ge n K k hkK hKn) (Nat.cast_nonneg t)
theorem size_of_assembly_k (n k w D : ℕ) (S : ℝ)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K t : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hbud : K + 2 * t * k + 2 * k + w ≤ D) :
    Real.exp ((t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k)) ≤ S :=
  size_core n k K t S hkK hKn (hasm K t hkK hbud)
theorem final_aux (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (K : ℕ) (hkK : k ≤ K) (hKn : K ≤ n + 1) (hKw : 8 * K + 8 * w ≤ 5 * D)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ ((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * r ^ k) ≤ S := by
  obtain ⟨t, ht⟩ : ∃ t, t = D / (8 * k) := ⟨_, rfl⟩
  have htk : t * (8 * k) ≤ D := by rw [ht]; exact Nat.div_mul_le_self D (8 * k)
  have ht2 : 2 ≤ t := by rw [ht]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 8 * k * (t + 1) := by rw [ht]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : t * (8 * k) = 8 * (t * k) := by ring
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have e3 : 8 * k * (t + 1) = 8 * (t * k) + 8 * k := by ring
  have h2k : 2 * k ≤ t * k := Nat.mul_le_mul_right k ht2
  have hbud : K + 2 * t * k + 2 * k + w ≤ D := by rw [e2]; omega
  have hDt : D ≤ 12 * (t * k) := by omega
  have hcore := size_of_assembly_k n k w D S hasm K t hkK hKn hbud
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hDtR : (D : ℝ) ≤ 12 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have h1 : (D : ℝ) / (24 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hk24 : (0 : ℝ) ≤ (D : ℝ) / (24 * (k : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (24 * (k : ℝ)) * r ^ k
      ≤ (t : ℝ) / 2 * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * (((K - k + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring
theorem final_of_assembly_k (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (3 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 7 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (3 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr
theorem final_of_assembly_k_w4 (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / (6 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 4 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  have haD : 3 * D ≤ 16 * a := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have haR : 3 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have hr : (D : ℝ) / (6 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  rw [ha] at hr
  exact final_aux n k w D S hk hkD hasm K (by omega) (by omega) (by omega) _
    (div_nonneg hD0 (by linarith)) hr
theorem exp_beats_poly_k (n k A D c : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hn : 1 ≤ n)
    (hA : n ≤ A * D) :
    (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hAR : (n : ℝ) ≤ (A : ℝ) * (D : ℝ) := by exact_mod_cast hA
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc0 : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have h24 : (0 : ℝ) < 24 * (k : ℝ) := by linarith
  have h24A : (0 : ℝ) < 24 * (k : ℝ) * (A : ℝ) := mul_pos h24 hA0
  have hcA : (0 : ℝ) < (c : ℝ) * (A : ℝ) := mul_pos hc0 hA0
  have hcn : (0 : ℝ) < (c : ℝ) * (n : ℝ) := mul_pos hc0 hn0
  have h1 : (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) ≤ (D : ℝ) / (24 * (k : ℝ)) := by
    rw [div_le_div_iff₀ h24A h24]
    nlinarith [mul_le_mul_of_nonneg_left hAR h24.le]
  have h2 : 1 / ((c : ℝ) * (A : ℝ)) ≤ (D : ℝ) / ((c : ℝ) * (n : ℝ)) := by
    rw [div_le_div_iff₀ hcA hcn]
    nlinarith [mul_le_mul_of_nonneg_left hAR hc0.le]
  have h3 : (0 : ℝ) ≤ 1 / ((c : ℝ) * (A : ℝ)) := by positivity
  calc (n : ℝ) / (24 * (k : ℝ) * (A : ℝ) * ((c : ℝ) * (A : ℝ)) ^ k)
      = (n : ℝ) / (24 * (k : ℝ) * (A : ℝ)) * (1 / ((c : ℝ) * (A : ℝ))) ^ k := by
        rw [one_div_pow, div_mul_div_comm, mul_one]
    _ ≤ (D : ℝ) / (24 * (k : ℝ)) * ((D : ℝ) / ((c : ℝ) * (n : ℝ))) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ h3 h2 k) (pow_nonneg h3 k) (div_nonneg hD0 h24.le)
theorem final_linear_k (n k w D A : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) * (n : ℝ)) ≤ S := by
  refine le_trans (Real.exp_le_exp.mpr ?_) (final_of_assembly_k n k w D S hk hkD hwD hDn hasm)
  have h := exp_beats_poly_k n k A D 3 hk (by norm_num) (by omega) hA
  push_cast at h
  rw [one_div_mul_eq_div]
  exact h
theorem pow_le_exp_lin (c : ℝ) (hc : 0 < c) (d n : ℕ)
    (hn : ((d + 1).factorial : ℝ) / c ^ (d + 1) ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ Real.exp (c * (n : ℝ)) := by
  have hx : 0 ≤ c * (n : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg n)
  have h := Real.pow_div_factorial_le_exp _ hx (d + 1)
  refine le_trans ?_ h
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [le_div_iff₀ hF]
  have hn' : ((d + 1).factorial : ℝ) ≤ (n : ℝ) * c ^ (d + 1) :=
    (div_le_iff₀ (pow_pos hc _)).mp hn
  calc (n : ℝ) ^ d * ((d + 1).factorial : ℝ) ≤ (n : ℝ) ^ d * ((n : ℝ) * c ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = (c * (n : ℝ)) ^ (d + 1) := by ring
theorem final_superpoly_k (n k w D A d : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 8 * w ≤ D) (hDn : D < n) (hA : n ≤ A * D)
    (hasm : ∀ K t : ℕ, k ≤ K → K + 2 * t * k + 2 * k + w ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t)
    (hn : ((d + 1).factorial : ℝ) / (1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k)) ^ (d + 1)
      ≤ (n : ℝ)) :
    (n : ℝ) ^ d ≤ S := by
  have hApos : 0 < A := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hApos
  have hc : (0 : ℝ) < 1 / (24 * (k : ℝ) * (A : ℝ) * (3 * (A : ℝ)) ^ k) := by positivity
  exact (pow_le_exp_lin _ hc d n hn).trans (final_linear_k n k w D A S hk hkD hwD hDn hA hasm)
section Plan
theorem negLinEq_not_sat {V : Type} (a : V → Bool) (e : LinEq V) (h : LinEqSat a e) :
    ¬ LinEqSat a (negLinEq e) := by
  unfold LinEqSat at h
  unfold LinEqSat negLinEq
  intro h'
  cases hb : e.2 <;> simp_all
theorem linK_cut_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKCut C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) : LinKLineSat a R := by
  obtain ⟨T, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases hTT : T' = T
  · subst hTT
    refine ⟨U, Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hU, ?_⟩), hsU⟩
    intro hmem
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hmem
    exact negLinEq_not_sat a e (hs' e he) (hsU _ (Finset.mem_singleton_self _))
  · exact ⟨T', Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hTT, hT'⟩), hs'⟩
theorem linK_andIntro_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) (hC : LinKLineSat a C) (hD : LinKLineSat a D) :
    LinKLineSat a R := by
  obtain ⟨T₁, T₂, -, -, rfl⟩ := h
  obtain ⟨T', hT', hs'⟩ := hC
  obtain ⟨U, hU, hsU⟩ := hD
  by_cases h1 : T' = T₁
  · by_cases h2 : U = T₂
    · subst h1 h2
      refine ⟨T' ∪ U, Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
      intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hs' q hq
      · exact hsU q hq
    · exact ⟨U, Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h2, hU⟩)), hsU⟩
  · exact ⟨T', Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h1, hT'⟩)), hs'⟩
theorem linK_derivation_sound {V : Type} [DecidableEq V] (a : V → Bool) {k : ℕ}
    {F : Set (LinKLine V)} {π : List (LinKLine V)}
    (h : IsLinKDerivation k IsLinKWeakening F π) (ha : ∀ C ∈ F, LinKLineSat a C) :
    ∀ C ∈ π, LinKLineSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hCF _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact ha _ hCF
    · exact ih E hE
  | cut _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_cut_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | andIntro _ hC hD hR _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact linK_andIntro_sound a hR (ih _ hC) (ih _ hD)
    · exact ih E hE
  | weak _ hC hw _ ih =>
    intro E hE
    rcases List.mem_cons.mp hE with rfl | hE
    · exact LinKOne.weakening_sound hw (ih _ hC)
    · exact ih E hE
theorem linK_refutation_unsat :
    ∀ (V : Type) [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (π : List (LinKLine V)),
      IsLinKRefutation k F π → ¬ Satisfiable F := by
  rintro V _ F k π h ⟨a, ha⟩
  have hax : ∀ C ∈ (fun C => linKOfClause C) '' F, LinKLineSat a C := by
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨l, hl, hs⟩ := ha C hC
    refine ⟨{(({l.1} : Finset V), l.2)},
      Finset.mem_image.mpr ⟨(({l.1} : Finset V), l.2), Finset.mem_image.mpr ⟨l, hl, rfl⟩, rfl⟩,
      ?_⟩
    intro q hq
    rw [Finset.mem_singleton.mp hq]
    exact (linEqSat_singleton a l.1 l.2).mpr hs
  obtain ⟨T, hT, -⟩ := linK_derivation_sound a h.1 hax ∅ h.2
  exact absurd hT (Finset.notMem_empty T)
theorem etaK_le_one : ∀ n K k : ℕ, LinKPlan.etaK n K k ≤ 1 :=
  fun n K k => eta_k_le_one n K k
theorem etaK_ge :
    ∀ n K k : ℕ, k ≤ K → K ≤ n + 1 →
      (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k) ≤ LinKPlan.etaK n K k := by
  intro n K k hk hK
  have h := eta_k_ge n K k hk hK
  rw [div_pow] at h
  have e : (((K - k + 1 : ℕ) : ℝ)) ^ k / (2 * ((n : ℝ) + 1) ^ k)
      = (1 / 2 : ℝ) * ((((K - k + 1 : ℕ) : ℝ)) ^ k / ((n : ℝ) + 1) ^ k) := by ring
  rw [e]
  exact h
theorem final_plan_num (n k w D : ℕ) (S : ℝ) (hk : 1 ≤ k) (hkD : 16 * k ≤ D)
    (hwD : 4 * w ≤ D) (hDn : D < n)
    (hasm : ∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
      1 ≤ S * (1 - eta_k n K k) ^ t) :
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k) ≤ S := by
  obtain ⟨K, hK⟩ : ∃ K, K = D / 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = K - k + 1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = D / (4 * k) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = q - 1 := ⟨_, rfl⟩
  have hqk : q * (4 * k) ≤ D := by rw [hq]; exact Nat.div_mul_le_self D (4 * k)
  have hq4 : 4 ≤ q := by rw [hq]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlt : D < 4 * k * (q + 1) := by rw [hq]; exact Nat.lt_mul_div_succ D (by omega)
  have e1 : q * (4 * k) = 4 * (q * k) := by ring
  have e3 : 4 * k * (q + 1) = 4 * (q * k) + 4 * k := by ring
  have h4k : 4 * k ≤ q * k := Nat.mul_le_mul_right k hq4
  have etk : t * k = q * k - k := by rw [ht, Nat.sub_mul, one_mul]
  have e2 : 2 * t * k = 2 * (t * k) := by ring
  have hbud : K + max (2 * t * k + 2 * k) (t * k + w) ≤ D := by
    rw [e2]
    rcases max_cases (2 * (t * k) + 2 * k) (t * k + w) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      rw [h'] <;> omega
  have hDt : D ≤ 8 * (t * k) := by omega
  have haD : 7 * D ≤ 16 * a := by omega
  have hcore := size_core n k K t S (by omega) (by omega) (hasm K t (by omega) hbud)
  rw [← ha] at hcore
  refine le_trans (Real.exp_le_exp.mpr ?_) hcore
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hDtR : (D : ℝ) ≤ 8 * ((t : ℝ) * (k : ℝ)) := by exact_mod_cast hDt
  have haR : 7 * (D : ℝ) ≤ 16 * (a : ℝ) := by exact_mod_cast haD
  have hnR : (17 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 17 ≤ n)
  have h1 : (D : ℝ) / (16 * (k : ℝ)) ≤ (t : ℝ) / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [hDtR]
  have hr : (D : ℝ) / (4 * (n : ℝ)) ≤ (a : ℝ) / ((n : ℝ) + 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_right haR hn0.le, mul_nonneg hD0 (sub_nonneg.mpr hnR)]
  have hr0 : (0 : ℝ) ≤ (D : ℝ) / (4 * (n : ℝ)) := div_nonneg hD0 (by linarith)
  calc (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (n : ℝ))) ^ k
      ≤ (t : ℝ) / 2 * ((a : ℝ) / ((n : ℝ) + 1)) ^ k :=
        mul_le_mul h1 (pow_le_pow_left₀ hr0 hr k) (pow_nonneg hr0 k)
          (div_nonneg (Nat.cast_nonneg t) (by norm_num))
    _ = (t : ℝ) * ((1 / 2 : ℝ) * ((a : ℝ) / ((n : ℝ) + 1)) ^ k) := by ring
theorem final_of_assembly_plan :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
      (k w D : ℕ),
      (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
      ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
      (∀ K t : ℕ, k ≤ K → K + max (2 * t * k + 2 * k) (t * k + w) ≤ D →
        1 ≤ (π.length : ℝ) * (1 - LinKPlan.etaK (Fintype.card V) K k) ^ t) →
      Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
        ≤ (π.length : ℝ) := by
  intro V _ _ F π k w D hw hk hkD hwD hnr href hasm
  have hunsat : ¬ Satisfiable F := linK_refutation_unsat V F k π href
  have hDn : D < Fintype.card V := by
    by_contra hcon
    exact hnr (DegSizeArith.complete_deg V F w D hw hunsat (by omega) (by omega))
  exact final_plan_num (Fintype.card V) k w D _ hk hkD hwD hDn hasm
end Plan
end C.DegSizeArithK
namespace C.LinKSimA
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan C.LinKPlan
section Abstract
variable {σ : Type} {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
theorem totalDegree_one_add_le_k {p : MvPolynomial σ (ZMod 2)} {k : ℕ}
    (h : p.totalDegree ≤ k) : (1 + p).totalDegree ≤ k := by
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) h
theorem totalDegree_prod_le_k {ι : Type} (s : Finset ι) (a : ι → MvPolynomial σ (ZMod 2))
    {k : ℕ} (ha : ∀ u ∈ s, (a u).totalDegree ≤ k) :
    (∏ u ∈ s, (1 + a u)).totalDegree ≤ s.card * k := by
  have := Helpers.totalDegree_prod_one_add_le s a (e := k) ha
  rw [Nat.mul_comm]
  exact this
theorem prod_absorb_k (hC : DegClosed C D) {ι : Type} (s : Finset ι)
    (a : ι → MvPolynomial σ (ZMod 2)) (Q : MvPolynomial σ (ZMod 2)) {dQ k : ℕ}
    (hdQ : Q.totalDegree ≤ dQ) (ha : ∀ u ∈ s, a u * Q ∈ C)
    (hdeg : ∀ u ∈ s, (a u).totalDegree ≤ k) (hB : s.card * k + dQ ≤ D) :
    (∏ u ∈ s, (1 + a u)) * Q + Q ∈ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, char2_add_self]
    exact C.zero_mem
  | insert u s hu ih =>
    rw [Finset.card_insert_of_notMem hu, Nat.add_mul, Nat.one_mul] at hB
    have hdeg' : ∀ v ∈ s, (a v).totalDegree ≤ k := fun v hv =>
      hdeg v (Finset.mem_insert_of_mem hv)
    have ih' := ih (fun v hv => ha v (Finset.mem_insert_of_mem hv)) hdeg' (by omega)
    have hd : ((∏ v ∈ s, (1 + a v)) * Q + Q).totalDegree ≤ s.card * k + dQ := by
      refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
      exact totalDegree_mul_le' (totalDegree_prod_le_k s a hdeg') hdQ
    have h1 : (1 + a u).totalDegree ≤ k :=
      totalDegree_one_add_le_k (hdeg u (Finset.mem_insert_self u s))
    have h2 := DegSizeSim.absorb_le hC (1 + a u) ih' h1 hd (by omega)
    have h3 := C.add_mem h2 (ha u (Finset.mem_insert_self u s))
    have e : (∏ v ∈ insert u s, (1 + a v)) * Q + Q
        = (1 + a u) * ((∏ v ∈ s, (1 + a v)) * Q + Q) + a u * Q := by
      rw [Finset.prod_insert hu]
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) * char2_add_self (a u * Q)
    rw [e]
    exact h3
theorem totalDegree_span_le_k {G : Set (MvPolynomial σ (ZMod 2))} {k : ℕ}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem totalDegree_appr_le_k {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_le_k Finset.univ qs (fun j _ => h j)
  simpa using this
theorem span_mul_mem {G : Set (MvPolynomial σ (ZMod 2))} {Q : MvPolynomial σ (ZMod 2)}
    (hg : ∀ g ∈ G, g * Q ∈ C) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q * Q ∈ C := by
  induction hq using Submodule.span_induction with
  | mem g hg' => exact hg g hg'
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_mul]
    exact C.add_mem hx hy
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem transfer_k' (hC : DegClosed C D) {K t k r : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (qs : Fin t → MvPolynomial σ (ZMod 2)) {f R : MvPolynomial σ (ZMod 2)}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) G)
    (hf : f.totalDegree ≤ K) (hR : R.totalDegree ≤ r) (hB : K + t * k + r ≤ D)
    (hP : (∏ j, (1 + qs j)) * f ∈ C) (hg : ∀ g ∈ G, g * R * f ∈ C) : R * f ∈ C := by
  have hQ : (R * f).totalDegree ≤ r + K := totalDegree_mul_le' hR hf
  have hspan : ∀ q ∈ Submodule.span (ZMod 2) G, q * (R * f) ∈ C := fun q hq =>
    span_mul_mem (fun g hg' => by
      rw [← mul_assoc]
      exact hg g hg') hq
  have hdq : ∀ j, (qs j).totalDegree ≤ k := fun j => totalDegree_span_le_k hG (hqs j)
  have h1 := prod_absorb_k hC Finset.univ qs (R * f) hQ (fun u _ => hspan _ (hqs u))
    (fun u _ => hdq u) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
  have hPd : ((∏ j, (1 + qs j)) * f).totalDegree ≤ t * k + K :=
    totalDegree_mul_le' (totalDegree_appr_le_k qs hdq) hf
  have h2 := DegSizeSim.absorb_le hC R hP hR hPd (by omega)
  have h3 := C.add_mem h1 h2
  have e : (∏ j, (1 + qs j)) * (R * f) + R * f + R * ((∏ j, (1 + qs j)) * f) = R * f := by
    linear_combination char2_add_self ((∏ j, (1 + qs j)) * (R * f))
  rwa [e] at h3
theorem transfer_k :
    ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t * k + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C :=
  fun _ _ _ _ _ _ _ _ qs _ _ hC hG hqs hf hR hB hP hg =>
    transfer_k' hC qs hG hqs hf hR hB hP hg
end Abstract
section Lines
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D K t k : ℕ}
  {f : MvPolynomial V (ZMod 2)}
theorem totalDegree_lineInputs_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem totalDegree_lineAppr_le {L : LinKLine V} (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  totalDegree_appr_le_k qs fun j =>
    totalDegree_span_le_k (totalDegree_lineInputs_le hL) (hqs j)
theorem lineInputs_linKOfClause_subset [DecidableEq V] (A : Clause V) :
    lineInputs (linKOfClause A) ⊆ (fun q => eqPoly q) '' (↑(linOfClause A) : Set (LinEq V)) := by
  rintro _ ⟨T, hT, rfl⟩
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hT)
  exact ⟨q, Finset.mem_coe.mpr hq, (termPoly_singleton q).symm⟩
theorem step_ax_k' [DecidableEq V] (hC : DegClosed C D) (A : Clause V) {w : ℕ}
    (hA : clausePoly A ∈ C) (hw : A.card ≤ w) (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A)))
    (hf : f.totalDegree ≤ K) (hB : K + t + w ≤ D)
    (hH : ∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qs j)) * f ∈ C := by
  refine DegSizeSim.step_ax hC A hA hw qs
    (fun j => Submodule.span_mono (lineInputs_linKOfClause_subset A) (hqs j)) hf hB ?_
  intro q hq
  have := hH {q} (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  rwa [termPoly_singleton] at this
theorem step_ax_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C := by
  intro V _ C D K t k w f A qs hC hk hA hw hqs hf hB hH
  have htk : t ≤ t * k := Nat.le_mul_of_pos_right t hk
  exact step_ax_k' hC A hA hw qs hqs hf (by omega) hH
theorem step_cut_k' [DecidableEq V] (hC : DegClosed C D) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2))
    (h1 : ∀ T ∈ L₁, T.card ≤ k) (h2 : ∀ T ∈ L₂, T.card ≤ k) (hM : ∀ T ∈ M, T.card ≤ k)
    (hq1 : ∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁))
    (hq2 : ∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂))
    (hqM : ∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M))
    (hf : f.totalDegree ≤ K) (hB : K + 2 * t * k + 2 * k ≤ D) (hcut : IsLinKCut L₁ L₂ M)
    (hP1 : (∏ j, (1 + q₁ j)) * f ∈ C) (hP2 : (∏ j, (1 + q₂ j)) * f ∈ C)
    (hHM : ∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) :
    (∏ j, (1 + qM j)) * f ∈ C := by
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k := totalDegree_lineAppr_le hM qM hqM
  generalize (∏ j, (1 + qM j)) = P at hdM hHM ⊢
  obtain ⟨T, hT1, -, rfl⟩ := hcut
  have hTk : T.card ≤ k := h1 T hT1
  have hτ : (termPoly T).totalDegree ≤ k := (totalDegree_termPoly_le T).trans hTk
  have hQ : (P * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hd1 : (1 + termPoly T).totalDegree ≤ k := totalDegree_one_add_le_k hτ
  have hmul : 2 * t * k = t * k + t * k := by ring
  have hA : (1 + termPoly T) * P * f ∈ C := by
    have hdR : ((1 + termPoly T) * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hd1 hdM
    refine transfer_k' hC q₁ (totalDegree_lineInputs_le h1) hq1 hf hdR (by omega) hP1 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₁ := Finset.mem_coe.mp hS
    by_cases hST : S = T
    · rw [hST]
      have := idem_mul hC (termPoly T) (P * f) hQ hτ (by omega)
      have e1 : termPoly T * ((1 + termPoly T) * P) * f
          = P * f * (termPoly T * termPoly T + termPoly T) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hST, hS'⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h1 S hS'))) hf
      have := DegSizeSim.absorb_le hC (1 + termPoly T) hmem hd1 hd (by omega)
      have e1 : termPoly S * ((1 + termPoly T) * P) * f
          = (1 + termPoly T) * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have hB' : termPoly T * P * f ∈ C := by
    have hdR : (termPoly T * P).totalDegree ≤ k + t * k := totalDegree_mul_le' hτ hdM
    refine transfer_k' hC q₂ (totalDegree_lineInputs_le h2) hq2 hf hdR (by omega) hP2 ?_
    rintro _ ⟨S, hS, rfl⟩
    have hS' : S ∈ L₂ := Finset.mem_coe.mp hS
    by_cases hSi : S ∈ T.image (fun e => ({negLinEq e} : LinTerm V))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hSi
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨e, he⟩
      have := term_neg_mul hC T e he (P * f) hQ (by omega)
      show termPoly {negLinEq e} * (termPoly T * P) * f ∈ C
      rw [termPoly_singleton]
      have e1 : eqPoly (negLinEq e) * (termPoly T * P) * f
          = P * f * (termPoly T * eqPoly (negLinEq e)) := by ring
      rw [e1]
      exact this
    · have hmem := hHM S (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hS', hSi⟩))
      have hd : (P * termPoly S * f).totalDegree ≤ t * k + k + K :=
        totalDegree_mul_le'
          (totalDegree_mul_le' hdM ((totalDegree_termPoly_le S).trans (h2 S hS'))) hf
      have := DegSizeSim.absorb_le hC (termPoly T) hmem hτ hd (by omega)
      have e1 : termPoly S * (termPoly T * P) * f
          = termPoly T * (P * termPoly S * f) := by ring
      rw [e1]
      exact this
  have h3 := C.add_mem hA hB'
  have e1 : (1 + termPoly T) * P * f + termPoly T * P * f = P * f := by
    linear_combination char2_add_self (termPoly T * P * f)
  rwa [e1] at h3
theorem step_cut_k :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
  exact step_cut_k' hC L₁ L₂ M q₁ q₂ qM h1 h2 hM hq1 hq2 hqM hf hB hcut hP1 hP2 hHM
end Lines
end C.LinKSimA
namespace C.LinKSim
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan C.LinKPlan
section Abstract
variable {σ : Type}
theorem and_totalDegree_span_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem and_totalDegree_appr_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := Helpers.totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, mul_comm] at this
  exact this
end Abstract
section Lines
variable {V : Type}
theorem and_totalDegree_lineInputs_le {k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem and_totalDegree_lineAppr_le {t k : ℕ} (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k)
    (qs : Fin t → MvPolynomial V (ZMod 2))
    (hqs : ∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs L)) :
    (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
  and_totalDegree_appr_le qs fun j =>
    and_totalDegree_span_le (and_totalDegree_lineInputs_le L hL) (hqs j)
variable {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem and_half (hC : DegClosed C D) (L M : LinKLine V) (T₀ : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) {K m k : ℕ}
    (hM : ∀ T ∈ M, T.card ≤ k) (hT₀ : T₀.card ≤ k)
    (hP : P.totalDegree ≤ m) (hf : f.totalDegree ≤ K) (hB : K + m + 2 * k ≤ D)
    (htr : ∀ R : MvPolynomial V (ZMod 2), R.totalDegree ≤ m + k →
      (∀ T ∈ L, termPoly T * R * f ∈ C) → R * f ∈ C)
    (hsub : ∀ T ∈ L, T ≠ T₀ → T ∈ M)
    (hHM : ∀ T ∈ M, P * termPoly T * f ∈ C) :
    (1 + termPoly T₀) * P * f ∈ C := by
  have hg0 : (termPoly T₀).totalDegree ≤ k := (totalDegree_termPoly_le T₀).trans hT₀
  have hd1 : (1 + termPoly T₀).totalDegree ≤ k :=
    (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg0)
  refine htr _ ((totalDegree_mul_le' hd1 hP).trans (by omega)) ?_
  intro T hT
  by_cases h0 : T = T₀
  · subst h0
    have h1 := idem_mul hC (termPoly T) (P * f) (totalDegree_mul_le' hP hf) hg0
      (by omega)
    have e : termPoly T * ((1 + termPoly T) * P) * f
        = P * f * (termPoly T * termPoly T + termPoly T) := by ring
    rw [e]
    exact h1
  · have hTM := hsub T hT h0
    have hmem := hHM T hTM
    have hd : (P * termPoly T * f).totalDegree ≤ m + k + K :=
      totalDegree_mul_le'
        (totalDegree_mul_le' hP ((totalDegree_termPoly_le T).trans (hM T hTM))) hf
    have h1 := DegSizeSim.absorb_le hC (1 + termPoly T₀) hmem hd1 hd (by omega)
    have e : termPoly T * ((1 + termPoly T₀) * P) * f
        = (1 + termPoly T₀) * (P * termPoly T * f) := by ring
    rw [e]
    exact h1
end Lines
theorem step_andIntro_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
      (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
      (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
      (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ C D K t k f L₁ L₂ M q₁ q₂ qM hC hL1 hL2 hM hq1 hq2 hqM hf hB hand hP1 hP2 hHM
  obtain ⟨T₁, T₂, hT1, hT2, rfl⟩ := hand
  rw [mul_assoc] at hB
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    and_totalDegree_lineAppr_le _ hM qM hqM
  have hc1 : T₁.card ≤ k := hL1 T₁ hT1
  have hc2 : T₂.card ≤ k := hL2 T₂ hT2
  have hg1 : (termPoly T₁).totalDegree ≤ k := (totalDegree_termPoly_le T₁).trans hc1
  have hg2 : (termPoly T₂).totalDegree ≤ k := (totalDegree_termPoly_le T₂).trans hc2
  have hQ : ((∏ j, (1 + qM j)) * f).totalDegree ≤ t * k + K := totalDegree_mul_le' hdM hf
  have hA : (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₁ _ T₁ _ f hM hc1 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₁) q₁ f R hC
        (and_totalDegree_lineInputs_le L₁ hL1) hq1 hf hR (by omega) hP1 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hA2 : (1 + termPoly T₂) * (∏ j, (1 + qM j)) * f ∈ C := by
    refine and_half hC L₂ _ T₂ _ f hM hc2 hdM hf (by omega) ?_ ?_ hHM
    · intro R hR hg
      refine htransfer V C D K t k (t * k + k) (lineInputs L₂) q₂ f R hC
        (and_totalDegree_lineInputs_le L₂ hL2) hq2 hf hR (by omega) hP2 ?_
      rintro _ ⟨T, hT, rfl⟩
      exact hg T (Finset.mem_coe.mp hT)
    · intro T hT h0
      exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h0, hT⟩))
  have hU : (∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f ∈ C :=
    hHM _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hun := term_union_mul hC T₁ T₂ ((∏ j, (1 + qM j)) * f) hQ (by omega)
  have hd2 : ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f).totalDegree ≤ k + t * k + K := by
    have hd : (1 + termPoly T₂).totalDegree ≤ k :=
      (totalDegree_add _ _).trans (max_le (by rw [totalDegree_one]; exact Nat.zero_le _) hg2)
    exact totalDegree_mul_le' (totalDegree_mul_le' hd hdM) hf
  have hmid := DegSizeSim.absorb_le hC (termPoly T₁) hA2 hg1 hd2 (by omega)
  have hsum := C.add_mem (C.add_mem hA hmid) (C.add_mem hU hun)
  have e : (∏ j, (1 + qM j)) * f
      = (1 + termPoly T₁) * (∏ j, (1 + qM j)) * f
        + termPoly T₁ * ((1 + termPoly T₂) * (∏ j, (1 + qM j)) * f)
        + ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f
          + (∏ j, (1 + qM j)) * f * (termPoly (T₁ ∪ T₂) + termPoly T₁ * termPoly T₂)) := by
    linear_combination
      (-1 : MvPolynomial V (ZMod 2)) * char2_add_self (termPoly T₁ * (∏ j, (1 + qM j)) * f)
      - char2_add_self (termPoly T₁ * termPoly T₂ * (∏ j, (1 + qM j)) * f)
      - char2_add_self ((∏ j, (1 + qM j)) * termPoly (T₁ ∪ T₂) * f)
  rw [e]
  exact hsum
end C.LinKSim
namespace C.LinKSim
open MvPolynomial PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan C.LinKPlan
section Degrees
variable {σ : Type}
theorem weak_span_degree_le {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k := by
  induction hq using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add x y _ _ hx hy => exact (totalDegree_add _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rcases zmod2_cases c with rfl | rfl
    · simp
    · simpa using hx
theorem weak_lineInputs_degree_le {V : Type} {k : ℕ} (L : LinKLine V)
    (hL : ∀ T ∈ L, T.card ≤ k) : ∀ g ∈ lineInputs L, g.totalDegree ≤ k := by
  rintro _ ⟨T, hT, rfl⟩
  exact (totalDegree_termPoly_le T).trans (hL T (Finset.mem_coe.mp hT))
theorem weak_appr_degree_le {t k : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  have := totalDegree_prod_one_add_le Finset.univ qs (e := k) (fun j _ => h j)
  rw [Finset.card_univ, Fintype.card_fin, Nat.mul_comm] at this
  exact this
end Degrees
section Cases
variable {V : Type} {C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))} {D : ℕ}
theorem weak_case_term (hC : DegClosed C D) {K r k : ℕ} (T S : LinTerm V)
    (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k) (hS : S.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + 2 * k ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T → LinTermSat a S)
    (hS' : P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  have h1 := weak_term_mul hC T S himp (P * f) (b := r + K) (totalDegree_mul_le' hP hf)
    (by omega)
  have hdS : (P * termPoly S * f).totalDegree ≤ r + k + K :=
    totalDegree_mul_le' (totalDegree_mul_le' hP ((totalDegree_termPoly_le S).trans hS)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hS'
    ((totalDegree_termPoly_le T).trans hT) hdS (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * termPoly S) + termPoly T * (P * termPoly S * f) := by
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * termPoly S * f))
  rw [e]
  exact C.add_mem h1 h2
theorem weak_case_disj [Fintype V] [DecidableEq V] (hC : DegClosed C D) {K r k : ℕ}
    (T : LinTerm V) (M : LinKLine V) (P f : MvPolynomial V (ZMod 2)) (hT : T.card ≤ k)
    (hP : P.totalDegree ≤ r) (hf : f.totalDegree ≤ K) (hB : K + r + k + 1 ≤ D)
    (himp : ∀ a : V → Bool, LinTermSat a T →
      ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)
    (hM : ∀ S ∈ M, P * termPoly S * f ∈ C) : termPoly T * P * f ∈ C := by
  obtain ⟨J, hJ, hmul⟩ := weak_disj_line (C := C) (D := D) hC T M himp
  have h1 := hmul (P * f) (r + K) (totalDegree_mul_le' hP hf) (by omega)
  have hsum : ∑ d ∈ J, P * eqPoly d * f ∈ C := by
    refine Submodule.sum_mem _ fun d hd => ?_
    have := hM {d} (hJ d hd)
    rwa [termPoly_singleton] at this
  have hds : (∑ d ∈ J, P * eqPoly d * f).totalDegree ≤ r + 1 + K :=
    totalDegree_finsetSum_le fun d _ =>
      totalDegree_mul_le' (totalDegree_mul_le' hP (totalDegree_eqPoly_le d)) hf
  have h2 := DegSizeSim.absorb_le hC (termPoly T) hsum
    ((totalDegree_termPoly_le T).trans hT) hds (by omega)
  have e : termPoly T * P * f
      = P * f * (termPoly T + termPoly T * ∑ d ∈ J, eqPoly d)
        + termPoly T * ∑ d ∈ J, P * eqPoly d * f := by
    have e1 : ∑ d ∈ J, P * eqPoly d * f = P * (∑ d ∈ J, eqPoly d) * f := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [e1]
    linear_combination (-1 : MvPolynomial V (ZMod 2))
      * char2_add_self (termPoly T * (P * (∑ d ∈ J, eqPoly d) * f))
  rw [e]
  exact C.add_mem h1 h2
end Cases
theorem step_weak_of
    (htransfer :
      ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t k r : ℕ)
        (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
        (f R : MvPolynomial σ (ZMod 2)),
        DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) →
        (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
        K + t * k + r ≤ D →
        (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
      (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
      (qL qM : Fin t → MvPolynomial V (ZMod 2)),
      DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
      (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
      f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
      (∏ j, (1 + qL j)) * f ∈ C →
      (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
      (∏ j, (1 + qM j)) * f ∈ C := by
  intro V _ _ C D K t k f L M qL qM hC hk hL hM hqL hqM hf hB hweak hPL hHM
  have h2 : 2 * t * k = t * k + t * k := by ring
  have hdM : (∏ j, (1 + qM j)).totalDegree ≤ t * k :=
    weak_appr_degree_le qM fun j =>
      weak_span_degree_le (weak_lineInputs_degree_le M hM) (hqM j)
  refine htransfer V C D K t k (t * k) (lineInputs L) qL f _ hC
    (weak_lineInputs_degree_le L hL) hqL hf hdM (by omega) hPL ?_
  rintro _ ⟨T, hT, rfl⟩
  have hT' : T ∈ L := Finset.mem_coe.mp hT
  rcases hweak T hT' with ⟨S, hS, himp⟩ | himp
  · exact weak_case_term hC T S _ f (hL T hT') (hM S hS) hdM hf (by omega) himp (hHM S hS)
  · exact weak_case_disj hC T M _ f (hL T hT') hdM hf (by omega) himp hHM
end C.LinKSim
namespace C.LinKSim
open MvPolynomial Module PEqualNP.ProofComplexity C.Helpers
  C.DegSizePlan C.LinKPlan
def AxRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k w : ℕ) (f : MvPolynomial V (ZMod 2)) (A : Clause V)
    (qs : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → clausePoly A ∈ C → A.card ≤ w →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) (lineInputs (linKOfClause A))) →
    f.totalDegree ≤ K → K + t * k + w ≤ D →
    (∀ T ∈ linKOfClause A, (∏ j, (1 + qs j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qs j)) * f ∈ C
def CutRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKCut L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def AndRule : Prop :=
  ∀ (V : Type) [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L₁ L₂ M : LinKLine V)
    (q₁ q₂ qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → (∀ T ∈ L₁, T.card ≤ k) → (∀ T ∈ L₂, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, q₁ j ∈ Submodule.span (ZMod 2) (lineInputs L₁)) →
    (∀ j, q₂ j ∈ Submodule.span (ZMod 2) (lineInputs L₂)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKAndIntro L₁ L₂ M →
    (∏ j, (1 + q₁ j)) * f ∈ C → (∏ j, (1 + q₂ j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def WeakRule : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (C : Submodule (ZMod 2) (MvPolynomial V (ZMod 2)))
    (D K t k : ℕ) (f : MvPolynomial V (ZMod 2)) (L M : LinKLine V)
    (qL qM : Fin t → MvPolynomial V (ZMod 2)),
    DegClosed C D → 1 ≤ k → (∀ T ∈ L, T.card ≤ k) → (∀ T ∈ M, T.card ≤ k) →
    (∀ j, qL j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ j, qM j ∈ Submodule.span (ZMod 2) (lineInputs M)) →
    f.totalDegree ≤ K → K + 2 * t * k + 2 * k ≤ D → IsLinKWeakening L M →
    (∏ j, (1 + qL j)) * f ∈ C →
    (∀ T ∈ M, (∏ j, (1 + qM j)) * termPoly T * f ∈ C) →
    (∏ j, (1 + qM j)) * f ∈ C
def SimDrv : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) →
    IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)
def SimRef : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinKLine V → Fin t → MvPolynomial V (ZMod 2)),
    1 ≤ k → (∀ A ∈ F, A.card ≤ w) → IsLinKRefutation k F π →
    K + max (2 * t * k + 2 * k) (t * k + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
    (∀ L ∈ π, ∀ T ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * termPoly T * f)) →
    PCDerivable (cnfSystem F) D f
theorem drv_card_le {V : Type} [DecidableEq V] {k : ℕ} {W : LinKLine V → LinKLine V → Prop}
    {F : Set (LinKLine V)} {π : List (LinKLine V)} (h : IsLinKDerivation k W F π) :
    ∀ L ∈ π, ∀ T ∈ L, T.card ≤ k := by
  induction h with
  | nil =>
    intro L hL
    simp at hL
  | ax _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | cut _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | andIntro _ _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
  | weak _ _ _ hk ih =>
    intro L hL
    rcases List.mem_cons.mp hL with hL' | hL'
    · subst hL'
      exact hk
    · exact ih L hL'
theorem simulation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule) (hweak : WeakRule) :
    SimDrv := by
  intro V _ _ F π k w D K t f qs hk hw hder hB hf
  have hB1 : K + 2 * t * k + 2 * k ≤ D := by
    have := (Nat.add_le_add_left (le_max_left (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hB2 : K + t * k + w ≤ D := by
    have := (Nat.add_le_add_left (le_max_right (2 * t * k + 2 * k) (t * k + w)) K).trans hB
    rwa [← Nat.add_assoc] at this
  have hD2 : 2 ≤ D := by
    have h2 : 2 ≤ 2 * k := by omega
    exact h2.trans ((Nat.le_add_left _ _).trans hB1)
  have hwD : w ≤ D := (Nat.le_add_left _ _).trans hB2
  have hC : DegClosed (pcClosure (cnfSystem F) D) D :=
    degClosed_pcClosure _ _ hD2 fun v => Or.inl ⟨v, rfl⟩
  have key : ∀ ρ : List (LinKLine V),
      IsLinKDerivation k IsLinKWeakening ((fun A => linKOfClause A) '' F) ρ →
      (∀ L ∈ ρ, ∀ j, qs L j ∈ Submodule.span (ZMod 2) (lineInputs L)) →
      (∀ L ∈ ρ, ∀ T ∈ L, (∏ j, (1 + qs L j)) * termPoly T * f ∈ pcClosure (cnfSystem F) D) →
      ∀ L ∈ ρ, (∏ j, (1 + qs L j)) * f ∈ pcClosure (cnfSystem F) D := by
    intro ρ hρ
    induction hρ with
    | nil =>
      intro _ _ L hL
      simp at hL
    | @ax ρ L0 _ hL0 _ ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        obtain ⟨A, hAF, hA⟩ := hL0
        subst hA
        have hAw := hw A hAF
        have hmem : clausePoly A ∈ pcClosure (cnfSystem F) D :=
          PCDerivable.ax (Or.inr ⟨A, hAF, rfl⟩)
            ((DegSizeSim.totalDegree_clausePoly_le A).trans (hAw.trans hwD))
        exact hax V (pcClosure (cnfSystem F) D) D K t k w f A (qs (linKOfClause A))
          hC hk hmem hAw (hs _ List.mem_cons_self) hf hB2 (hH _ List.mem_cons_self)
      · exact ih' L hL'
    | @cut ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hcut V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @andIntro ρ L1 L2 M hρ' h1 h2 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hand V (pcClosure (cnfSystem F) D) D K t k f L1 L2 L (qs L1) (qs L2) (qs L)
          hC (drv_card_le hρ' L1 h1) (drv_card_le hρ' L2 h2) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L2 (List.mem_cons_of_mem _ h2))
          (hs L List.mem_cons_self) hf hB1 hrule (ih' L1 h1) (ih' L2 h2)
          (hH L List.mem_cons_self)
      · exact ih' L hL'
    | @weak ρ L1 M hρ' h1 hrule hkM ih =>
      intro hs hH L hL
      have ih' := ih (fun L hL => hs L (List.mem_cons_of_mem _ hL))
        (fun L hL => hH L (List.mem_cons_of_mem _ hL))
      rcases List.mem_cons.mp hL with hL' | hL'
      · subst hL'
        exact hweak V (pcClosure (cnfSystem F) D) D K t k f L1 L (qs L1) (qs L)
          hC hk (drv_card_le hρ' L1 h1) hkM
          (hs L1 (List.mem_cons_of_mem _ h1)) (hs L List.mem_cons_self) hf hB1 hrule
          (ih' L1 h1) (hH L List.mem_cons_self)
      · exact ih' L hL'
  intro hs hH
  exact key π hder hs hH
theorem simulation_refutation_of (hax : AxRule) (hcut : CutRule) (hand : AndRule)
    (hweak : WeakRule) : SimRef := by
  intro V _ _ F π k w D K t f qs hk hw href hB hf hs hH
  obtain ⟨hder, hemp⟩ := href
  have h := simulation_of hax hcut hand hweak V F π k w D K t f qs hk hw hder hB hf hs hH
    ∅ hemp
  have hq : ∀ j, qs ∅ j = 0 := by
    intro j
    have := hs ∅ hemp j
    simpa [lineInputs] using this
  simpa [hq] using h
end C.LinKSim
namespace C.LinKSim
open C.LinKPlan C.LinKSimA
theorem step_andIntro : AndRule := step_andIntro_of transfer_k
theorem step_weak : WeakRule := step_weak_of transfer_k
theorem simulation : SimDrv := simulation_of step_ax_k step_cut_k step_andIntro step_weak
theorem simulation_refutation : C.LinKAsm.StmtSimRefutation :=
  simulation_refutation_of step_ax_k step_cut_k step_andIntro step_weak
end C.LinKSim
namespace C.LinKFinal
open PEqualNP.ProofComplexity PEqualNP.Expanders
def StmtLinK : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinKLine V))
    (k w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → 1 ≤ k → 16 * k ≤ D → 4 * w ≤ D →
    ¬ PCRefutable (cnfSystem F) D → IsLinKRefutation k F π →
    Real.exp ((D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (Fintype.card V : ℝ))) ^ k)
      ≤ (π.length : ℝ)
theorem funGraphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ funGraphPHP G, C.card ≤ max b 2 := by
  intro C hC
  rcases hC with hC | ⟨e, e', -, -, rfl⟩
  · exact PhpFinal.graphPHP_width G b hb C hC
  · exact le_trans Finset.card_le_two (le_max_right _ _)
theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (hxy : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)
theorem degree_facts (n s₀ w : ℕ) (hs : 0 < s₀) (hw : 0 < w) (hn : 4 * (s₀ * w) ≤ n) :
    w * (n / s₀ / w) ≤ n / s₀ ∧ n ≤ 2 * (s₀ * w * (n / s₀ / w)) := by
  refine ⟨Nat.mul_div_le _ _, ?_⟩
  have h1 : n < s₀ * (n / s₀ + 1) := Nat.lt_mul_div_succ n hs
  have h2 : n / s₀ < w * (n / s₀ / w + 1) := Nat.lt_mul_div_succ _ hw
  have h3 : s₀ * (n / s₀ + 1) ≤ s₀ * (w * (n / s₀ / w + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : s₀ * (w * (n / s₀ / w + 1)) = s₀ * w * (n / s₀ / w) + s₀ * w := by ring
  omega
theorem exp_arith (k s₀ w n D card : ℕ) (hk : 1 ≤ k) (hs : 0 < s₀) (hw : 0 < w) (hn : 0 < n)
    (hcard_pos : 0 < card) (hcard : card ≤ 2 * n * w) (hnD : n ≤ 2 * (s₀ * w * D)) :
    (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n ≤
      (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcR : (0 : ℝ) < card := by exact_mod_cast hcard_pos
  have hDR : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hnD' : (n : ℝ) ≤ 2 * ((s₀ : ℝ) * w * D) := by exact_mod_cast hnD
  have hcard' : (card : ℝ) ≤ 2 * n * w := by exact_mod_cast hcard
  set ρ : ℝ := 1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have h1 : (n : ℝ) / (32 * (k : ℝ) * s₀ * w) ≤ (D : ℝ) / (16 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnD' (by positivity : (0 : ℝ) ≤ 16 * (k : ℝ))]
  have h2 : ρ ≤ (D : ℝ) / (4 * (card : ℝ)) := by
    rw [hρ, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have h8 : 4 * (card : ℝ) ≤ 8 * n * w := by linarith
    have h9 : 8 * (n : ℝ) * w ≤ 16 * ((s₀ : ℝ) * w * D) * w := by
      have := mul_le_mul_of_nonneg_right hnD' (by positivity : (0 : ℝ) ≤ 8 * w)
      linarith
    nlinarith
  have h3 : ρ ^ k ≤ ((D : ℝ) / (4 * (card : ℝ))) ^ k := pow_le_pow_left₀ hρ0 h2 k
  calc ρ ^ k / (32 * (k : ℝ) * s₀ * w) * n = (n : ℝ) / (32 * (k : ℝ) * s₀ * w) * ρ ^ k := by
        ring
    _ ≤ (D : ℝ) / (16 * (k : ℝ)) * ((D : ℝ) / (4 * (card : ℝ))) ^ k :=
        mul_le_mul h1 h3 (pow_nonneg hρ0 k) (by positivity)
end C.LinKFinal
namespace C.LinKWire
theorem general (hSim : LinKAsm.StmtSimRefutation) : LinKFinal.StmtLinK :=
  LinKAsm.degree_to_size_k hSim DegSizeArithK.final_of_assembly_plan
end C.LinKWire
namespace C.LinKGrow
open PEqualNP.ProofComplexity PEqualNP.Expanders C.LinKFinal
theorem graph_bound (hL : StmtLinK) (b s₀ n k w : ℕ) (hw : w = max b 2) (hs₀ : 0 < s₀)
    (hk : 1 ≤ k) (G : BipGraph (n + 1) n) (hLd : LeftDegLe G b)
    (hE : IsBdryExpander G (n / s₀) 2)
    (hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n) (hn2 : 4 * (s₀ * w) + s₀ ≤ n)
    (π : List (LinKLine (GEdge G))) (hπ : IsLinKRefutation k (funGraphPHP G) π) :
    Real.exp ((1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n)
      ≤ (π.length : ℝ) := by
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hsw : 0 < s₀ * w := Nat.mul_pos hs₀ (by omega)
  have hnpos : 0 < n := by omega
  obtain ⟨hwD, hnD⟩ := degree_facts n s₀ w hs₀ (by omega) (by omega)
  set D := n / s₀ / w with hD
  have hDk : 16 * k + 4 * w ≤ D := by
    have h : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ 2 * (s₀ * w) * D := by
      calc 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n := hn1
        _ ≤ 2 * (s₀ * w * D) := hnD
        _ = 2 * (s₀ * w) * D := by ring
    exact Nat.le_of_mul_le_mul_left h (by omega)
  have hs1 : 1 ≤ n / s₀ := (Nat.le_div_iff_mul_le hs₀).mpr (by omega)
  have hLw : LeftDegLe G w := fun i => le_trans (hLd i) hbw
  have hnr := C.L049 (n + 1) n G (n / s₀) w D hE hLw hs1 hwD
  have hcard_pos : 0 < Fintype.card (GEdge G) := by
    have h := hE {0} (by rw [Finset.card_singleton]; exact hs1)
    rw [Finset.card_singleton] at h
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by norm_num) h)
    unfold uniqueNbrs at hj
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hj).2
    have hi' : i ∈ Finset.filter (fun i => j ∈ G i) {0} := by
      rw [hi]; exact Finset.mem_singleton_self i
    exact Fintype.card_pos_iff.mpr ⟨⟨(i, j), (Finset.mem_filter.mp hi').2⟩⟩
  have hcard : Fintype.card (GEdge G) ≤ 2 * n * w := by
    have := le_trans (PhpFinal.card_gedge_le G b hLd) (Nat.mul_le_mul_left (n + 1) hbw)
    have h2 : (n + 1) * w ≤ 2 * n * w := Nat.mul_le_mul_right _ (by omega)
    omega
  have hsize := hL (GEdge G) (funGraphPHP G) π k w D
    (fun C hC => hw ▸ funGraphPHP_width G b hLd C hC) hk (by omega) (by omega) hnr hπ
  have harith := exp_arith k s₀ w n D (Fintype.card (GEdge G)) hk hs₀ (by omega) hnpos
    hcard_pos hcard hnD
  exact le_trans (Real.exp_le_exp.mpr harith) hsize
end C.LinKGrow
end PEqualNP.Outside.L_pcx_377_aux
namespace PEqualNP.Outside.L_pcx_377_aux
open PEqualNP.ProofComplexity PEqualNP.Expanders
private lemma funGraphPHP_nonempty {n : ℕ} (G : BipGraph (n + 1) n) :
    (funGraphPHP G).Nonempty := by
  refine ⟨Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = (0 : Fin (n + 1)) ∧ l.2 = true), ?_⟩
  exact Or.inl (Or.inl ⟨0, rfl⟩)
private lemma add_one_le_two_pow {k : ℕ} (hk : 1 ≤ k) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => norm_num
    | succ k' =>
      have h := ih (by omega)
      rw [pow_succ']
      omega
private lemma lower_bound_on_expander (b s₀ n : ℕ) (hs₀ : 0 < s₀) (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hE : IsBdryExpander G (n / s₀) 2)
    (w : ℕ) (hw : w = max b 2)
    (hn2 : 4 * (s₀ * w) + s₀ ≤ n)
    (C : ℕ) (hC : 768 * (16 * s₀ * w ^ 2) * s₀ * w ≤ C)
    (a h t r p q : ℕ) (f : (GEdge G → Bool) → Fin a → Bool)
    (menu : Fin t → Fin h → Bool)
    (ht : 0 < t)
    (hcert : ∀ (x : GEdge G → Bool) (i : Fin a), ∃ T : LinTerm (GEdge G),
      T.card ≤ (if f x i then q else p) ∧ LinTermSat x T ∧
      ∀ y : GEdge G → Bool, LinTermSat y T → f y i = f x i)
    (extra : Set (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))
    (hwidth : ∀ D ∈ extra, (D.filter (fun l => l.1.isLeft)).card ≤ r)
    (hmenu : ∀ x : GEdge G → Bool, ∃ j : Fin t, Satisfies
      (Sum.elim (Sum.elim x (f x)) (menu j)) extra)
    (π : List (Clause ((GEdge G ⊕ Fin a) ⊕ Fin h)))
    (hπ : IsRefutation
      (Set.image (fun cl : Clause (GEdge G) =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (GEdge G ⊕ Fin a) ⊕ Fin h), l.2)))
        (funGraphPHP G) ∪ extra) π) :
    n ≤ C ^ (max 1 (p * q)) * t * (r + Nat.clog 2 (π.length + 1) + 1) := by
  set k := max 1 (p * q)
  have hk : 1 ≤ k := le_max_left _ _
  set B := 16 * s₀ * w ^ 2 with hB
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hB1 : 64 ≤ B := by
    rw [hB]
    have : 4 ≤ w ^ 2 := by nlinarith
    nlinarith
  have hsw1 : 2 ≤ s₀ * w := by nlinarith
  by_cases hn1 : 2 * (s₀ * w) * (16 * k + 4 * w) ≤ n
  · obtain ⟨τ, hτ, hτlen⟩ :=
      PEqualNP.Outside.L_pcx_377_aux.L376_main (GEdge G) (funGraphPHP G) (funGraphPHP_nonempty G)
        a h t r p q f menu ht hcert extra hwidth hmenu π hπ
    have hL : PEqualNP.Outside.L_pcx_377_aux.C.LinKFinal.StmtLinK :=
      PEqualNP.Outside.L_pcx_377_aux.C.LinKWire.general PEqualNP.Outside.L_pcx_377_aux.C.LinKSim.simulation_refutation
    have hgb := PEqualNP.Outside.L_pcx_377_aux.C.LinKGrow.graph_bound hL b s₀ n k w hw hs₀ hk G hLd hE
      hn1 hn2 τ hτ
    set m := Nat.clog 2 (π.length + 1)
    have hclog : π.length + 1 ≤ 2 ^ m := Nat.le_pow_clog (by omega) (π.length + 1)
    have hbase : 16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1)) ≤
        2 ^ (6 * k * (r + m + 1)) := by
      have h16 : 16 = 2 ^ 4 := by norm_num
      have hk1 : k + 1 ≤ 2 ^ k := add_one_le_two_pow hk
      have hmul1 : 16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1)) ≤
          2 ^ 4 * 2 ^ k * 2 ^ m * 2 ^ (k * (r + 1)) := by
        rw [h16]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hk1) hclog)
      have hexp : 4 + k + m + k * (r + 1) ≤ 6 * k * (r + m + 1) := by
        have hkr : k * r ≤ 6 * k * r := by nlinarith
        have hkm : m ≤ 6 * k * m := by nlinarith
        nlinarith
      calc 16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1))
          ≤ 2 ^ 4 * 2 ^ k * 2 ^ m * 2 ^ (k * (r + 1)) := hmul1
        _ = 2 ^ (4 + k + m + k * (r + 1)) := by
            simp only [← pow_add]
        _ ≤ 2 ^ (6 * k * (r + m + 1)) := Nat.pow_le_pow_right (by omega) hexp
    have hlen_nat : τ.length ≤ 2 ^ (6 * k * t * (r + m + 1)) := by
      calc τ.length
          ≤ (16 * (k + 1) * (π.length + 1) * 2 ^ (k * (r + 1))) ^ t := hτlen
        _ ≤ (2 ^ (6 * k * (r + m + 1))) ^ t := Nat.pow_le_pow_left hbase t
        _ = 2 ^ (6 * k * (r + m + 1) * t) := (pow_mul _ _ _).symm
        _ = 2 ^ (6 * k * t * (r + m + 1)) := by congr 1; ring
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hexp_ub : (τ.length : ℝ) ≤ Real.exp ((6 * k * t * (r + m + 1) : ℕ) : ℝ) := by
      calc (τ.length : ℝ)
          ≤ ((2 ^ (6 * k * t * (r + m + 1)) : ℕ) : ℝ) := by exact_mod_cast hlen_nat
        _ = (2 : ℝ) ^ (6 * k * t * (r + m + 1)) := by push_cast; rfl
        _ ≤ (Real.exp 1) ^ (6 * k * t * (r + m + 1)) := pow_le_pow_left₀ (by norm_num) h2e _
        _ = Real.exp (((6 * k * t * (r + m + 1) : ℕ) : ℝ) * 1) := by rw [← Real.exp_nat_mul]
        _ = Real.exp ((6 * k * t * (r + m + 1) : ℕ) : ℝ) := by ring_nf
    have hle_exp := le_trans hgb hexp_ub
    have hle_arg : (1 / (16 * (s₀ : ℝ) * (w : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * s₀ * w) * n ≤
        ((6 * k * t * (r + m + 1) : ℕ) : ℝ) := Real.exp_le_exp.mp hle_exp
    have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
    have hDpos : (0 : ℝ) < (32 * (k : ℝ) * s₀ * w) := by
      have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hsR : (0 : ℝ) < s₀ := by exact_mod_cast hs₀
      have hwR : (0 : ℝ) < w := by exact_mod_cast (by omega : 0 < w)
      positivity
    have hBcast : (16 * (s₀ : ℝ) * (w : ℝ) ^ 2) = (B : ℝ) := by rw [hB]; push_cast; rfl
    rw [hBcast, one_div, inv_pow] at hle_arg
    have hmul : (n : ℝ) ≤ (B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w) *
        ((6 * k * t * (r + m + 1) : ℕ) : ℝ) := by
      have hden : (0 : ℝ) < (B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w) := by positivity
      have hrew : ((B : ℝ) ^ k)⁻¹ / (32 * (k : ℝ) * s₀ * w) * (n : ℝ) =
          (n : ℝ) / ((B : ℝ) ^ k * (32 * (k : ℝ) * s₀ * w)) := by
        field_simp
      rw [hrew, div_le_iff₀ hden] at hle_arg
      linarith
    have hnat : n ≤ B ^ k * (32 * k * s₀ * w) * (6 * k * t * (r + m + 1)) := by
      have : ((n : ℕ) : ℝ) ≤ ((B ^ k * (32 * k * s₀ * w) * (6 * k * t * (r + m + 1)) : ℕ) : ℝ) := by
        push_cast at hmul ⊢
        exact hmul
      exact_mod_cast this
    have hpow_le : B ^ k * (192 * s₀ * w) * k ^ 2 ≤ C ^ k := by
      have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
      have hk2sq : k ^ 2 ≤ 4 ^ k := by
        calc k ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hk2 2
          _ = (2 ^ 2) ^ k := by rw [← pow_mul, mul_comm, pow_mul]
          _ = 4 ^ k := by norm_num
      have h192 : 192 * s₀ * w ≤ (192 * s₀ * w) ^ k := Nat.le_self_pow (by omega) _
      calc B ^ k * (192 * s₀ * w) * k ^ 2
          ≤ B ^ k * (192 * s₀ * w) ^ k * 4 ^ k :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h192) hk2sq
        _ = (768 * B * s₀ * w) ^ k := by
            rw [← mul_pow, ← mul_pow]; congr 1; ring
        _ ≤ C ^ k := Nat.pow_le_pow_left hC k
    calc n ≤ B ^ k * (32 * k * s₀ * w) * (6 * k * t * (r + m + 1)) := hnat
      _ = (B ^ k * (192 * s₀ * w) * k ^ 2) * t * (r + m + 1) := by ring
      _ ≤ C ^ k * t * (r + m + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow_le)
  · have hlt : n < 2 * (s₀ * w) * (16 * k + 4 * w) := by omega
    have h1 : 16 * k + 4 * w ≤ (16 + 4 * w) * k := by nlinarith
    have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
    have hCk : 2 * (s₀ * w) * (16 + 4 * w) * k ≤ C ^ k := by
      have hC_half : 2 * (s₀ * w) * (16 + 4 * w) ≤ (C / 2) ^ k := by
        have hle : 2 * (s₀ * w) * (16 + 4 * w) ≤ C / 2 := by
          have : 2 * (2 * (s₀ * w) * (16 + 4 * w)) ≤ 768 * B * s₀ * w := by
            have : 4 * (16 + 4 * w) ≤ 768 * B := by
              rw [hB]
              have : w ≤ w ^ 2 := by nlinarith
              nlinarith
            nlinarith
          omega
        exact le_trans hle (Nat.le_self_pow (by omega) _)
      calc 2 * (s₀ * w) * (16 + 4 * w) * k
          ≤ (C / 2) ^ k * 2 ^ k := Nat.mul_le_mul hC_half hk2
        _ = (C / 2 * 2) ^ k := (mul_pow _ _ _).symm
        _ ≤ C ^ k := Nat.pow_le_pow_left (by omega) k
    have hn_le : n ≤ C ^ k := by
      calc n ≤ 2 * (s₀ * w) * (16 * k + 4 * w) := le_of_lt hlt
        _ ≤ 2 * (s₀ * w) * ((16 + 4 * w) * k) := Nat.mul_le_mul_left _ h1
        _ = 2 * (s₀ * w) * (16 + 4 * w) * k := by ring
        _ ≤ C ^ k := hCk
    have hpos : 1 ≤ t * (r + Nat.clog 2 (π.length + 1) + 1) :=
      Nat.mul_pos ht (Nat.succ_pos _)
    calc n ≤ C ^ k := hn_le
      _ ≤ C ^ k * (t * (r + Nat.clog 2 (π.length + 1) + 1)) := Nat.le_mul_of_pos_right _ hpos
      _ = C ^ k * t * (r + Nat.clog 2 (π.length + 1) + 1) := by ring
section ChainRefutation
variable {V : Type} [DecidableEq V]
private def liftCl (m : ℕ) (cl : Clause V) : Clause (V ⊕ Fin m) :=
  cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin m), l.2))
private def chainCl (m : ℕ) (k : Fin m) (l : Literal V) : Clause (V ⊕ Fin m) :=
  if hk : k.val + 1 < m then
    {(Sum.inr k, false), (Sum.inr ⟨k.val + 1, hk⟩, true), (Sum.inl l.1, !l.2)}
  else
    {(Sum.inr k, false), (Sum.inl l.1, !l.2)}
private lemma chainCl_card_le (m : ℕ) (k : Fin m) (l : Literal V) :
    (chainCl m k l).card ≤ 3 := by
  unfold chainCl
  split_ifs
  · exact le_trans (Finset.card_insert_le _ _)
      (Nat.add_le_add_right (le_trans (Finset.card_insert_le _ _) (by simp)) 1)
  · exact le_trans (Finset.card_insert_le _ _) (by simp)
private lemma chainCl_left_card_le (m : ℕ) (k : Fin m) (l : Literal V) :
    ((chainCl m k l).filter (fun p => p.1.isLeft)).card ≤ 1 := by
  unfold chainCl
  split_ifs
  · have hsub :
        ({(Sum.inr k, false), (Sum.inr ⟨k.val + 1, ‹_›⟩, true),
            (Sum.inl l.1, !l.2)} : Clause (V ⊕ Fin m)).filter (fun p => p.1.isLeft) ⊆
          {(Sum.inl l.1, !l.2)} := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
      rcases hp with ⟨rfl | rfl | rfl, hL⟩
      · simp at hL
      · simp at hL
      · rfl
    exact le_trans (Finset.card_le_card hsub) (by simp)
  · have hsub :
        ({(Sum.inr k, false), (Sum.inl l.1, !l.2)} : Clause (V ⊕ Fin m)).filter
            (fun p => p.1.isLeft) ⊆ {(Sum.inl l.1, !l.2)} := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hp ⊢
      rcases hp with ⟨rfl | rfl, hL⟩
      · simp at hL
      · rfl
    exact le_trans (Finset.card_le_card hsub) (by simp)
private lemma resolve_set_away {m : ℕ} {F : Set (Clause (V ⊕ Fin m))}
    (k : Fin m) (W : ℕ) (hW : 2 ≤ W)
    (π₀ : List (Clause (V ⊕ Fin m))) (hD₀ : IsDerivation F π₀) (hW₀ : ∀ D ∈ π₀, D.card ≤ W) :
    ∀ (S : Finset (Literal V)) (A : Clause (V ⊕ Fin m)),
      S.Nonempty →
      (∀ v : V, ¬((v, true) ∈ S ∧ (v, false) ∈ S)) →
      (A = liftCl m S ∨ A = insert (Sum.inr k, false) (liftCl m S)) →
      A ∈ π₀ →
      S.card + 1 ≤ W →
      (∀ l ∈ S, ({(Sum.inr k, false), (Sum.inl l.1, !l.2)} : Clause (V ⊕ Fin m)) ∈ π₀) →
      ∃ π : List (Clause (V ⊕ Fin m)),
        IsDerivation F π ∧
        (∀ D ∈ π₀, D ∈ π) ∧
        ({(Sum.inr k, false)} : Clause (V ⊕ Fin m)) ∈ π ∧
        π.length ≤ π₀.length + S.card ∧
        (∀ D ∈ π, D.card ≤ W) := by
  intro S
  induction S using Finset.induction_on generalizing π₀ with
  | empty =>
    intro _ hne
    exact absurd hne (by simp)
  | @insert l S' hl ih =>
    intro A _ hnoTaut hA hA_mem hScard hpairs
    have hl_pair : ({(Sum.inr k, false), (Sum.inl l.1, !l.2)} : Clause (V ⊕ Fin m)) ∈ π₀ :=
      hpairs l (Finset.mem_insert_self l S')
    have hnot_opp : (Sum.inl l.1, !l.2) ∉ liftCl m S' := by
      intro hm
      rw [liftCl, Finset.mem_image] at hm
      obtain ⟨l', hl'S', heq⟩ := hm
      have hv : l'.1 = l.1 := Sum.inl.inj (Prod.mk.inj heq).1
      have hs : l'.2 = !l.2 := (Prod.mk.inj heq).2
      have h1 : (l.1, l.2) ∈ insert l S' := Finset.mem_insert_self l S'
      have h2 : (l.1, !l.2) ∈ insert l S' := by
        have : l' = (l.1, !l.2) := Prod.ext hv hs
        exact Finset.mem_insert_of_mem (this ▸ hl'S')
      cases hb : l.2
      · rw [hb] at h1 h2; exact hnoTaut l.1 ⟨h2, h1⟩
      · rw [hb] at h1 h2; exact hnoTaut l.1 ⟨h1, h2⟩
    have hl_not_lift : (Sum.inl l.1, l.2) ∉ liftCl m S' := by
      intro hm
      rw [liftCl, Finset.mem_image] at hm
      obtain ⟨l', hl'S', heq⟩ := hm
      have : l' = l := Prod.ext (Sum.inl.inj (Prod.mk.inj heq).1) (Prod.mk.inj heq).2
      exact hl (this ▸ hl'S')
    have hlift_ins : liftCl m (insert l S') = insert (Sum.inl l.1, l.2) (liftCl m S') := by
      simp [liftCl]
    let A' : Clause (V ⊕ Fin m) := insert (Sum.inr k, false) (liftCl m S')
    have hA_erase : A.erase (Sum.inl l.1, l.2) ∪ {(Sum.inr k, false)} = A' := by
      rcases hA with rfl | rfl
      · rw [hlift_ins, Finset.erase_insert hl_not_lift]
        ext p; simp [A']
      · rw [hlift_ins]
        have hne_rk : (Sum.inr k, false) ≠ (Sum.inl l.1, l.2) := by simp
        rw [Finset.erase_insert_of_ne hne_rk, Finset.erase_insert hl_not_lift]
        ext p; simp [A']
    have hl_in_A : (Sum.inl l.1, l.2) ∈ A := by
      rcases hA with rfl | rfl
      · rw [hlift_ins]; exact Finset.mem_insert_self _ _
      · rw [hlift_ins]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hres_step : IsDerivation F (A' :: π₀) := by
      let P : Clause (V ⊕ Fin m) := {(Sum.inr k, false), (Sum.inl l.1, !l.2)}
      have hP_erase : P.erase (Sum.inl l.1, !l.2) = {(Sum.inr k, false)} := by
        ext p
        simp only [P, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1, rfl | rfl⟩
          · rfl
          · exact absurd rfl h1
        · rintro rfl
          exact ⟨by simp, Or.inl rfl⟩
      cases hs : l.2
      ·
        have hres : IsResolvent P A A' := by
          refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
          · simp [P, hs]
          · simpa [hs] using hl_in_A
          · rw [← hA_erase, Finset.union_comm]
            have h1 : P.erase (Sum.inl l.1, true) = {(Sum.inr k, false)} := by
              simpa [hs] using hP_erase
            rw [h1, hs]
        exact IsDerivation.res hD₀ hl_pair hA_mem hres
      ·
        have hres : IsResolvent A P A' := by
          refine ⟨Sum.inl l.1, ?_, ?_, ?_⟩
          · simpa [hs] using hl_in_A
          · simp [P, hs]
          · rw [← hA_erase]
            have h1 : P.erase (Sum.inl l.1, false) = {(Sum.inr k, false)} := by
              simpa [hs] using hP_erase
            rw [h1, hs]
        exact IsDerivation.res hD₀ hA_mem hl_pair hres
    have hA'_card : A'.card ≤ W := by
      have h1 : A'.card ≤ (liftCl m S').card + 1 := Finset.card_insert_le _ _
      have h2 : (liftCl m S').card ≤ S'.card := Finset.card_image_le
      have h3 : (insert l S').card = S'.card + 1 := Finset.card_insert_of_notMem hl
      omega
    by_cases hS'_emp : S' = ∅
    · subst hS'_emp
      refine ⟨A' :: π₀, hres_step, fun D hD => List.mem_cons_of_mem _ hD, ?_, ?_, ?_⟩
      · have : A' = {(Sum.inr k, false)} := by simp [A', liftCl]
        rw [← this]; exact List.mem_cons_self
      · simp
      · intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact hA'_card
        · exact hW₀ D hD
    · have hS'_ne : S'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS'_emp
      have hnoTaut' : ∀ v : V, ¬((v, true) ∈ S' ∧ (v, false) ∈ S') := fun v hv =>
        hnoTaut v ⟨Finset.mem_insert_of_mem hv.1, Finset.mem_insert_of_mem hv.2⟩
      have hW1 : ∀ D ∈ A' :: π₀, D.card ≤ W := by
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact hA'_card
        · exact hW₀ D hD
      have hS'_card : S'.card + 1 ≤ W := by
        have := Finset.card_insert_of_notMem hl
        omega
      obtain ⟨π, hD, hsub, hunit, hlen, hWπ⟩ :=
        ih (A' :: π₀) hres_step hW1 A' hS'_ne hnoTaut' (Or.inr rfl) List.mem_cons_self hS'_card
          (fun l' hl' => List.mem_cons_of_mem _ (hpairs l' (Finset.mem_insert_of_mem hl')))
      refine ⟨π, hD, fun D hD => hsub D (List.mem_cons_of_mem _ hD), hunit, ?_, hWπ⟩
      have hcard_ins : (insert l S').card = S'.card + 1 := Finset.card_insert_of_notMem hl
      simp only [List.length_cons] at hlen
      omega
private lemma derive_pairs {m : ℕ} {F : Set (Clause (V ⊕ Fin m))}
    (k : Fin m) (W : ℕ) (hW : 3 ≤ W)
    (hchain : ∀ l : Literal V, l ∈ (∅ : Finset (Literal V)) → True)
    (S : Finset (Literal V))
    (hax : ∀ l ∈ S, chainCl m k l ∈ F)
    (π₀ : List (Clause (V ⊕ Fin m))) (hD₀ : IsDerivation F π₀) (hW₀ : ∀ D ∈ π₀, D.card ≤ W)
    (hnext : ∀ hk : k.val + 1 < m, ({(Sum.inr ⟨k.val + 1, hk⟩, false)} : Clause (V ⊕ Fin m)) ∈ π₀) :
    ∃ π : List (Clause (V ⊕ Fin m)),
      IsDerivation F π ∧
      (∀ D ∈ π₀, D ∈ π) ∧
      (∀ l ∈ S, ({(Sum.inr k, false), (Sum.inl l.1, !l.2)} : Clause (V ⊕ Fin m)) ∈ π) ∧
      π.length ≤ π₀.length + 2 * S.card ∧
      (∀ D ∈ π, D.card ≤ W) := by
  induction S using Finset.induction_on generalizing π₀ with
  | empty =>
    exact ⟨π₀, hD₀, fun _ h => h, fun _ h => by simp at h, by simp, hW₀⟩
  | @insert l S' hl ih =>
    have hcl_ax : chainCl m k l ∈ F := hax l (Finset.mem_insert_self l S')
    have hD1 : IsDerivation F (chainCl m k l :: π₀) := IsDerivation.ax hD₀ hcl_ax
    have hW1 : ∀ D ∈ chainCl m k l :: π₀, D.card ≤ W := by
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact le_trans (chainCl_card_le m k l) hW
      · exact hW₀ D hD
    by_cases hk : k.val + 1 < m
    · let P : Clause (V ⊕ Fin m) := {(Sum.inr k, false), (Sum.inl l.1, !l.2)}
      let k1 : Fin m := ⟨k.val + 1, hk⟩
      have hne_kk1 : k ≠ k1 := by
        intro heq; have := congrArg Fin.val heq; simp [k1] at this
      have hres : IsResolvent (chainCl m k l) {(Sum.inr k1, false)} P := by
        refine ⟨Sum.inr k1, ?_, by simp, ?_⟩
        · simp [chainCl, hk, k1]
        · ext p
          simp only [chainCl, hk, dite_true, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton, P, k1]
          constructor
          · rintro (rfl | rfl)
            · exact Or.inl ⟨by simp [hne_kk1], Or.inl rfl⟩
            · exact Or.inl ⟨by simp, Or.inr (Or.inr rfl)⟩
          · rintro (⟨h1, rfl | rfl | rfl⟩ | ⟨h1, rfl⟩)
            · exact Or.inl rfl
            · exact absurd rfl h1
            · exact Or.inr rfl
            · exact absurd rfl h1
      have hD2 : IsDerivation F (P :: chainCl m k l :: π₀) :=
        IsDerivation.res hD1 List.mem_cons_self (List.mem_cons_of_mem _ (hnext hk)) hres
      have hW2 : ∀ D ∈ P :: chainCl m k l :: π₀, D.card ≤ W := by
        intro D hD
        rcases List.mem_cons.mp hD with rfl | hD
        · exact le_trans (le_trans (Finset.card_insert_le _ _) (by simp)) hW
        · exact hW1 D hD
      obtain ⟨π, hD, hsub, hp, hlen, hWπ⟩ :=
        ih (fun l' hl' => hax l' (Finset.mem_insert_of_mem hl'))
          (P :: chainCl m k l :: π₀) hD2 hW2
          (fun hk' => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hnext hk')))
      refine ⟨π, hD, fun D hD => hsub D (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hD)), ?_, ?_, hWπ⟩
      · intro l' hl'
        rcases Finset.mem_insert.mp hl' with rfl | hl'
        · exact hsub P List.mem_cons_self
        · exact hp l' hl'
      · have hcard := Finset.card_insert_of_notMem hl
        simp only [List.length_cons] at hlen
        omega
    · have hceq : chainCl m k l = {(Sum.inr k, false), (Sum.inl l.1, !l.2)} := by
        simp [chainCl, hk]
      obtain ⟨π, hD, hsub, hp, hlen, hWπ⟩ :=
        ih (fun l' hl' => hax l' (Finset.mem_insert_of_mem hl'))
          (chainCl m k l :: π₀) hD1 hW1
          (fun hk' => absurd hk' hk)
      refine ⟨π, hD, fun D hD => hsub D (List.mem_cons_of_mem _ hD), ?_, ?_, hWπ⟩
      · intro l' hl'
        rcases Finset.mem_insert.mp hl' with rfl | hl'
        · rw [← hceq]; exact hsub _ List.mem_cons_self
        · exact hp l' hl'
      · have hcard := Finset.card_insert_of_notMem hl
        simp only [List.length_cons] at hlen
        omega
private lemma derive_chain_units {m : ℕ} (hm : 0 < m) (L : Fin m → Clause V)
    (F : Set (Clause V)) (extra : Set (Clause (V ⊕ Fin m)))
    (W : ℕ) (hW : 3 ≤ W)
    (hLF : ∀ k : Fin m, L k ∈ F)
    (hLne : ∀ k : Fin m, (L k).Nonempty)
    (hLnoTaut : ∀ k : Fin m, ∀ v : V, ¬((v, true) ∈ L k ∧ (v, false) ∈ L k))
    (hLcard : ∀ k : Fin m, (L k).card + 1 ≤ W)
    (hchain : ∀ (k : Fin m), ∀ l ∈ L k, chainCl m k l ∈ extra) :
    ∀ d : ℕ, d < m →
      ∃ π : List (Clause (V ⊕ Fin m)),
        IsDerivation (Set.image (liftCl m) F ∪ extra) π ∧
        ({(Sum.inr ⟨m - 1 - d, by omega⟩, false)} : Clause (V ⊕ Fin m)) ∈ π ∧
        π.length ≤ (d + 1) * (3 * W) ∧
        (∀ D ∈ π, D.card ≤ W) := by
  intro d
  induction d with
  | zero =>
    intro hd
    let k : Fin m := ⟨m - 1, by omega⟩
    have hnotlt : ¬ (k.val + 1 < m) := by simp [k]; omega
    have hax_lk : liftCl m (L k) ∈ Set.image (liftCl m) F ∪ extra :=
      Or.inl ⟨L k, hLF k, rfl⟩
    let π₀ : List (Clause (V ⊕ Fin m)) := [liftCl m (L k)]
    have hD₀ : IsDerivation (Set.image (liftCl m) F ∪ extra) π₀ :=
      IsDerivation.ax IsDerivation.nil hax_lk
    have hW₀ : ∀ D ∈ π₀, D.card ≤ W := by
      intro D hD
      simp only [π₀, List.mem_singleton] at hD
      subst hD
      exact le_trans Finset.card_image_le (by have := hLcard k; omega)
    obtain ⟨π₁, hD₁, hsub₁, hpairs, hlen₁, hW₁⟩ :=
      derive_pairs k W hW (fun _ h => by simp at h) (L k)
        (fun l hl => Or.inr (hchain k l hl)) π₀ hD₀ hW₀ (fun hk => absurd hk hnotlt)
    obtain ⟨π₂, hD₂, _, hunit, hlen₂, hW₂⟩ :=
      resolve_set_away k W (by omega) π₁ hD₁ hW₁ (L k) (liftCl m (L k))
        (hLne k) (hLnoTaut k) (Or.inl rfl) (hsub₁ _ List.mem_cons_self) (hLcard k) hpairs
    refine ⟨π₂, hD₂, by simpa [k] using hunit, ?_, hW₂⟩
    have hLk : (L k).card + 1 ≤ W := hLcard k
    simp only [π₀, List.length_singleton] at hlen₁
    omega
  | succ d ih =>
    intro hd
    obtain ⟨π₀, hD₀, hprev, hlen₀, hW₀⟩ := ih (by omega)
    let k : Fin m := ⟨m - 1 - (d + 1), by omega⟩
    have hlt : k.val + 1 < m := by simp [k]; omega
    have hidx : (⟨k.val + 1, hlt⟩ : Fin m) = ⟨m - 1 - d, by omega⟩ := by
      ext; simp [k]; omega
    have hnext : ∀ hk : k.val + 1 < m,
        ({(Sum.inr ⟨k.val + 1, hk⟩, false)} : Clause (V ⊕ Fin m)) ∈ π₀ := by
      intro hk
      have heq : (⟨k.val + 1, hk⟩ : Fin m) = ⟨m - 1 - d, by omega⟩ := by
        ext; simp [k]; omega
      rw [heq]; exact hprev
    have hax_lk : liftCl m (L k) ∈ Set.image (liftCl m) F ∪ extra :=
      Or.inl ⟨L k, hLF k, rfl⟩
    let π₁ := liftCl m (L k) :: π₀
    have hD₁ : IsDerivation (Set.image (liftCl m) F ∪ extra) π₁ := IsDerivation.ax hD₀ hax_lk
    have hW₁ : ∀ D ∈ π₁, D.card ≤ W := by
      intro D hD
      rcases List.mem_cons.mp hD with rfl | hD
      · exact le_trans Finset.card_image_le (by have := hLcard k; omega)
      · exact hW₀ D hD
    obtain ⟨π₂, hD₂, hsub₂, hpairs, hlen₂, hW₂⟩ :=
      derive_pairs k W hW (fun _ h => by simp at h) (L k)
        (fun l hl => Or.inr (hchain k l hl)) π₁ hD₁ hW₁
        (fun hk => List.mem_cons_of_mem _ (hnext hk))
    obtain ⟨π₃, hD₃, _, hunit, hlen₃, hW₃⟩ :=
      resolve_set_away k W (by omega) π₂ hD₂ hW₂ (L k) (liftCl m (L k))
        (hLne k) (hLnoTaut k) (Or.inl rfl) (hsub₂ _ List.mem_cons_self) (hLcard k) hpairs
    refine ⟨π₃, hD₃, hunit, ?_, hW₃⟩
    have hLk : (L k).card + 1 ≤ W := hLcard k
    simp only [π₁, List.length_cons] at hlen₂
    have : (d + 1 + 1) * (3 * W) = (d + 1) * (3 * W) + 3 * W := by ring
    omega
private lemma chain_upper_bound (F : Set (Clause V)) (Ffin : Finset (Clause V)) (w : ℕ) (hw : 2 ≤ w)
    (hSub : ∀ C ∈ Ffin, C ∈ F)
    (hNonempty : Ffin.Nonempty)
    (hUnsat : ∀ x : V → Bool, ∃ C ∈ Ffin, ¬ ClauseSat x C)
    (hWidth : ∀ C ∈ Ffin, C.card ≤ w)
    (hNoTaut : ∀ C ∈ Ffin, ∀ v : V, ¬((v, true) ∈ C ∧ (v, false) ∈ C)) :
    ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
      (extra : Finset (Clause (V ⊕ Fin h)))
      (π : List (Clause (V ⊕ Fin h))),
      (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
      (∀ x : V → Bool, ∃ j : Fin t, Satisfies (Sum.elim x (menu j)) (↑extra : Set _)) ∧
      IsRefutation (Set.image (liftCl h) F ∪ (↑extra : Set _)) π ∧
      h + t + extra.card + π.length ≤ (4 * w + 6) * Ffin.card + 3 ∧
      ∀ D ∈ π, D.card ≤ w + 1 := by
  by_cases hEmp : (∅ : Clause V) ∈ Ffin
  · refine ⟨0, 1, fun _ => Fin.elim0, ∅, [∅], ?_, ?_, ?_, ?_, ?_⟩
    · intro D hD; simp at hD
    · intro x; exact ⟨0, fun D hD => by simp at hD⟩
    · refine ⟨IsDerivation.ax IsDerivation.nil (Or.inl ⟨∅, hSub ∅ hEmp, by simp [liftCl]⟩),
        List.mem_cons_self⟩
    · have hpos : 1 ≤ Ffin.card := Finset.card_pos.mpr hNonempty
      simp only [Finset.card_empty, List.length_singleton]
      nlinarith
    · intro D hD; simp at hD; subst hD; simp
  · let Llist : List (Clause V) := Ffin.toList
    set m := Llist.length with hm_def
    have hm_eq : m = Ffin.card := Finset.length_toList Ffin
    have hm_pos : 0 < m := by rw [hm_eq]; exact Finset.card_pos.mpr hNonempty
    let L : Fin m → Clause V := fun k => Llist[k.val]'k.isLt
    have hL_mem : ∀ k : Fin m, L k ∈ Ffin := fun k =>
      Finset.mem_toList.mp (List.getElem_mem k.isLt)
    have hmem_L : ∀ C ∈ Ffin, ∃ k : Fin m, L k = C := by
      intro C hC
      have hmem : C ∈ Llist := Finset.mem_toList.mpr hC
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
      exact ⟨⟨i, hi⟩, rfl⟩
    let rootCl : Clause (V ⊕ Fin m) := {(Sum.inr ⟨0, hm_pos⟩, true)}
    let bodyCl : Finset (Clause (V ⊕ Fin m)) :=
      (Finset.univ : Finset (Fin m)).biUnion fun k => (L k).image (chainCl m k)
    let extra : Finset (Clause (V ⊕ Fin m)) := insert rootCl bodyCl
    let menu : Fin m → Fin m → Bool := fun j k => decide (k.val ≤ j.val)
    have hroot_mem : rootCl ∈ extra := Finset.mem_insert_self _ _
    have hchain_mem : ∀ (k : Fin m), ∀ l ∈ L k, chainCl m k l ∈ extra := fun k l hl =>
      Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
        Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩)
    have hextra_card : extra.card ≤ 1 + w * m := by
      have h1 : extra.card ≤ bodyCl.card + 1 := Finset.card_insert_le _ _
      have h2 : bodyCl.card ≤ ∑ k : Fin m, ((L k).image (chainCl m k)).card := Finset.card_biUnion_le
      have h3 : ∑ k : Fin m, ((L k).image (chainCl m k)).card ≤ ∑ _k : Fin m, w :=
        Finset.sum_le_sum fun k _ => le_trans Finset.card_image_le (hWidth (L k) (hL_mem k))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h3
      rw [mul_comm] at h3
      omega
    have hextra_width : ∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1 := by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · constructor
        · simp [rootCl]
        · have : rootCl.filter (fun l => l.1.isLeft) = ∅ := by
            ext p; simp [rootCl]; rintro rfl; simp
          simp [this]
      · obtain ⟨k, _, hDk⟩ := Finset.mem_biUnion.mp hD
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hDk
        exact ⟨chainCl_card_le m k l, chainCl_left_card_le m k l⟩
    have hmenu_sat : ∀ x : V → Bool, ∃ j : Fin m, Satisfies (Sum.elim x (menu j)) (↑extra : Set _) := by
      intro x
      obtain ⟨C, hCF, hCfalse⟩ := hUnsat x
      obtain ⟨j, rfl⟩ := hmem_L C hCF
      refine ⟨j, fun D hD => ?_⟩
      rcases Finset.mem_insert.mp hD with rfl | hD
      · refine ⟨(Sum.inr ⟨0, hm_pos⟩, true), by simp [rootCl], ?_⟩
        simp only [Sum.elim_inr, menu, decide_eq_true_eq]
        exact Nat.zero_le _
      · obtain ⟨k, _, hDk⟩ := Finset.mem_biUnion.mp hD
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hDk
        by_cases hkj : k.val < j.val
        · have hk1 : k.val + 1 < m := by omega
          refine ⟨(Sum.inr ⟨k.val + 1, hk1⟩, true), by simp [chainCl, hk1], ?_⟩
          simp only [Sum.elim_inr, menu, decide_eq_true_eq]
          omega
        · by_cases heq : k.val = j.val
          · have hkj_fin : k = j := Fin.ext heq
            subst hkj_fin
            have hnotl : x l.1 ≠ l.2 := fun h => hCfalse ⟨l, hl, h⟩
            have hneg : x l.1 = !l.2 := by cases hx : x l.1 <;> cases hs : l.2 <;> simp_all
            refine ⟨(Sum.inl l.1, !l.2), ?_, by simpa using hneg⟩
            unfold chainCl; split_ifs <;> simp
          · refine ⟨(Sum.inr k, false), ?_, ?_⟩
            · unfold chainCl; split_ifs <;> simp
            · simp only [Sum.elim_inr, menu, decide_eq_false_iff_not]
              omega
    obtain ⟨π₀, hD₀, hunit0, hlen₀, hW₀⟩ :=
      derive_chain_units hm_pos L F (↑extra : Set _) (w + 1) (by omega)
        (fun k => hSub (L k) (hL_mem k))
        (fun k => Finset.nonempty_iff_ne_empty.mpr (fun he => hEmp (he ▸ hL_mem k)))
        (fun k => hNoTaut (L k) (hL_mem k))
        (fun k => Nat.add_le_add_right (hWidth (L k) (hL_mem k)) 1)
        (fun k l hl => hchain_mem k l hl)
        (m - 1) (by omega)
    have hidx0 : (⟨m - 1 - (m - 1), by omega⟩ : Fin m) = ⟨0, hm_pos⟩ := by ext; simp
    rw [hidx0] at hunit0
    let π₁ := rootCl :: π₀
    have hD₁ : IsDerivation (Set.image (liftCl m) F ∪ (↑extra : Set _)) π₁ :=
      IsDerivation.ax hD₀ (Or.inr hroot_mem)
    have hres_end : IsResolvent rootCl {(Sum.inr ⟨0, hm_pos⟩, false)} ∅ := by
      refine ⟨Sum.inr ⟨0, hm_pos⟩, by simp [rootCl], by simp, ?_⟩
      ext p; simp [rootCl]
    let π := (∅ : Clause (V ⊕ Fin m)) :: π₁
    have hD : IsDerivation (Set.image (liftCl m) F ∪ (↑extra : Set _)) π :=
      IsDerivation.res hD₁ List.mem_cons_self (List.mem_cons_of_mem _ hunit0) hres_end
    refine ⟨m, m, menu, extra, π, hextra_width, hmenu_sat, ⟨hD, List.mem_cons_self⟩, ?_, ?_⟩
    · have hplen : π.length ≤ m * (3 * (w + 1)) + 2 := by
        have hm1 : m - 1 + 1 = m := by omega
        rw [hm1] at hlen₀
        simp only [π, π₁, List.length_cons]
        omega
      rw [← hm_eq]
      nlinarith
    · intro D hDmem
      rcases List.mem_cons.mp hDmem with rfl | hDmem
      · simp
      · rcases List.mem_cons.mp hDmem with rfl | hDmem
        · simp [rootCl]
        · exact hW₀ D hDmem
end ChainRefutation
private lemma upper_bound_on_expander (b n : ℕ) (hn : 1 ≤ n) (G : BipGraph (n + 1) n)
    (hLd : LeftDegLe G b) (hRd : RightDegLe G b)
    (w : ℕ) (hw : w = max b 2) :
    let V := GEdge G
    let F := funGraphPHP G
    ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
      (extra : Finset (Clause (V ⊕ Fin h)))
      (π : List (Clause (V ⊕ Fin h))),
      (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
      (∀ x : V → Bool, ∃ j : Fin t, Satisfies (Sum.elim x (menu j)) (↑extra : Set _)) ∧
      IsRefutation (Set.image (liftCl h) F ∪ (↑extra : Set _)) π ∧
      h + t + extra.card + π.length ≤ ((4 * w + 6) * (b ^ 2 + 2) + 3) * n ∧
      ∀ D ∈ π, D.card ≤ w + 1 := by
  intro V F
  let pigCl : Fin (n + 1) → Clause V := fun i =>
    Finset.univ.filter (fun l : Literal V => l.1.1.1 = i ∧ l.2 = true)
  let pigSet : Finset (Clause V) := Finset.univ.image pigCl
  let holeEdges (j : Fin n) : Finset V :=
    Finset.univ.filter (fun e : V => e.1.2 = j)
  let holeSet : Finset (Clause V) :=
    (Finset.univ : Finset (Fin n)).biUnion fun j =>
      ((holeEdges j ×ˢ holeEdges j).filter (fun p => p.1.1.1 ≠ p.2.1.1)).image
        (fun p => ({(p.1, false), (p.2, false)} : Clause V))
  let Ffin : Finset (Clause V) := pigSet ∪ holeSet
  have hSub : ∀ C ∈ Ffin, C ∈ F := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      exact Or.inl (Or.inl ⟨i, rfl⟩)
    · obtain ⟨j, _, hCj⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨⟨e, e'⟩, hp, rfl⟩ := Finset.mem_image.mp hCj
      simp only [Finset.mem_filter, Finset.mem_product, holeEdges, Finset.mem_univ, true_and] at hp
      exact Or.inl (Or.inr ⟨e, e', hp.1.1.trans hp.1.2.symm, hp.2, rfl⟩)
  have hNonempty : Ffin.Nonempty :=
    ⟨pigCl 0, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩)⟩
  have hUnsat : ∀ x : V → Bool, ∃ C ∈ Ffin, ¬ ClauseSat x C := by
    intro x
    by_contra hall
    push_neg at hall
    have hpig : ∀ i : Fin (n + 1), ∃ e : V, e.1.1 = i ∧ x e = true := by
      intro i
      have hsat := hall (pigCl i)
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      obtain ⟨⟨e, s⟩, he, hxe⟩ := hsat
      simp only [pigCl, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact ⟨e, he.1, he.2 ▸ hxe⟩
    choose f hf1 hf2 using hpig
    have hcard_lt : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
    obtain ⟨i₁, i₂, hne, hsame⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => (f i).1.2) hcard_lt
    let j := (f i₁).1.2
    have hmem : ({(f i₁, false), (f i₂, false)} : Clause V) ∈ Ffin := by
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩)
      refine Finset.mem_image.mpr ⟨(f i₁, f i₂), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_product, holeEdges, Finset.mem_univ, true_and]
      exact ⟨⟨rfl, hsame.symm⟩, by rw [hf1 i₁, hf1 i₂]; exact hne⟩
    obtain ⟨l, hl, hxl⟩ := hall _ hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · rw [hf2 i₁] at hxl; exact Bool.noConfusion hxl
    · rw [hf2 i₂] at hxl; exact Bool.noConfusion hxl
  have hw2 : 2 ≤ w := hw ▸ le_max_right _ _
  have hbw : b ≤ w := hw ▸ le_max_left _ _
  have hWidth : ∀ C ∈ Ffin, C.card ≤ w := by
    intro C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      have hinj : Function.Injective (fun l : {l : Literal V // l ∈ pigCl i} => l.1.1.1.2) := by
        intro a b hab
        apply Subtype.ext
        have ha := (Finset.mem_filter.mp a.2).2
        have hb := (Finset.mem_filter.mp b.2).2
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext (ha.1.trans hb.1.symm) hab
        · exact ha.2.trans hb.2.symm
      have hsub : (pigCl i).image (fun l => l.1.1.2) ⊆ G i := by
        intro j hj
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
        have hli := (Finset.mem_filter.mp hl).2.1
        exact hli ▸ l.1.2
      have hcard_eq : ((pigCl i).image (fun l => l.1.1.2)).card = (pigCl i).card := by
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        have ha' := (Finset.mem_filter.mp ha).2
        have hb' := (Finset.mem_filter.mp hb).2
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext (ha'.1.trans hb'.1.symm) hab
        · exact ha'.2.trans hb'.2.symm
      calc (pigCl i).card = ((pigCl i).image (fun l => l.1.1.2)).card := hcard_eq.symm
        _ ≤ (G i).card := Finset.card_le_card hsub
        _ ≤ b := hLd i
        _ ≤ w := hbw
    · obtain ⟨j, _, hCj⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hCj
      exact le_trans (le_trans (Finset.card_insert_le _ _) (by simp)) hw2
  have hNoTaut : ∀ C ∈ Ffin, ∀ v : V, ¬((v, true) ∈ C ∧ (v, false) ∈ C) := by
    intro C hC v hv
    rcases Finset.mem_union.mp hC with hC | hC
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
      have := (Finset.mem_filter.mp hv.2).2.2
      exact Bool.noConfusion this
    · obtain ⟨j, _, hCj⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hCj
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Bool.true_eq_false,
        and_false, or_self] at hv
      exact hv.1
  have hholeEdges_card : ∀ j : Fin n, (holeEdges j).card ≤ b := by
    intro j
    have hsub : (holeEdges j).image (fun e : V => e.1.1) ⊆ rightNbrs G j := by
      intro i hi
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
      have hej := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hej ▸ e.2⟩
    have hcard_eq : ((holeEdges j).image (fun e : V => e.1.1)).card = (holeEdges j).card := by
      apply Finset.card_image_of_injOn
      intro e1 he1 e2 he2 heq
      have h1 := (Finset.mem_filter.mp he1).2
      have h2 := (Finset.mem_filter.mp he2).2
      exact Subtype.ext (Prod.ext heq (h1.trans h2.symm))
    calc (holeEdges j).card = ((holeEdges j).image (fun e : V => e.1.1)).card := hcard_eq.symm
      _ ≤ (rightNbrs G j).card := Finset.card_le_card hsub
      _ ≤ b := hRd j
  have hFfin_card : Ffin.card ≤ (b ^ 2 + 2) * n := by
    have hp : pigSet.card ≤ n + 1 :=
      le_trans Finset.card_image_le (by simp)
    have hh : holeSet.card ≤ n * b ^ 2 := by
      calc holeSet.card
          ≤ ∑ j : Fin n, (((holeEdges j ×ˢ holeEdges j).filter
              (fun p => p.1.1.1 ≠ p.2.1.1)).image _).card := Finset.card_biUnion_le
        _ ≤ ∑ j : Fin n, (holeEdges j ×ˢ holeEdges j).card :=
            Finset.sum_le_sum fun j _ =>
              le_trans Finset.card_image_le (Finset.card_filter_le _ _)
        _ ≤ ∑ _j : Fin n, b ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Finset.card_product, sq]
            exact Nat.mul_le_mul (hholeEdges_card j) (hholeEdges_card j)
        _ = n * b ^ 2 := by simp
    have hu : Ffin.card ≤ pigSet.card + holeSet.card := Finset.card_union_le _ _
    have : n + 1 + n * b ^ 2 ≤ (b ^ 2 + 2) * n := by nlinarith
    omega
  obtain ⟨h, t, menu, extra, π, hwid, hsat, href, hsz, hpiW⟩ :=
    chain_upper_bound F Ffin w hw2 hSub hNonempty hUnsat hWidth hNoTaut
  refine ⟨h, t, menu, extra, π, hwid, hsat, href, ?_, hpiW⟩
  calc h + t + extra.card + π.length
      ≤ (4 * w + 6) * Ffin.card + 3 := hsz
    _ ≤ (4 * w + 6) * ((b ^ 2 + 2) * n) + 3 * n := by
        have h1 : (4 * w + 6) * Ffin.card ≤ (4 * w + 6) * ((b ^ 2 + 2) * n) :=
          Nat.mul_le_mul_left _ hFfin_card
        have h2 : 3 ≤ 3 * n := by omega
        omega
    _ = ((4 * w + 6) * (b ^ 2 + 2) + 3) * n := by ring
end PEqualNP.Outside.L_pcx_377_aux
theorem PEqualNP.Outside.L_pcx_377 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let F := PEqualNP.Expanders.funGraphPHP G
    (∀ (a h t r p q : ℕ) (f : (V → Bool) → Fin a → Bool)
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
          n ≤ C^k * t * (r + Nat.clog 2 (π.length+1) + 1)) ∧
    ∃ (h t : ℕ) (menu : Fin t → Fin h → Bool)
        (extra : Finset (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))
        (π : List (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h))),
      let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
        cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin h), l.2))
      (∀ D ∈ extra, D.card ≤ 3 ∧ (D.filter (fun l => l.1.isLeft)).card ≤ 1) ∧
      (∀ x : V → Bool, ∃ j : Fin t, PEqualNP.ProofComplexity.Satisfies
        (Sum.elim x (menu j)) (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) ∧
      PEqualNP.ProofComplexity.IsRefutation
        (Set.image lift F ∪ (↑extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin h)))) π ∧
      h + t + extra.card + π.length ≤ C*n ∧ ∀ D ∈ π, D.card ≤ C) := by
  obtain ⟨b, s₀, n₀_43, hs₀, hG⟩ := PEqualNP.Outside.L_pcx_377_aux.C.L043
  set w := max b 2
  set C_low := 768 * (16 * s₀ * w ^ 2) * s₀ * w
  set C_up := max (w + 1) ((4 * w + 6) * (b ^ 2 + 2) + 3)
  set C := max (max b 2) (max C_low C_up)
  set n₀ := max n₀_43 (max (4 * (s₀ * w) + s₀) 1)
  refine ⟨C, n₀, by omega, fun n hn => ?_⟩
  have hn_43 : n₀_43 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 4 * (s₀ * w) + s₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_pos : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨G, hLd, hRd, hE⟩ := hG n hn_43
  have hbC : b ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hClow : C_low ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCup : C_up ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨G, fun i => le_trans (hLd i) hbC, fun j => le_trans (hRd j) hbC, ?_, ?_⟩
  · intro a h t r p q f menu W lift k ht hcert extra hwidth hmenu π hπ
    exact PEqualNP.Outside.L_pcx_377_aux.lower_bound_on_expander b s₀ n hs₀ G hLd hE w rfl
      hn2 C hClow a h t r p q f menu ht hcert extra hwidth hmenu π hπ
  · obtain ⟨h, t, menu, extra, π, hwid, hsat, href, hsz, hpiW⟩ :=
      PEqualNP.Outside.L_pcx_377_aux.upper_bound_on_expander b n hn_pos G hLd hRd w rfl
    have hCup1 : (4 * w + 6) * (b ^ 2 + 2) + 3 ≤ C := le_trans (le_max_right _ _) hCup
    have hCup2 : w + 1 ≤ C := le_trans (le_max_left _ _) hCup
    exact ⟨h, t, menu, extra, π, hwid, hsat, href,
      le_trans hsz (Nat.mul_le_mul_right n hCup1),
      fun D hD => le_trans (hpiW D hD) hCup2⟩
