import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25663

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents


def signZ (b : Bool) : ℤ := if b then -1 else 1

lemma signZ_xor (a b : Bool) : signZ (xor a b) = signZ a * signZ b := by
  cases a <;> cases b <;> rfl

lemma signZ_not (a : Bool) : signZ (!a) = - signZ a := by
  cases a <;> rfl

lemma signZ_mul_self (a : Bool) : signZ a * signZ a = 1 := by
  cases a <;> rfl

lemma signZ_eq_neg_iff (a b : Bool) : signZ a = - signZ b ↔ a = !b := by
  cases a <;> cases b <;> simp [signZ]

lemma signZ_le_one (a : Bool) : signZ a ≤ 1 := by
  cases a <;> simp [signZ]

lemma neg_one_le_signZ (a : Bool) : -1 ≤ signZ a := by
  cases a <;> simp [signZ]

lemma sum_signZ_ge_neg_card {ι : Type} (S : Finset ι) (f : ι → Bool) :
    -(S.card : ℤ) ≤ ∑ x ∈ S, signZ (f x) := by
  have h1 : ∑ x ∈ S, (-1 : ℤ) ≤ ∑ x ∈ S, signZ (f x) :=
    Finset.sum_le_sum (fun x _ => neg_one_le_signZ (f x))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one] at h1
  exact h1

lemma sum_signZ_le_card {ι : Type} (S : Finset ι) (f : ι → Bool) :
    ∑ x ∈ S, signZ (f x) ≤ (S.card : ℤ) := by
  have h1 : ∑ x ∈ S, signZ (f x) ≤ ∑ x ∈ S, (1 : ℤ) :=
    Finset.sum_le_sum (fun x _ => signZ_le_one (f x))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
  exact h1

lemma sum_signZ_extremal {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → Bool) (c : Bool)
    (hsum : ∑ x ∈ S, signZ (f x) = -(signZ c) * (S.card : ℤ)) :
    ∀ x ∈ S, f x = !c := by
  intro x0 hx0
  by_contra hne
  have hfx0 : f x0 = c := by
    cases h1 : f x0 <;> cases c <;> simp_all
  have hmul : signZ c * (∑ x ∈ S, signZ (f x)) = -(S.card : ℤ) := by
    rw [hsum]
    have hs := signZ_mul_self c
    calc
      signZ c * (-(signZ c) * (S.card : ℤ)) = -((signZ c * signZ c) * (S.card : ℤ)) := by ring
      _ = -(S.card : ℤ) := by rw [hs, one_mul]
  have hsplit : signZ c * (∑ x ∈ S, signZ (f x)) =
      1 + ∑ x ∈ S.erase x0, signZ (xor c (f x)) := by
    rw [Finset.mul_sum, ← Finset.add_sum_erase S (fun x => signZ c * signZ (f x)) hx0]
    rw [hfx0, signZ_mul_self]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [signZ_xor]
  have hge := sum_signZ_ge_neg_card (S.erase x0) (fun x => xor c (f x))
  have hcard : ((S.erase x0).card : ℤ) + 1 = (S.card : ℤ) := by
    have h1 := Finset.card_erase_add_one hx0
    omega
  omega

lemma sum_signZ_eq_zero_of_invol {α : Type} [Fintype α] (f : α → Bool)
    (σ : α → α) (hinv : ∀ x, σ (σ x) = x) (hflip : ∀ x, f (σ x) = !(f x)) :
    ∑ x : α, signZ (f x) = 0 := by
  let e : α ≃ α := ⟨σ, σ, hinv, hinv⟩
  have h1 : ∑ x : α, signZ (f (e x)) = ∑ x : α, signZ (f x) :=
    Fintype.sum_equiv e (fun x => signZ (f (e x))) (fun x => signZ (f x)) (fun _ => rfl)
  have h2 : ∑ x : α, signZ (f (e x)) = -(∑ x : α, signZ (f x)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact (congrArg signZ (hflip x)).trans (signZ_not (f x))
  omega

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def z2b (x : ZMod 2) : Bool := decide (x = 1)

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma z2b_b2z (a : Bool) : z2b (b2z a) = a := by
  cases a <;> decide

lemma b2z_z2b (x : ZMod 2) : b2z (z2b x) = x := by
  fin_cases x
  · rfl
  · rfl

lemma z2b_add (x y : ZMod 2) : z2b (x + y) = xor (z2b x) (z2b y) := by
  fin_cases x <;> fin_cases y <;> rfl

lemma z2b_sum_b2z_eq_card_mod2 {ι : Type} [Fintype ι] (f : ι → Bool) :
    z2b (∑ i : ι, b2z (f i)) =
      (((Finset.univ : Finset ι).filter (fun i => f i = true)).card % 2 == 1) := by
  have hsum : ∑ i : ι, b2z (f i) =
      ((((Finset.univ : Finset ι).filter (fun i => f i = true)).card : ℕ) : ZMod 2) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases f i <;> simp [b2z]
  rw [hsum]
  set m := ((Finset.univ : Finset ι).filter (fun i => f i = true)).card
  have hm : ((m : ℕ) : ZMod 2) = ((m % 2 : ℕ) : ZMod 2) := by
    have hdiv := Nat.div_add_mod m 2
    have hcast : ((2 * (m / 2) + m % 2 : ℕ) : ZMod 2) = (m : ZMod 2) := by rw [hdiv]
    rw [← hcast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_mul, zero_add]
  rw [hm]
  have hlt : m % 2 < 2 := Nat.mod_lt m (by omega)
  interval_cases (m % 2) <;> decide

def IsHadamard {α β : Type} [Fintype α] [Fintype β] (G : α → β → Bool) : Prop :=
  ∀ u1 u2 : α, u1 ≠ u2 → ∑ v : β, signZ (xor (G u1 v) (G u2 v)) = 0

lemma hadamard_transpose {N : ℕ} (hN : 0 < N) {G : Fin N → Fin N → Bool}
    (hH : IsHadamard G) : IsHadamard (fun v u => G u v) := by
  let M : Matrix (Fin N) (Fin N) ℚ := fun u v => (signZ (G u v) : ℚ)
  let M' : Matrix (Fin N) (Fin N) ℚ := fun v u => ((N : ℚ)⁻¹) * (signZ (G u v) : ℚ)
  have hNq : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hmul : M * M' = 1 := by
    ext u1 u2
    rw [Matrix.mul_apply, Matrix.one_apply]
    dsimp only [M, M']
    have hpull : ∑ v : Fin N, (signZ (G u1 v) : ℚ) * ((N : ℚ)⁻¹ * (signZ (G u2 v) : ℚ)) =
        (N : ℚ)⁻¹ * ((∑ v : Fin N, signZ (xor (G u1 v) (G u2 v)) : ℤ) : ℚ) := by
      rw [Int.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [signZ_xor, Int.cast_mul]
      ring
    rw [hpull]
    by_cases heq : u1 = u2
    · subst heq
      have hdiag : ∑ v : Fin N, signZ (xor (G u1 v) (G u1 v)) = (N : ℤ) := by
        simp [signZ]
      rw [hdiag, Int.cast_natCast, if_pos rfl, inv_mul_cancel₀ hNq]
    · rw [hH u1 u2 heq, Int.cast_zero, mul_zero, if_neg heq]
  have hmul' : M' * M = 1 := by
    let f : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) := Matrix.mulVecLin M
    let g : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) := Matrix.mulVecLin M'
    have hfg : f.comp g = LinearMap.id := by
      dsimp only [f, g]
      rw [← Matrix.mulVecLin_mul, hmul, Matrix.mulVecLin_one]
    have hsurj : Function.Surjective f := fun y => ⟨g y, by simpa using LinearMap.congr_fun hfg y⟩
    have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
    have hgf : g.comp f = LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply hinj
      change (f.comp g) (f x) = f x
      rw [hfg]; rfl
    ext v1 v2
    let e : Fin N → ℚ := fun i => if i = v2 then 1 else 0
    have h1 := congrFun (LinearMap.congr_fun hgf e) v1
    have hL : ((g.comp f) e) v1 = (M' * M) v1 v2 := by
      have hcomp : g.comp f = Matrix.mulVecLin (M' * M) := by
        dsimp only [f, g]
        rw [Matrix.mulVecLin_mul]
      rw [hcomp]
      simp [Matrix.mulVec, dotProduct, e]
      rw [Matrix.mul_apply]
    have hR : ((LinearMap.id : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ)) e) v1 = (1 : Matrix (Fin N) (Fin N) ℚ) v1 v2 := by
      simp [e, Matrix.one_apply]
    rw [← hL, h1, hR]
  intro v1 v2 hne
  have hent := congrFun (congrFun hmul' v1) v2
  rw [Matrix.mul_apply, Matrix.one_apply, if_neg hne] at hent
  dsimp only [M, M'] at hent
  have hpull : ∑ u : Fin N, ((N : ℚ)⁻¹ * (signZ (G u v1) : ℚ)) * (signZ (G u v2) : ℚ) =
      (N : ℚ)⁻¹ * ((∑ u : Fin N, signZ (xor (G u v1) (G u v2)) : ℤ) : ℚ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [signZ_xor, Int.cast_mul]
    ring
  rw [hpull] at hent
  have hq : ((∑ u : Fin N, signZ (xor (G u v1) (G u v2)) : ℤ) : ℚ) = 0 := by
    rcases mul_eq_zero.mp hent with hinv | h0
    · exact absurd (inv_ne_zero hNq) (not_not.mpr hinv)
    · exact h0
  exact Int.cast_eq_zero.mp hq

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

lemma affine_gate_2 (f : Bool → Bool → Bool)
    (hlin : xor (xor (f false false) (f false true)) (xor (f true false) (f true true)) = false) :
    ∃ c0 c1 c2 : Bool, ∀ x y : Bool, f x y = xor c0 (xor (c1 && x) (c2 && y)) := by
  refine ⟨f false false, xor (f false false) (f true false), xor (f false false) (f false true), ?_⟩
  intro x y
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    simp [h00, h01, h10, h11] at hlin
  all_goals (cases x <;> cases y <;> simp [h00, h01, h10, h11])

lemma nonlinear_gate_2 (f : Bool → Bool → Bool)
    (hnl : xor (xor (f false false) (f false true)) (xor (f true false) (f true true)) = true) :
    ∃ c0 c1 c2 : Bool, ∀ x y : Bool, f x y = xor c0 ((xor x c1) && (xor y c2)) := by
  refine ⟨xor (f false false) ((xor (f false false) (f false true)) && (xor (f false false) (f true false))),
    xor (f false false) (f false true), xor (f false false) (f true false), ?_⟩
  intro x y
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    simp [h00, h01, h10, h11] at hnl
  all_goals (cases x <;> cases y <;> simp [h00, h01, h10, h11])

lemma affine_gate_1 (f : Bool → Bool) :
    ∃ c0 c1 : Bool, ∀ x : Bool, f x = xor c0 (c1 && x) := by
  refine ⟨f false, xor (f false) (f true), ?_⟩
  intro x
  cases h0 : f false <;> cases h1 : f true <;> cases x <;> simp [h0, h1]

inductive GenGate (α β : Type) where
  | pureU (f : α → Bool)
  | pureV (g : β → Bool)
  | real (g : Gate)

def GenGate.nl {α β : Type} : GenGate α β → Bool
  | GenGate.real g => nonlinear g
  | _ => false

def GenGate.eval {α β : Type} (u : α) (v : β) (w : List Bool) : GenGate α β → Bool
  | GenGate.pureU f => f u
  | GenGate.pureV g => g v
  | GenGate.real g => g.op.eval (g.inputs.map (fun i => w.getD i false))

def evalGen {α β : Type} (gs : List (GenGate α β)) (init : List Bool) (u : α) (v : β) : List Bool :=
  gs.foldl (fun w g => w ++ [g.eval u v w]) init

lemma evalGen_append {α β : Type} (gs1 gs2 : List (GenGate α β)) (init : List Bool) (u : α) (v : β) :
    evalGen (gs1 ++ gs2) init u v = evalGen gs2 (evalGen gs1 init u v) u v := by
  simp [evalGen, List.foldl_append]

lemma evalGen_length {α β : Type} (gs : List (GenGate α β)) (init : List Bool) (u : α) (v : β) :
    (evalGen gs init u v).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [evalGen]
  | cons g gs ih =>
    simp only [evalGen, List.foldl_cons]
    have h1 := ih (init ++ [g.eval u v init])
    simp only [evalGen, List.length_append, List.length_singleton] at h1
    simp only [List.length_cons]
    omega

def GenFanIn2 {α β : Type} (gs : List (GenGate α β)) : Prop :=
  ∀ gg ∈ gs, match gg with
    | GenGate.real g => g.inputs.length ≤ 2
    | _ => True

def GenReadsBack {α β : Type} (n0 : ℕ) (gs : List (GenGate α β)) : Prop :=
  ∀ j (hj : j < gs.length), match gs[j] with
    | GenGate.real g => ∀ i ∈ g.inputs, i < n0 + j
    | _ => True

lemma evalGen_cons {α β : Type} (g : GenGate α β) (gs : List (GenGate α β))
    (init : List Bool) (u : α) (v : β) :
    evalGen (g :: gs) init u v = evalGen gs (init ++ [g.eval u v init]) u v := rfl

lemma evalGen_prefix_agree {α β : Type} (gs : List (GenGate α β)) (init : List Bool)
    (u : α) (v : β) (i : ℕ) (hi : i < init.length) :
    (evalGen gs init u v).getD i false = init.getD i false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGen_cons]
    have hi' : i < (init ++ [g.eval u v init]).length := by simp; omega
    rw [ih (init ++ [g.eval u v init]) hi']
    simp [List.getD, List.getElem?_append_left hi]

lemma evalGen_zero_affine {α β : Type} (gs : List (GenGate α β)) (n0 : ℕ)
    (init : α → β → List Bool)
    (hlen : ∀ u v, (init u v).length = n0)
    (hinit : ∀ i < n0, ∃ (a : α → Bool) (b : β → Bool),
      ∀ u v, (init u v).getD i false = xor (a u) (b v))
    (hfan : GenFanIn2 gs) (hnl0 : gs.countP GenGate.nl = 0) :
    ∀ i, ∃ (a : α → Bool) (b : β → Bool),
      ∀ u v, (evalGen gs (init u v) u v).getD i false = xor (a u) (b v) := by
  induction gs generalizing n0 init with
  | nil =>
    intro i
    by_cases hi : i < n0
    · exact hinit i hi
    · refine ⟨fun _ => false, fun _ => false, fun u v => ?_⟩
      have hge : (init u v).length ≤ i := by rw [hlen u v]; omega
      simp [evalGen, List.getD, List.getElem?_eq_none hge]
  | cons gg gs ih =>
    have hgg_nl : gg.nl = false := by
      cases h : gg.nl
      · rfl
      · simp [List.countP_cons, h] at hnl0
    have hgs_nl : gs.countP GenGate.nl = 0 := by
      simpa [List.countP_cons, hgg_nl] using hnl0
    have hgg_aff : ∃ (a : α → Bool) (b : β → Bool),
        ∀ u v, gg.eval u v (init u v) = xor (a u) (b v) := by
      cases gg with
      | pureU f => exact ⟨f, fun _ => false, fun u v => by simp [GenGate.eval]⟩
      | pureV g => exact ⟨fun _ => false, g, fun u v => by simp [GenGate.eval]⟩
      | real g =>
        have hgl : g.inputs.length ≤ 2 := hfan (GenGate.real g) (List.mem_cons_self ..)
        have hwire : ∀ i : ℕ, ∃ (a : α → Bool) (b : β → Bool),
            ∀ u v, (init u v).getD i false = xor (a u) (b v) := by
          intro i
          by_cases hi : i < n0
          · exact hinit i hi
          · refine ⟨fun _ => false, fun _ => false, fun u v => ?_⟩
            have hge : (init u v).length ≤ i := by rw [hlen u v]; omega
            simp [List.getD, List.getElem?_eq_none hge]
        match hlist : g.inputs with
        | [] =>
          refine ⟨fun _ => g.op.eval [], fun _ => false, fun u v => ?_⟩
          simp [GenGate.eval, hlist]
        | [i1] =>
          obtain ⟨a1, b1, h1⟩ := hwire i1
          obtain ⟨c0, c1, hf⟩ := affine_gate_1 (fun x => g.op.eval [x])
          refine ⟨fun u => xor c0 (c1 && a1 u), fun v => c1 && b1 v, fun u v => ?_⟩
          simp only [GenGate.eval, hlist, List.map_cons, List.map_nil, h1 u v, hf]
          cases c0 <;> cases c1 <;> cases a1 u <;> cases b1 v <;> rfl
        | [i1, i2] =>
          have hlin : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
              (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
            simpa [GenGate.nl, nonlinear, hlist] using hgg_nl
          obtain ⟨a1, b1, h1⟩ := hwire i1
          obtain ⟨a2, b2, h2⟩ := hwire i2
          obtain ⟨c0, c1, c2, hf⟩ := affine_gate_2 (fun x y => g.op.eval [x, y]) hlin
          refine ⟨fun u => xor c0 (xor (c1 && a1 u) (c2 && a2 u)),
            fun v => xor (c1 && b1 v) (c2 && b2 v), fun u v => ?_⟩
          simp only [GenGate.eval, hlist, List.map_cons, List.map_nil, h1 u v, h2 u v, hf]
          cases c0 <;> cases c1 <;> cases c2 <;>
            cases a1 u <;> cases b1 v <;> cases a2 u <;> cases b2 v <;> rfl
        | _ :: _ :: _ :: _ =>
          simp [hlist] at hgl
    obtain ⟨a0, b0, h0⟩ := hgg_aff
    let init' : α → β → List Bool := fun u v => init u v ++ [gg.eval u v (init u v)]
    have hlen' : ∀ u v, (init' u v).length = n0 + 1 := fun u v => by
      simp [init', hlen u v]
    have hinit' : ∀ i < n0 + 1, ∃ (a : α → Bool) (b : β → Bool),
        ∀ u v, (init' u v).getD i false = xor (a u) (b v) := by
      intro i hi
      by_cases hlt : i < n0
      · obtain ⟨a, b, hab⟩ := hinit i hlt
        refine ⟨a, b, fun u v => ?_⟩
        have hlt' : i < (init u v).length := by rw [hlen u v]; exact hlt
        simp only [init', List.getD, List.getElem?_append_left hlt']
        exact hab u v
      · have heq : i = n0 := by omega
        subst heq
        refine ⟨a0, b0, fun u v => ?_⟩
        simp only [init', List.getD, ← hlen u v, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        exact h0 u v
    have hfan' : GenFanIn2 gs := fun g hg => hfan g (List.mem_cons_of_mem _ hg)
    have hres := ih (n0 + 1) init' hlen' hinit' hfan' hgs_nl
    intro i
    simpa [evalGen, List.foldl_cons, init'] using hres i

inductive HasNL : ℕ → {α β : Type} → (α → β → Bool) → Prop
  | zero {α β : Type} (a : α → Bool) (b : β → Bool) :
      HasNL 0 (fun u v => xor (a u) (b v))
  | step {t : ℕ} {α β : Type} (G : α → β → Bool)
      (a1 a2 : α → Bool) (b1 b2 : β → Bool)
      (F0 F1 : α → β → Bool) :
      HasNL t F0 → HasNL t F1 →
      (∀ u v, G u v = if (xor (a1 u) (b1 v) && xor (a2 u) (b2 v)) then F1 u v else F0 u v) →
      (∀ p q : Bool, HasNL t (fun (u : {u : α // a1 u = p ∧ a2 u = q}) (v : β) => G u.1 v)) →
      (∀ r s : Bool, HasNL t (fun (u : α) (v : {v : β // b1 v = r ∧ b2 v = s}) => G u v.1)) →
      HasNL (t + 1) G

lemma hasNL_congr {t : ℕ} {α β : Type} {G1 G2 : α → β → Bool}
    (h : HasNL t G1) (heq : ∀ u v, G1 u v = G2 u v) : HasNL t G2 := by
  have hfun : G1 = G2 := funext (fun u => funext (fun v => heq u v))
  rwa [← hfun]

lemma hasNL_comap {t : ℕ} {α β α' β' : Type} {G : α → β → Bool}
    (h : HasNL t G) (f : α' → α) (g : β' → β) :
    HasNL t (fun u v => G (f u) (g v)) := by
  induction h generalizing α' β' with
  | zero a b =>
    exact HasNL.zero (fun u => a (f u)) (fun v => b (g v))
  | step G a1 a2 b1 b2 F0 F1 hF0 hF1 hEq hU hV ihF0 ihF1 ihU ihV =>
    refine HasNL.step (fun u v => G (f u) (g v))
      (fun u => a1 (f u)) (fun u => a2 (f u))
      (fun v => b1 (g v)) (fun v => b2 (g v))
      (fun u v => F0 (f u) (g v)) (fun u v => F1 (f u) (g v))
      (ihF0 f g) (ihF1 f g) (fun u v => hEq (f u) (g v)) ?_ ?_
    · intro p q
      exact ihU p q (fun (u : {u : α' // a1 (f u) = p ∧ a2 (f u) = q}) => ⟨f u.1, u.2⟩) g
    · intro r s
      exact ihV r s f (fun (v : {v : β' // b1 (g v) = r ∧ b2 (g v) = s}) => ⟨g v.1, v.2⟩)

lemma hasNL_succ {t : ℕ} {α β : Type} {G : α → β → Bool} (h : HasNL t G) :
    HasNL (t + 1) G := by
  refine HasNL.step G (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
    G G h h (fun u v => by simp) ?_ ?_
  · intro p q
    exact hasNL_comap h Subtype.val id
  · intro r s
    exact hasNL_comap h id Subtype.val

lemma hasNL_mono {t1 t2 : ℕ} {α β : Type} {G : α → β → Bool}
    (hle : t1 ≤ t2) (h : HasNL t1 G) : HasNL t2 G := by
  induction hle with
  | refl => exact h
  | step _ ih => exact hasNL_succ ih

lemma list_split_first_countP {γ : Type} (p : γ → Bool) :
    ∀ (l : List γ), 0 < l.countP p →
      ∃ (pref suff : List γ) (x : γ),
        l = pref ++ x :: suff ∧ pref.countP p = 0 ∧ p x = true ∧
        suff.countP p + 1 = l.countP p := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hpos
    cases hpa : p a
    · have hpos' : 0 < l.countP p := by
        simp only [List.countP_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hpos
        exact hpos
      obtain ⟨pref, suff, x, hl, hpref, hx, hsuff⟩ := ih hpos'
      refine ⟨a :: pref, suff, x, by simp [hl], by simp [List.countP_cons, hpa, hpref], hx, ?_⟩
      simp [List.countP_cons, hpa, hsuff]
    · refine ⟨[], l, a, rfl, rfl, hpa, ?_⟩
      simp [List.countP_cons, hpa]

lemma evalGen_hasNL :
    ∀ (t : ℕ) {α β : Type} (gs : List (GenGate α β)) (n0 : ℕ)
      (init : α → β → List Bool)
      (hlen : ∀ u v, (init u v).length = n0)
      (hinit : ∀ i < n0, ∃ (a : α → Bool) (b : β → Bool),
        ∀ u v, (init u v).getD i false = xor (a u) (b v))
      (hfan : GenFanIn2 gs) (hcnt : gs.countP GenGate.nl ≤ t) (out : ℕ),
      HasNL t (fun u v => (evalGen gs (init u v) u v).getD out false) := by
  intro t
  induction t with
  | zero =>
    intro α β gs n0 init hlen hinit hfan hcnt out
    have h0 : gs.countP GenGate.nl = 0 := Nat.eq_zero_of_le_zero hcnt
    obtain ⟨a, b, hab⟩ := evalGen_zero_affine gs n0 init hlen hinit hfan h0 out
    exact hasNL_congr (HasNL.zero a b) (fun u v => (hab u v).symm)
  | succ t ih =>
    intro α β gs n0 init hlen hinit hfan hcnt out
    by_cases h0 : gs.countP GenGate.nl = 0
    · obtain ⟨a, b, hab⟩ := evalGen_zero_affine gs n0 init hlen hinit hfan h0 out
      exact hasNL_mono (Nat.zero_le _) (hasNL_congr (HasNL.zero a b) (fun u v => (hab u v).symm))
    · have hpos : 0 < gs.countP GenGate.nl := Nat.pos_of_ne_zero h0
      obtain ⟨pref, suff, gg, hgs_eq, hpref0, hgg_nl, hsuff_cnt⟩ :=
        list_split_first_countP GenGate.nl gs hpos
      have hsuff_le : suff.countP GenGate.nl ≤ t := by omega
      cases gg with
      | pureU _ => simp [GenGate.nl] at hgg_nl
      | pureV _ => simp [GenGate.nl] at hgg_nl
      | real g1 =>
        have hlen2 : g1.inputs.length = 2 := by
          simp only [GenGate.nl, nonlinear, Bool.and_eq_true, beq_iff_eq] at hgg_nl
          exact hgg_nl.1
        have hnl1 : xor (xor (g1.op.eval [false, false]) (g1.op.eval [false, true]))
            (xor (g1.op.eval [true, false]) (g1.op.eval [true, true])) = true := by
          simp only [GenGate.nl, nonlinear, Bool.and_eq_true] at hgg_nl
          exact hgg_nl.2
        match hlist : g1.inputs with
        | [i1, i2] =>
          have hfan_pref : GenFanIn2 pref := fun g hg =>
            hfan g (by rw [hgs_eq]; exact List.mem_append_left _ hg)
          have hfan_suff : GenFanIn2 suff := fun g hg =>
            hfan g (by rw [hgs_eq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
          have hpref_aff := evalGen_zero_affine pref n0 init hlen hinit hfan_pref hpref0
          obtain ⟨a1, b1, hi1⟩ := hpref_aff i1
          obtain ⟨a2, b2, hi2⟩ := hpref_aff i2
          obtain ⟨c0, c1, c2, hf⟩ := nonlinear_gate_2 (fun x y => g1.op.eval [x, y]) hnl1
          let a1' : α → Bool := fun u => xor (a1 u) c1
          let a2' : α → Bool := fun u => xor (a2 u) c2
          have hg1_val : ∀ u v,
              (GenGate.real g1 : GenGate α β).eval u v (evalGen pref (init u v) u v) =
                xor c0 ((xor (a1' u) (b1 v)) && (xor (a2' u) (b2 v))) := by
            intro u v
            simp only [GenGate.eval, hlist, List.map_cons, List.map_nil, hi1 u v, hi2 u v, hf, a1', a2']
            cases c0 <;> cases c1 <;> cases c2 <;>
              cases a1 u <;> cases b1 v <;> cases a2 u <;> cases b2 v <;> rfl
          let gs0 : List (GenGate α β) := pref ++ GenGate.pureU (fun _ => c0) :: suff
          let gs1 : List (GenGate α β) := pref ++ GenGate.pureU (fun _ => !c0) :: suff
          have hfan0 : GenFanIn2 gs0 := by
            intro g hg
            simp only [gs0, List.mem_append, List.mem_cons] at hg
            rcases hg with h1 | rfl | h2
            · exact hfan_pref g h1
            · trivial
            · exact hfan_suff g h2
          have hfan1 : GenFanIn2 gs1 := by
            intro g hg
            simp only [gs1, List.mem_append, List.mem_cons] at hg
            rcases hg with h1 | rfl | h2
            · exact hfan_pref g h1
            · trivial
            · exact hfan_suff g h2
          have hcnt0 : gs0.countP GenGate.nl ≤ t := by
            simp [gs0, List.countP_append, List.countP_cons, GenGate.nl, hpref0]; omega
          have hcnt1 : gs1.countP GenGate.nl ≤ t := by
            simp [gs1, List.countP_append, List.countP_cons, GenGate.nl, hpref0]; omega
          have hF0 := ih gs0 n0 init hlen hinit hfan0 hcnt0 out
          have hF1 := ih gs1 n0 init hlen hinit hfan1 hcnt1 out
          have hEq : ∀ u v,
              (evalGen gs (init u v) u v).getD out false =
                if (xor (a1' u) (b1 v) && xor (a2' u) (b2 v))
                then (evalGen gs1 (init u v) u v).getD out false
                else (evalGen gs0 (init u v) u v).getD out false := by
            intro u v
            rw [hgs_eq, evalGen_append, evalGen_cons]
            dsimp only [gs0, gs1]
            rw [evalGen_append, evalGen_cons, evalGen_append, evalGen_cons, hg1_val u v]
            cases hcond : (xor (a1' u) (b1 v) && xor (a2' u) (b2 v)) <;>
              simp [GenGate.eval]
          refine HasNL.step (fun u v => (evalGen gs (init u v) u v).getD out false)
            a1' a2' b1 b2
            (fun u v => (evalGen gs0 (init u v) u v).getD out false)
            (fun u v => (evalGen gs1 (init u v) u v).getD out false)
            hF0 hF1 hEq ?_ ?_
          · intro p q
            let α' := {u : α // a1' u = p ∧ a2' u = q}
            let liftG : GenGate α β → GenGate α' β
              | GenGate.pureU f => GenGate.pureU (fun u => f u.1)
              | GenGate.pureV g => GenGate.pureV g
              | GenGate.real g => GenGate.real g
            let gsU : List (GenGate α' β) :=
              pref.map liftG ++
                GenGate.pureV (fun v => xor c0 ((xor p (b1 v)) && (xor q (b2 v)))) ::
                suff.map liftG
            have hcomp : GenGate.nl ∘ liftG = GenGate.nl :=
              funext (fun gg => by cases gg <;> rfl)
            have hcntU : gsU.countP GenGate.nl ≤ t := by
              have hp : (pref.map liftG).countP GenGate.nl = pref.countP GenGate.nl := by
                rw [List.countP_map, hcomp]
              have hs : (suff.map liftG).countP GenGate.nl = suff.countP GenGate.nl := by
                rw [List.countP_map, hcomp]
              simp [gsU, List.countP_append, List.countP_cons, GenGate.nl, hp, hs, hpref0]
              omega
            have hfanU : GenFanIn2 gsU := by
              intro g hg
              simp only [gsU, List.mem_append, List.mem_cons, List.mem_map] at hg
              rcases hg with ⟨gg, hgg, rfl⟩ | rfl | ⟨gg, hgg, rfl⟩
              · cases gg with
                | pureU _ => trivial
                | pureV _ => trivial
                | real g => exact hfan_pref (GenGate.real g) hgg
              · trivial
              · cases gg with
                | pureU _ => trivial
                | pureV _ => trivial
                | real g => exact hfan_suff (GenGate.real g) hgg
            have heval_map : ∀ (l : List (GenGate α β)) (w : List Bool) (u : α') (v : β),
                evalGen (l.map liftG) w u v = evalGen l w u.1 v := by
              intro l
              induction l with
              | nil => intros; rfl
              | cons g l ihl =>
                intro w u v
                simp only [List.map_cons, evalGen, List.foldl_cons]
                have hg : (liftG g).eval u v w = g.eval u.1 v w := by
                  cases g <;> rfl
                rw [hg]
                exact ihl _ u v
            have hU := ih gsU n0 (fun u v => init u.1 v) (fun u v => hlen u.1 v)
              (fun i hi => by
                obtain ⟨a, b, hab⟩ := hinit i hi
                exact ⟨fun u => a u.1, b, fun u v => hab u.1 v⟩)
              hfanU hcntU out
            apply hasNL_congr hU
            intro u v
            rw [hgs_eq, evalGen_append, evalGen_cons]
            rw [evalGen_append, evalGen_cons, heval_map pref]
            have heq1 : (GenGate.pureV (fun v => xor c0 ((xor p (b1 v)) && (xor q (b2 v)))) :
                GenGate α' β).eval u v (evalGen pref (init u.1 v) u.1 v) =
                (GenGate.real g1 : GenGate α β).eval u.1 v (evalGen pref (init u.1 v) u.1 v) := by
              rw [hg1_val u.1 v, u.2.1, u.2.2]
              rfl
            rw [heq1, heval_map suff]
          · intro r s
            let β' := {v : β // b1 v = r ∧ b2 v = s}
            let liftG : GenGate α β → GenGate α β'
              | GenGate.pureU f => GenGate.pureU f
              | GenGate.pureV g => GenGate.pureV (fun v => g v.1)
              | GenGate.real g => GenGate.real g
            let gsV : List (GenGate α β') :=
              pref.map liftG ++
                GenGate.pureU (fun u => xor c0 ((xor (a1' u) r) && (xor (a2' u) s))) ::
                suff.map liftG
            have hcomp : GenGate.nl ∘ liftG = GenGate.nl :=
              funext (fun gg => by cases gg <;> rfl)
            have hcntV : gsV.countP GenGate.nl ≤ t := by
              have hp : (pref.map liftG).countP GenGate.nl = pref.countP GenGate.nl := by
                rw [List.countP_map, hcomp]
              have hs : (suff.map liftG).countP GenGate.nl = suff.countP GenGate.nl := by
                rw [List.countP_map, hcomp]
              simp [gsV, List.countP_append, List.countP_cons, GenGate.nl, hp, hs, hpref0]
              omega
            have hfanV : GenFanIn2 gsV := by
              intro g hg
              simp only [gsV, List.mem_append, List.mem_cons, List.mem_map] at hg
              rcases hg with ⟨gg, hgg, rfl⟩ | rfl | ⟨gg, hgg, rfl⟩
              · cases gg with
                | pureU _ => trivial
                | pureV _ => trivial
                | real g => exact hfan_pref (GenGate.real g) hgg
              · trivial
              · cases gg with
                | pureU _ => trivial
                | pureV _ => trivial
                | real g => exact hfan_suff (GenGate.real g) hgg
            have heval_map : ∀ (l : List (GenGate α β)) (w : List Bool) (u : α) (v : β'),
                evalGen (l.map liftG) w u v = evalGen l w u v.1 := by
              intro l
              induction l with
              | nil => intros; rfl
              | cons g l ihl =>
                intro w u v
                simp only [List.map_cons, evalGen, List.foldl_cons]
                have hg : (liftG g).eval u v w = g.eval u v.1 w := by
                  cases g <;> rfl
                rw [hg]
                exact ihl _ u v
            have hV := ih gsV n0 (fun u v => init u v.1) (fun u v => hlen u v.1)
              (fun i hi => by
                obtain ⟨a, b, hab⟩ := hinit i hi
                exact ⟨a, fun v => b v.1, fun u v => hab u v.1⟩)
              hfanV hcntV out
            apply hasNL_congr hV
            intro u v
            rw [hgs_eq, evalGen_append, evalGen_cons]
            rw [evalGen_append, evalGen_cons, heval_map pref]
            have heq1 : (GenGate.pureU (fun u => xor c0 ((xor (a1' u) r) && (xor (a2' u) s))) :
                GenGate α β').eval u v (evalGen pref (init u v.1) u v.1) =
                (GenGate.real g1 : GenGate α β).eval u v.1 (evalGen pref (init u v.1) u v.1) := by
              rw [hg1_val u v.1, v.2.1, v.2.2]
              rfl
            rw [heq1, heval_map suff]
        | [] => simp [hlist] at hlen2
        | [_] => simp [hlist] at hlen2
        | _ :: _ :: _ :: _ => simp [hlist] at hlen2

lemma circuit_hasNL {n m t : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrep : Represents G C)
    (hcnt : C.gates.countP nonlinear ≤ t) :
    HasNL t G := by
  let gs : List (GenGate (Fin n) (Fin m)) := C.gates.map GenGate.real
  have heval : ∀ (l : List Gate) (w : List Bool) (u : Fin n) (v : Fin m),
      evalGen (l.map GenGate.real) w u v =
        l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons g l ihl =>
      intro w u v
      simp only [List.map_cons, evalGen, List.foldl_cons, GenGate.eval]
      exact ihl _ u v
  have hlen : ∀ (u : Fin n) (v : Fin m), (oneEach u v).length = n + m := fun u v => by
    simp [oneEach]
  have hinit : ∀ i < n + m, ∃ (a : Fin n → Bool) (b : Fin m → Bool),
      ∀ u v, (oneEach u v).getD i false = xor (a u) (b v) := by
    intro i hi
    by_cases hlt : i < n
    · refine ⟨fun u => decide (⟨i, hlt⟩ = u), fun _ => false, fun u v => ?_⟩
      have hlenL : (List.ofFn (fun x : Fin n => decide (x = u))).length = n := by simp
      simp only [oneEach, List.getD, List.getElem?_append_left (by omega : i < (List.ofFn (fun x : Fin n => decide (x = u))).length),
        List.getElem?_ofFn, hlt, dite_true, Option.getD_some, Bool.xor_false]
    · have hge : n ≤ i := by omega
      have hlt2 : i - n < m := by omega
      refine ⟨fun _ => false, fun v => decide (⟨i - n, hlt2⟩ = v), fun u v => ?_⟩
      have hlenL : (List.ofFn (fun x : Fin n => decide (x = u))).length = n := by simp
      simp only [oneEach, List.getD, List.getElem?_append_right (by omega : (List.ofFn (fun x : Fin n => decide (x = u))).length ≤ i),
        hlenL, List.getElem?_ofFn, hlt2, dite_true, Option.getD_some, Bool.false_xor]
  have hfanG : GenFanIn2 gs := by
    intro gg hgg
    rcases List.mem_map.mp hgg with ⟨g, hg, rfl⟩
    exact hfan g hg
  have hcntG : gs.countP GenGate.nl ≤ t := by
    have : gs.countP GenGate.nl = C.gates.countP nonlinear := by
      simp [gs, List.countP_map]; rfl
    omega
  have hres := evalGen_hasNL t gs (n + m) oneEach hlen hinit hfanG hcntG C.output
  apply hasNL_congr hres
  intro u v
  rw [heval C.gates (oneEach u v) u v]
  exact hrep u v

lemma hasNL_row_tag {t : ℕ} {α β : Type} {G : α → β → Bool} (h : HasNL t G) :
    ∃ tag : α → Fin (4 ^ t),
      ∀ u1 u2, tag u1 = tag u2 → ∃ c : Bool, ∀ v, G u1 v = xor (G u2 v) c := by
  induction h with
  | zero a b =>
    refine ⟨fun _ => ⟨0, by simp⟩, fun u1 u2 _ => ⟨xor (a u1) (a u2), fun v => ?_⟩⟩
    dsimp only
    cases a u1 <;> cases a u2 <;> cases b v <;> rfl
  | @step t α β G a1 a2 b1 b2 F0 F1 _ _ _ _ _ _ _ ihU _ =>
    choose tagU htagU using ihU
    let pairIdx : Bool → Bool → ℕ := fun p q => (if p then 2 else 0) + (if q then 1 else 0)
    have hpair_lt : ∀ p q, pairIdx p q < 4 := by
      intro p q; cases p <;> cases q <;> decide
    have hpair_inj : ∀ p1 q1 p2 q2, pairIdx p1 q1 = pairIdx p2 q2 → p1 = p2 ∧ q1 = q2 := by
      intro p1 q1 p2 q2 h
      cases p1 <;> cases q1 <;> cases p2 <;> cases q2 <;> simp [pairIdx] at h ⊢
    refine ⟨fun u => ⟨pairIdx (a1 u) (a2 u) * 4 ^ t + (tagU (a1 u) (a2 u) ⟨u, rfl, rfl⟩).val, ?_⟩, ?_⟩
    · have h1 := hpair_lt (a1 u) (a2 u)
      have h2 := (tagU (a1 u) (a2 u) ⟨u, rfl, rfl⟩).isLt
      have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := by ring
      rw [hpow]
      have h3 : pairIdx (a1 u) (a2 u) * 4 ^ t + 4 ^ t ≤ 4 * 4 ^ t := by
        have : (pairIdx (a1 u) (a2 u) + 1) * 4 ^ t ≤ 4 * 4 ^ t :=
          Nat.mul_le_mul_right _ (by omega)
        linarith
      omega
    · intro u1 u2 heq
      have hval : pairIdx (a1 u1) (a2 u1) * 4 ^ t + (tagU (a1 u1) (a2 u1) ⟨u1, rfl, rfl⟩).val =
          pairIdx (a1 u2) (a2 u2) * 4 ^ t + (tagU (a1 u2) (a2 u2) ⟨u2, rfl, rfl⟩).val :=
        congrArg Fin.val heq
      have hlt1 := (tagU (a1 u1) (a2 u1) ⟨u1, rfl, rfl⟩).isLt
      have hlt2 := (tagU (a1 u2) (a2 u2) ⟨u2, rfl, rfl⟩).isLt
      have hpos : 0 < 4 ^ t := Nat.pow_pos (by omega)
      have hdiv1 : (pairIdx (a1 u1) (a2 u1) * 4 ^ t + (tagU (a1 u1) (a2 u1) ⟨u1, rfl, rfl⟩).val) / 4 ^ t =
          pairIdx (a1 u1) (a2 u1) := by
        rw [Nat.mul_comm (pairIdx _ _), Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt1, Nat.add_zero]
      have hdiv2 : (pairIdx (a1 u2) (a2 u2) * 4 ^ t + (tagU (a1 u2) (a2 u2) ⟨u2, rfl, rfl⟩).val) / 4 ^ t =
          pairIdx (a1 u2) (a2 u2) := by
        rw [Nat.mul_comm (pairIdx _ _), Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt2, Nat.add_zero]
      have hpq_eq : pairIdx (a1 u1) (a2 u1) = pairIdx (a1 u2) (a2 u2) := by
        rw [← hdiv1, hval, hdiv2]
      obtain ⟨ha1, ha2⟩ := hpair_inj _ _ _ _ hpq_eq
      have hcast : ∀ (p' q' : Bool) (hp' : a1 u2 = p') (hq' : a2 u2 = q'),
          (tagU p' q' ⟨u2, hp', hq'⟩).val = (tagU (a1 u2) (a2 u2) ⟨u2, rfl, rfl⟩).val := by
        intro p' q' hp' hq'; subst hp'; subst hq'; rfl
      have hsub : tagU (a1 u1) (a2 u1) ⟨u1, rfl, rfl⟩ = tagU (a1 u1) (a2 u1) ⟨u2, ha1.symm, ha2.symm⟩ := by
        apply Fin.ext
        rw [hcast (a1 u1) (a2 u1) ha1.symm ha2.symm]
        rw [hpq_eq] at hval
        omega
      exact htagU (a1 u1) (a2 u1) ⟨u1, rfl, rfl⟩ ⟨u2, ha1.symm, ha2.symm⟩ hsub

lemma hasNL_col_tag {t : ℕ} {α β : Type} {G : α → β → Bool} (h : HasNL t G) :
    ∃ tag : β → Fin (4 ^ t),
      ∀ v1 v2, tag v1 = tag v2 → ∃ c : Bool, ∀ u, G u v1 = xor (G u v2) c := by
  induction h with
  | zero a b =>
    refine ⟨fun _ => ⟨0, by simp⟩, fun v1 v2 _ => ⟨xor (b v1) (b v2), fun u => ?_⟩⟩
    dsimp only
    cases a u <;> cases b v1 <;> cases b v2 <;> rfl
  | @step t α β G a1 a2 b1 b2 F0 F1 _ _ _ _ _ _ _ _ ihV =>
    choose tagV htagV using ihV
    let pairIdx : Bool → Bool → ℕ := fun r s => (if r then 2 else 0) + (if s then 1 else 0)
    have hpair_lt : ∀ r s, pairIdx r s < 4 := by
      intro r s; cases r <;> cases s <;> decide
    have hpair_inj : ∀ r1 s1 r2 s2, pairIdx r1 s1 = pairIdx r2 s2 → r1 = r2 ∧ s1 = s2 := by
      intro r1 s1 r2 s2 h
      cases r1 <;> cases s1 <;> cases r2 <;> cases s2 <;> simp [pairIdx] at h ⊢
    refine ⟨fun v => ⟨pairIdx (b1 v) (b2 v) * 4 ^ t + (tagV (b1 v) (b2 v) ⟨v, rfl, rfl⟩).val, ?_⟩, ?_⟩
    · have h1 := hpair_lt (b1 v) (b2 v)
      have h2 := (tagV (b1 v) (b2 v) ⟨v, rfl, rfl⟩).isLt
      have hpow : 4 ^ (t + 1) = 4 * 4 ^ t := by ring
      rw [hpow]
      have h3 : pairIdx (b1 v) (b2 v) * 4 ^ t + 4 ^ t ≤ 4 * 4 ^ t := by
        have : (pairIdx (b1 v) (b2 v) + 1) * 4 ^ t ≤ 4 * 4 ^ t :=
          Nat.mul_le_mul_right _ (by omega)
        linarith
      omega
    · intro v1 v2 heq
      have hval : pairIdx (b1 v1) (b2 v1) * 4 ^ t + (tagV (b1 v1) (b2 v1) ⟨v1, rfl, rfl⟩).val =
          pairIdx (b1 v2) (b2 v2) * 4 ^ t + (tagV (b1 v2) (b2 v2) ⟨v2, rfl, rfl⟩).val :=
        congrArg Fin.val heq
      have hlt1 := (tagV (b1 v1) (b2 v1) ⟨v1, rfl, rfl⟩).isLt
      have hlt2 := (tagV (b1 v2) (b2 v2) ⟨v2, rfl, rfl⟩).isLt
      have hpos : 0 < 4 ^ t := Nat.pow_pos (by omega)
      have hdiv1 : (pairIdx (b1 v1) (b2 v1) * 4 ^ t + (tagV (b1 v1) (b2 v1) ⟨v1, rfl, rfl⟩).val) / 4 ^ t =
          pairIdx (b1 v1) (b2 v1) := by
        rw [Nat.mul_comm (pairIdx _ _), Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt1, Nat.add_zero]
      have hdiv2 : (pairIdx (b1 v2) (b2 v2) * 4 ^ t + (tagV (b1 v2) (b2 v2) ⟨v2, rfl, rfl⟩).val) / 4 ^ t =
          pairIdx (b1 v2) (b2 v2) := by
        rw [Nat.mul_comm (pairIdx _ _), Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt2, Nat.add_zero]
      have hrs_eq : pairIdx (b1 v1) (b2 v1) = pairIdx (b1 v2) (b2 v2) := by
        rw [← hdiv1, hval, hdiv2]
      obtain ⟨hb1, hb2⟩ := hpair_inj _ _ _ _ hrs_eq
      have hcast : ∀ (r' s' : Bool) (hr' : b1 v2 = r') (hs' : b2 v2 = s'),
          (tagV r' s' ⟨v2, hr', hs'⟩).val = (tagV (b1 v2) (b2 v2) ⟨v2, rfl, rfl⟩).val := by
        intro r' s' hr' hs'; subst hr'; subst hs'; rfl
      have hsub : tagV (b1 v1) (b2 v1) ⟨v1, rfl, rfl⟩ = tagV (b1 v1) (b2 v1) ⟨v2, hb1.symm, hb2.symm⟩ := by
        apply Fin.ext
        rw [hcast (b1 v1) (b2 v1) hb1.symm hb2.symm]
        rw [hrs_eq] at hval
        omega
      exact htagV (b1 v1) (b2 v1) ⟨v1, rfl, rfl⟩ ⟨v2, hb1.symm, hb2.symm⟩ hsub

lemma hadamard_card_le {t : ℕ} {α β : Type} [Fintype α] [Fintype β]
    {G : α → β → Bool} (hβ : 0 < Fintype.card β)
    (hH : IsHadamard G) (hNL : HasNL t G) :
    Fintype.card α ≤ 4 ^ t := by
  obtain ⟨tag, htag⟩ := hasNL_row_tag hNL
  have hinj : Function.Injective tag := by
    intro u1 u2 heq
    by_contra hne
    obtain ⟨c, hc⟩ := htag u1 u2 heq
    have hsum : ∑ v : β, signZ (xor (G u1 v) (G u2 v)) = (Fintype.card β : ℤ) * signZ c := by
      have hterm : ∀ v : β, signZ (xor (G u1 v) (G u2 v)) = signZ c := fun v => by
        rw [hc v]
        cases G u2 v <;> cases c <;> rfl
      simp [hterm]
    have hz := hH u1 u2 hne
    rw [hsum] at hz
    have hsc : signZ c ≠ 0 := by cases c <;> decide
    have hcard0 : (Fintype.card β : ℤ) = 0 := (mul_eq_zero.mp hz).resolve_right hsc
    omega
  have := Fintype.card_le_of_injective tag hinj
  simpa using this

def IsSignedIP (s : ℕ) (G : Fin (4 ^ s) → Fin (4 ^ s) → Bool) : Prop :=
  ∃ (α β : Fin (4 ^ s) → Bool) (φ ψ : Fin (4 ^ s) → Fin (2 * s) → Bool),
    ∀ u v, G u v = z2b (b2z (α u) + b2z (β v) + ∑ i : Fin (2 * s), b2z (φ u i) * b2z (ψ v i))

lemma block_card_eq_of_le {N M : ℕ} (hNM : N = 4 * M)
    (f1 f2 : Fin N → Bool)
    (hle : ∀ p q : Bool, ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = p ∧ f2 x = q)).card ≤ M) :
    ∀ p q : Bool, ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = p ∧ f2 x = q)).card = M := by
  let S : Bool → Bool → Finset (Fin N) := fun p q =>
    (Finset.univ : Finset (Fin N)).filter (fun x => f1 x = p ∧ f2 x = q)
  have hsum : (S false false).card + (S false true).card + (S true false).card + (S true true).card = N := by
    have h1 : S false false ∪ S false true = (Finset.univ : Finset (Fin N)).filter (fun x => f1 x = false) := by
      ext x; simp [S]; cases f2 x <;> simp
    have h2 : S true false ∪ S true true = (Finset.univ : Finset (Fin N)).filter (fun x => f1 x = true) := by
      ext x; simp [S]; cases f2 x <;> simp
    have hd1 : Disjoint (S false false) (S false true) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      rw [hx1.2] at hx2; exact Bool.false_ne_true hx2.2
    have hd2 : Disjoint (S true false) (S true true) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      rw [hx1.2] at hx2; exact Bool.false_ne_true hx2.2
    have hd3 : Disjoint ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = false))
        ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = true)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      rw [h1] at h2
      cases h2
    have hun : ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = false)) ∪
        ((Finset.univ : Finset (Fin N)).filter (fun x => f1 x = true)) = Finset.univ := by
      ext x; simp
    have hc1 := Finset.card_union_of_disjoint hd1
    have hc2 := Finset.card_union_of_disjoint hd2
    have hc3 := Finset.card_union_of_disjoint hd3
    rw [h1] at hc1
    rw [h2] at hc2
    rw [hun, Finset.card_univ, Fintype.card_fin] at hc3
    omega
  have h00 : (S false false).card ≤ M := hle false false
  have h01 : (S false true).card ≤ M := hle false true
  have h10 : (S true false).card ≤ M := hle true false
  have h11 : (S true true).card ≤ M := hle true true
  intro p q
  change (S p q).card = M
  cases p <;> cases q <;> omega

lemma xor_and_eq_true_iff (x1 x2 y1 y2 : Bool) :
    (xor x1 y1 && xor x2 y2) = true ↔ x1 = !y1 ∧ x2 = !y2 := by
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> decide

lemma classification :
    ∀ (s : ℕ) (G : Fin (4 ^ s) → Fin (4 ^ s) → Bool),
      IsHadamard G → HasNL s G → IsSignedIP s G := by
  intro s
  induction s with
  | zero =>
    intro G _ _
    refine ⟨fun _ => G ⟨0, by decide⟩ ⟨0, by decide⟩, fun _ => false,
      fun _ i => Fin.elim0 i, fun _ i => Fin.elim0 i, fun u v => ?_⟩
    have hu : u = ⟨0, by decide⟩ := Fin.ext (by have := u.isLt; simp at this; omega)
    have hv : v = ⟨0, by decide⟩ := Fin.ext (by have := v.isLt; simp at this; omega)
    subst hu; subst hv
    simp only [Nat.mul_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [show b2z false = 0 from rfl, add_zero, z2b_b2z]
  | succ s ih =>
    intro G hH hNL
    classical
    cases hNL with
    | step _ a1 a2 b1 b2 F0 F1 hF0 hF1 hEq hU hV =>
      have hNpos : 0 < 4 ^ (s + 1) := Nat.pow_pos (by omega)
      have hMpos : 0 < 4 ^ s := Nat.pow_pos (by omega)
      have hMposZ : (0 : ℤ) < (4 : ℤ) ^ s := by positivity
      have hNM : 4 ^ (s + 1) = 4 * 4 ^ s := by ring
      have hHt : IsHadamard (fun v u => G u v) := hadamard_transpose hNpos hH
      let U : Bool → Bool → Finset (Fin (4 ^ (s + 1))) := fun p q =>
        (Finset.univ : Finset (Fin (4 ^ (s + 1)))).filter (fun u => a1 u = p ∧ a2 u = q)
      let V : Bool → Bool → Finset (Fin (4 ^ (s + 1))) := fun r t =>
        (Finset.univ : Finset (Fin (4 ^ (s + 1)))).filter (fun v => b1 v = r ∧ b2 v = t)
      have hU_le : ∀ p q, (U p q).card ≤ 4 ^ s := by
        intro p q
        have hHu : IsHadamard (fun (u : {u : Fin (4 ^ (s + 1)) // a1 u = p ∧ a2 u = q})
            (v : Fin (4 ^ (s + 1))) => G u.1 v) := by
          intro u1 u2 hne
          exact hH u1.1 u2.1 (fun h => hne (Subtype.ext h))
        have hle := hadamard_card_le (by simp [hNpos]) hHu (hU p q)
        have hcard : Fintype.card {u : Fin (4 ^ (s + 1)) // a1 u = p ∧ a2 u = q} = (U p q).card := by
          rw [Fintype.card_subtype]
        omega
      have hV_le : ∀ r t, (V r t).card ≤ 4 ^ s := by
        intro r t
        have hHv : IsHadamard (fun (v : {v : Fin (4 ^ (s + 1)) // b1 v = r ∧ b2 v = t})
            (u : Fin (4 ^ (s + 1))) => G u v.1) := by
          intro v1 v2 hne
          exact hHt v1.1 v2.1 (fun h => hne (Subtype.ext h))
        have hNLt : HasNL s (fun (v : {v : Fin (4 ^ (s + 1)) // b1 v = r ∧ b2 v = t})
            (u : Fin (4 ^ (s + 1))) => G u v.1) := by
          clear hHv hHt hU_le hH hU hF0 hF1 hEq
          have hVs := hV r t
          have hswap : ∀ {k : ℕ} {α β : Type} {H : α → β → Bool}, HasNL k H → HasNL k (fun v u => H u v) := by
            intro k α β H h
            induction h with
            | zero a b =>
              exact hasNL_congr (HasNL.zero b a) (fun v u => Bool.xor_comm _ _)
            | step H a1' a2' b1' b2' F0' F1' _ _ hE' _ _ ih0 ih1 ihU' ihV' =>
              refine HasNL.step (fun v u => H u v) b1' b2' a1' a2'
                (fun v u => F0' u v) (fun v u => F1' u v) ih0 ih1
                (fun v u => by rw [hE' u v, Bool.xor_comm (a1' u), Bool.xor_comm (a2' u)])
                ihV' ihU'
          exact hswap hVs
        have hle := hadamard_card_le (by simp [hNpos]) hHv hNLt
        have hcard : Fintype.card {v : Fin (4 ^ (s + 1)) // b1 v = r ∧ b2 v = t} = (V r t).card := by
          rw [Fintype.card_subtype]
        omega
      have hU_card : ∀ p q, (U p q).card = 4 ^ s := block_card_eq_of_le hNM a1 a2 hU_le
      have hV_card : ∀ r t, (V r t).card = 4 ^ s := block_card_eq_of_le hNM b1 b2 hV_le
      obtain ⟨tagU, htagU⟩ := hasNL_row_tag hF0
      obtain ⟨tagV, htagV⟩ := hasNL_col_tag hF0
      have hcond_eq : ∀ u v, (xor (a1 u) (b1 v) && xor (a2 u) (b2 v)) = true ↔
          v ∈ V (!(a1 u)) (!(a2 u)) := by
        intro u v
        simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [Bool.xor_comm (a1 u), Bool.xor_comm (a2 u)]
        exact xor_and_eq_true_iff (b1 v) (b2 v) (a1 u) (a2 u)
      have hU_inj : ∀ p q, ∀ u1 ∈ U p q, ∀ u2 ∈ U p q, tagU u1 = tagU u2 → u1 = u2 := by
        intro p q u1 hu1 u2 hu2 heq
        by_contra hne
        obtain ⟨c, hc⟩ := htagU u1 u2 heq
        have ha1 : a1 u1 = p ∧ a2 u1 = q := (Finset.mem_filter.mp hu1).2
        have ha2 : a1 u2 = p ∧ a2 u2 = q := (Finset.mem_filter.mp hu2).2
        let B := V (!p) (!q)
        let S := (Finset.univ : Finset (Fin (4 ^ (s + 1)))) \ B
        have hScard : S.card = 3 * 4 ^ s := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hV_card (!p) (!q)]
          omega
        have hBcard : B.card = 4 ^ s := hV_card (!p) (!q)
        have hsum0 := hH u1 u2 hne
        have hsplit : ∑ v : Fin (4 ^ (s + 1)), signZ (xor (G u1 v) (G u2 v)) =
            (∑ v ∈ S, signZ (xor (G u1 v) (G u2 v))) + (∑ v ∈ B, signZ (xor (G u1 v) (G u2 v))) := by
          rw [← Finset.sum_union disjoint_sdiff_self_left, Finset.sdiff_union_of_subset (Finset.subset_univ B)]
        have hS_const : ∑ v ∈ S, signZ (xor (G u1 v) (G u2 v)) = (3 * 4 ^ s : ℤ) * signZ c := by
          have hterm : ∀ v ∈ S, signZ (xor (G u1 v) (G u2 v)) = signZ c := by
            intro v hv
            have hnotB : v ∉ B := (Finset.mem_sdiff.mp hv).2
            have hc1 : (xor (a1 u1) (b1 v) && xor (a2 u1) (b2 v)) = false := by
              cases h : (xor (a1 u1) (b1 v) && xor (a2 u1) (b2 v))
              · rfl
              · exfalso; apply hnotB
                have := (hcond_eq u1 v).mp h
                simpa [B, ha1.1, ha1.2] using this
            have hc2 : (xor (a1 u2) (b1 v) && xor (a2 u2) (b2 v)) = false := by
              cases h : (xor (a1 u2) (b1 v) && xor (a2 u2) (b2 v))
              · rfl
              · exfalso; apply hnotB
                have := (hcond_eq u2 v).mp h
                simpa [B, ha2.1, ha2.2] using this
            rw [hEq u1 v, hEq u2 v, hc1, hc2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hc v]
            cases F0 u2 v <;> cases c <;> rfl
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hScard]
          push_cast; rfl
        have hBle := sum_signZ_le_card B (fun v => xor (G u1 v) (G u2 v))
        have hBge := sum_signZ_ge_neg_card B (fun v => xor (G u1 v) (G u2 v))
        have hBcardZ : (B.card : ℤ) = (4 : ℤ) ^ s := by rw [hBcard]; push_cast; rfl
        rw [hBcardZ] at hBle hBge
        rw [hsplit, hS_const] at hsum0
        cases c
        · rw [show signZ false = 1 from rfl, mul_one] at hsum0; linarith [hMposZ, hBge, hsum0]
        · rw [show signZ true = -1 from rfl, mul_neg, mul_one] at hsum0; linarith [hMposZ, hBle, hsum0]
      have hU_surj : ∀ p q, ∀ y : Fin (4 ^ s), ∃ u ∈ U p q, tagU u = y := by
        intro p q y
        have himg : ((U p q).image tagU).card = (U p q).card :=
          Finset.card_image_of_injOn (fun u1 hu1 u2 hu2 h => hU_inj p q u1 hu1 u2 hu2 h)
        have hfull : (U p q).image tagU = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [himg, hU_card p q, Fintype.card_fin]
        have hy : y ∈ (U p q).image tagU := by rw [hfull]; exact Finset.mem_univ y
        exact Finset.mem_image.mp hy
      have hV_inj : ∀ r t, ∀ v1 ∈ V r t, ∀ v2 ∈ V r t, tagV v1 = tagV v2 → v1 = v2 := by
        intro r t v1 hv1 v2 hv2 heq
        by_contra hne
        obtain ⟨c, hc⟩ := htagV v1 v2 heq
        have hb1 : b1 v1 = r ∧ b2 v1 = t := (Finset.mem_filter.mp hv1).2
        have hb2 : b1 v2 = r ∧ b2 v2 = t := (Finset.mem_filter.mp hv2).2
        let B := U (!r) (!t)
        let S := (Finset.univ : Finset (Fin (4 ^ (s + 1)))) \ B
        have hScard : S.card = 3 * 4 ^ s := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hU_card (!r) (!t)]
          omega
        have hBcard : B.card = 4 ^ s := hU_card (!r) (!t)
        have hsum0 := hHt v1 v2 hne
        have hsplit : ∑ u : Fin (4 ^ (s + 1)), signZ (xor (G u v1) (G u v2)) =
            (∑ u ∈ S, signZ (xor (G u v1) (G u v2))) + (∑ u ∈ B, signZ (xor (G u v1) (G u v2))) := by
          rw [← Finset.sum_union disjoint_sdiff_self_left, Finset.sdiff_union_of_subset (Finset.subset_univ B)]
        have hS_const : ∑ u ∈ S, signZ (xor (G u v1) (G u v2)) = (3 * 4 ^ s : ℤ) * signZ c := by
          have hterm : ∀ u ∈ S, signZ (xor (G u v1) (G u v2)) = signZ c := by
            intro u hu
            have hnotB : u ∉ B := (Finset.mem_sdiff.mp hu).2
            have hc1 : (xor (a1 u) (b1 v1) && xor (a2 u) (b2 v1)) = false := by
              cases h : (xor (a1 u) (b1 v1) && xor (a2 u) (b2 v1))
              · rfl
              · exfalso; apply hnotB
                rw [hb1.1, hb1.2] at h
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (xor_and_eq_true_iff (a1 u) (a2 u) r t).mp h⟩
            have hc2 : (xor (a1 u) (b1 v2) && xor (a2 u) (b2 v2)) = false := by
              cases h : (xor (a1 u) (b1 v2) && xor (a2 u) (b2 v2))
              · rfl
              · exfalso; apply hnotB
                rw [hb2.1, hb2.2] at h
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (xor_and_eq_true_iff (a1 u) (a2 u) r t).mp h⟩
            rw [hEq u v1, hEq u v2, hc1, hc2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hc u]
            cases F0 u v2 <;> cases c <;> rfl
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hScard]
          push_cast; rfl
        have hBle := sum_signZ_le_card B (fun u => xor (G u v1) (G u v2))
        have hBge := sum_signZ_ge_neg_card B (fun u => xor (G u v1) (G u v2))
        have hBcardZ : (B.card : ℤ) = (4 : ℤ) ^ s := by rw [hBcard]; push_cast; rfl
        rw [hBcardZ] at hBle hBge
        rw [hsplit, hS_const] at hsum0
        cases c
        · rw [show signZ false = 1 from rfl, mul_one] at hsum0; linarith [hMposZ, hBge, hsum0]
        · rw [show signZ true = -1 from rfl, mul_neg, mul_one] at hsum0; linarith [hMposZ, hBle, hsum0]
      have hV_surj : ∀ r t, ∀ y : Fin (4 ^ s), ∃ v ∈ V r t, tagV v = y := by
        intro r t y
        have himg : ((V r t).image tagV).card = (V r t).card :=
          Finset.card_image_of_injOn (fun v1 hv1 v2 hv2 h => hV_inj r t v1 hv1 v2 hv2 h)
        have hfull : (V r t).image tagV = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [himg, hV_card r t, Fintype.card_fin]
        have hy : y ∈ (V r t).image tagV := by rw [hfull]; exact Finset.mem_univ y
        exact Finset.mem_image.mp hy
      have hF1_neg : ∀ u v, (xor (a1 u) (b1 v) && xor (a2 u) (b2 v)) = true →
          F1 u v = !(F0 u v) := by
        intro u v hcond
        let p := a1 u
        let q := a2 u
        obtain ⟨u', hu', htag_eq⟩ := hU_surj (!p) q (tagU u)
        have ha' : a1 u' = !p ∧ a2 u' = q := (Finset.mem_filter.mp hu').2
        have hu_ne : u ≠ u' := by
          intro h; subst h
          have : p = !p := ha'.1
          cases p <;> simp at this
        obtain ⟨c, hc⟩ := htagU u u' htag_eq.symm
        let B1 := V (!p) (!q)
        let B2 := V p (!q)
        have hdB : Disjoint B1 B2 := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          have h1 := (Finset.mem_filter.mp hw1).2.1
          have h2 := (Finset.mem_filter.mp hw2).2.1
          rw [h1] at h2
          cases p <;> simp at h2
        let B := B1 ∪ B2
        let S := (Finset.univ : Finset (Fin (4 ^ (s + 1)))) \ B
        have hBcard : B.card = 2 * 4 ^ s := by
          rw [Finset.card_union_of_disjoint hdB, hV_card (!p) (!q), hV_card p (!q)]
          omega
        have hScard : S.card = 2 * 4 ^ s := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hBcard]
          omega
        have hsum0 := hH u u' hu_ne
        have hsplit : ∑ w : Fin (4 ^ (s + 1)), signZ (xor (G u w) (G u' w)) =
            (∑ w ∈ S, signZ (xor (G u w) (G u' w))) + (∑ w ∈ B, signZ (xor (G u w) (G u' w))) := by
          rw [← Finset.sum_union disjoint_sdiff_self_left, Finset.sdiff_union_of_subset (Finset.subset_univ B)]
        have hS_const : ∑ w ∈ S, signZ (xor (G u w) (G u' w)) = (2 * 4 ^ s : ℤ) * signZ c := by
          have hterm : ∀ w ∈ S, signZ (xor (G u w) (G u' w)) = signZ c := by
            intro w hw
            have hnotB : w ∉ B := (Finset.mem_sdiff.mp hw).2
            have hc1 : (xor (a1 u) (b1 w) && xor (a2 u) (b2 w)) = false := by
              cases h : (xor (a1 u) (b1 w) && xor (a2 u) (b2 w))
              · rfl
              · exfalso; apply hnotB
                exact Finset.mem_union_left _ ((hcond_eq u w).mp h)
            have hc2 : (xor (a1 u') (b1 w) && xor (a2 u') (b2 w)) = false := by
              cases h : (xor (a1 u') (b1 w) && xor (a2 u') (b2 w))
              · rfl
              · exfalso; apply hnotB
                have hw' := (hcond_eq u' w).mp h
                simp only [ha'.1, ha'.2, Bool.not_not] at hw'
                exact Finset.mem_union_right _ hw'
            rw [hEq u w, hEq u' w, hc1, hc2, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, hc w]
            cases F0 u' w <;> cases c <;> rfl
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hScard]
          push_cast; rfl
        have hBsum : ∑ w ∈ B, signZ (xor (G u w) (G u' w)) = -(signZ c) * (B.card : ℤ) := by
          rw [hsplit, hS_const] at hsum0
          rw [hBcard]
          push_cast
          linarith
        have hAll := sum_signZ_extremal B (fun w => xor (G u w) (G u' w)) c hBsum
        have hvB1 : v ∈ B1 := (hcond_eq u v).mp hcond
        have hvB : v ∈ B := Finset.mem_union_left _ hvB1
        have hGu_v := hAll v hvB
        have hv_notB2 : v ∉ B2 := Finset.disjoint_left.mp hdB hvB1
        have hc2v : (xor (a1 u') (b1 v) && xor (a2 u') (b2 v)) = false := by
          cases h : (xor (a1 u') (b1 v) && xor (a2 u') (b2 v))
          · rfl
          · exfalso; apply hv_notB2
            have hw' := (hcond_eq u' v).mp h
            simpa [ha'.1, ha'.2, Bool.not_not] using hw'
        rw [hEq u v, hEq u' v, hcond, hc2v, if_pos rfl, if_neg Bool.false_ne_true] at hGu_v
        have hF0v := hc v
        rw [hF0v]
        cases h1 : F1 u v <;> cases h2 : F0 u' v <;> cases hc' : c <;> simp [h1, h2, hc'] at hGu_v ⊢
      have hG_xor : ∀ u v,
          G u v = xor ((xor (a1 u) (b1 v)) && (xor (a2 u) (b2 v))) (F0 u v) := by
        intro u v
        rw [hEq u v]
        cases hcond : (xor (a1 u) (b1 v) && xor (a2 u) (b2 v))
        · simp
        · simp [hF1_neg u v hcond]
      let eU : Fin (4 ^ s) ≃ {u : Fin (4 ^ (s + 1)) // u ∈ U false false} :=
        (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hU_card false false)).symm
      let eV : Fin (4 ^ s) ≃ {v : Fin (4 ^ (s + 1)) // v ∈ V false false} :=
        (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hV_card false false)).symm
      let G0 : Fin (4 ^ s) → Fin (4 ^ s) → Bool := fun i j => F0 (eU i).1 (eV j).1
      have hG0_NL : HasNL s G0 := hasNL_comap hF0 (fun i => (eU i).1) (fun j => (eV j).1)
      have hG0_H : IsHadamard G0 := by
        intro i1 i2 hne
        have hu1_mem := (eU i1).2
        have hu2_mem := (eU i2).2
        have hu_ne : (eU i1).1 ≠ (eU i2).1 := fun h => hne (eU.injective (Subtype.ext h))
        have ha1 : a1 (eU i1).1 = false ∧ a2 (eU i1).1 = false := (Finset.mem_filter.mp hu1_mem).2
        have ha2 : a1 (eU i2).1 = false ∧ a2 (eU i2).1 = false := (Finset.mem_filter.mp hu2_mem).2
        have hGF0 : ∀ v, xor (G (eU i1).1 v) (G (eU i2).1 v) = xor (F0 (eU i1).1 v) (F0 (eU i2).1 v) := by
          intro v
          rw [hG_xor (eU i1).1 v, hG_xor (eU i2).1 v, ha1.1, ha1.2, ha2.1, ha2.2]
          cases (xor false (b1 v) && xor false (b2 v)) <;>
            cases F0 (eU i1).1 v <;> cases F0 (eU i2).1 v <;> rfl
        have hsum_all : ∑ v : Fin (4 ^ (s + 1)), signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) = 0 := by
          have := hH (eU i1).1 (eU i2).1 hu_ne
          simpa [hGF0] using this
        have hblock_eq : ∀ r t : Bool,
            ∑ v ∈ V r t, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) =
              ∑ v ∈ V false false, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) := by
          intro r t
          choose toV0 htoV0_mem htoV0_tag using fun y => hV_surj false false y
          refine Finset.sum_bij (fun v _ => toV0 (tagV v)) ?_ ?_ ?_ ?_
          · intro v _; exact htoV0_mem (tagV v)
          · intro v1 hv1 v2 hv2 heq
            apply hV_inj r t v1 hv1 v2 hv2
            have h1 := htoV0_tag (tagV v1)
            have h2 := htoV0_tag (tagV v2)
            rw [heq] at h1
            exact h1.symm.trans h2
          · intro v0 hv0
            obtain ⟨v, hv, htv⟩ := hV_surj r t (tagV v0)
            refine ⟨v, hv, ?_⟩
            apply hV_inj false false (toV0 (tagV v)) (htoV0_mem _) v0 hv0
            rw [htoV0_tag, htv]
          · intro v _
            obtain ⟨c, hc⟩ := htagV v (toV0 (tagV v)) (htoV0_tag (tagV v)).symm
            rw [hc (eU i1).1, hc (eU i2).1]
            cases F0 (eU i1).1 (toV0 (tagV v)) <;> cases F0 (eU i2).1 (toV0 (tagV v)) <;> cases c <;> rfl
        have hpart : ∑ v : Fin (4 ^ (s + 1)), signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) =
            (∑ v ∈ V false false, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v))) +
            (∑ v ∈ V false true, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v))) +
            (∑ v ∈ V true false, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v))) +
            (∑ v ∈ V true true, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v))) := by
          have hd1 : Disjoint (V false false) (V false true) := by
            rw [Finset.disjoint_left]; intro x h1 h2; simp [V] at h1 h2; rw [h1.2] at h2; cases h2.2
          have hd2 : Disjoint (V true false) (V true true) := by
            rw [Finset.disjoint_left]; intro x h1 h2; simp [V] at h1 h2; rw [h1.2] at h2; cases h2.2
          have hd3 : Disjoint (V false false ∪ V false true) (V true false ∪ V true true) := by
            rw [Finset.disjoint_left]; intro x h1 h2
            simp [V] at h1 h2
            rcases h1 with ⟨h1a, _⟩ | ⟨h1a, _⟩ <;> rcases h2 with ⟨h2a, _⟩ | ⟨h2a, _⟩ <;>
              (rw [h1a] at h2a; cases h2a)
          have hun : (V false false ∪ V false true) ∪ (V true false ∪ V true true) = Finset.univ := by
            ext x; simp [V]; cases b1 x <;> cases b2 x <;> simp
          rw [← hun, Finset.sum_union hd3, Finset.sum_union hd1, Finset.sum_union hd2]
          ring
        rw [hpart, hblock_eq false true, hblock_eq true false, hblock_eq true true] at hsum_all
        have hV0_sum : ∑ v ∈ V false false, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) = 0 := by
          omega
        have heq_sum : ∑ j : Fin (4 ^ s), signZ (xor (G0 i1 j) (G0 i2 j)) =
            ∑ v ∈ V false false, signZ (xor (F0 (eU i1).1 v) (F0 (eU i2).1 v)) := by
          rw [← Finset.sum_coe_sort (V false false)]
          exact Fintype.sum_equiv eV (fun j => signZ (xor (G0 i1 j) (G0 i2 j)))
            (fun v => signZ (xor (F0 (eU i1).1 v.1) (F0 (eU i2).1 v.1))) (fun _ => rfl)
        rw [heq_sum, hV0_sum]
      obtain ⟨α0, β0, φ0, ψ0, hIP0⟩ := ih G0 hG0_H hG0_NL
      choose piU_val hpiU_mem hpiU_tag using fun u : Fin (4 ^ (s + 1)) => hU_surj false false (tagU u)
      choose piV_val hpiV_mem hpiV_tag using fun v : Fin (4 ^ (s + 1)) => hV_surj false false (tagV v)
      choose σU hσU using fun u : Fin (4 ^ (s + 1)) => htagU u (piU_val u) (hpiU_tag u).symm
      choose σV hσV using fun v : Fin (4 ^ (s + 1)) => htagV v (piV_val v) (hpiV_tag v).symm
      let piU : Fin (4 ^ (s + 1)) → Fin (4 ^ s) := fun u => eU.symm ⟨piU_val u, hpiU_mem u⟩
      let piV : Fin (4 ^ (s + 1)) → Fin (4 ^ s) := fun v => eV.symm ⟨piV_val v, hpiV_mem v⟩
      let α : Fin (4 ^ (s + 1)) → Bool := fun u =>
        xor (xor (a1 u && a2 u) (σU u)) (α0 (piU u))
      let β : Fin (4 ^ (s + 1)) → Bool := fun v =>
        xor (xor (b1 v && b2 v) (σV v)) (β0 (piV v))
      let φ : Fin (4 ^ (s + 1)) → Fin (2 * (s + 1)) → Bool := fun u i =>
        if h : i.val < 2 * s then φ0 (piU u) ⟨i.val, h⟩
        else if i.val = 2 * s then a1 u else a2 u
      let ψ : Fin (4 ^ (s + 1)) → Fin (2 * (s + 1)) → Bool := fun v i =>
        if h : i.val < 2 * s then ψ0 (piV v) ⟨i.val, h⟩
        else if i.val = 2 * s then b2 v else b1 v
      refine ⟨α, β, φ, ψ, fun u v => ?_⟩
      have hF0_uv : F0 u v = xor (xor (σU u) (σV v)) (G0 (piU u) (piV v)) := by
        have h1 := hσU u v
        have h2 := hσV v (piU_val u)
        have h3 : G0 (piU u) (piV v) = F0 (piU_val u) (piV_val v) := by
          simp [G0, piU, piV]
        rw [h1, h2, h3]
        cases σU u <;> cases σV v <;> cases F0 (piU_val u) (piV_val v) <;> rfl
      have hG0_val := hIP0 (piU u) (piV v)
      have hsum_split :
          (∑ i : Fin (2 * (s + 1)), b2z (φ u i) * b2z (ψ v i)) =
            (∑ i : Fin (2 * s), b2z (φ0 (piU u) i) * b2z (ψ0 (piV v) i)) +
            b2z (a1 u) * b2z (b2 v) + b2z (a2 u) * b2z (b1 v) := by
        have hadd : 2 * (s + 1) = 2 * s + 2 := by omega
        let eFin : Fin (2 * s + 2) ≃ Fin (2 * (s + 1)) := finCongr hadd.symm
        rw [← Fintype.sum_equiv eFin (fun i => b2z (φ u (eFin i)) * b2z (ψ v (eFin i)))
          (fun i => b2z (φ u i) * b2z (ψ v i)) (fun _ => rfl)]
        rw [Fin.sum_univ_add]
        have hL : ∑ i : Fin (2 * s),
            b2z (φ u (eFin (Fin.castAdd 2 i))) * b2z (ψ v (eFin (Fin.castAdd 2 i))) =
            ∑ i : Fin (2 * s), b2z (φ0 (piU u) i) * b2z (ψ0 (piV v) i) := by
          apply Finset.sum_congr rfl
          intro i _
          have hlt : (eFin (Fin.castAdd 2 i)).val < 2 * s := by simp [eFin]
          simp [φ, ψ, hlt, eFin]
        have hR : ∑ i : Fin 2,
            b2z (φ u (eFin (Fin.natAdd (2 * s) i))) * b2z (ψ v (eFin (Fin.natAdd (2 * s) i))) =
            b2z (a1 u) * b2z (b2 v) + b2z (a2 u) * b2z (b1 v) := by
          rw [Fin.sum_univ_two]
          have h0_not : ¬ ((eFin (Fin.natAdd (2 * s) 0)).val < 2 * s) := by simp [eFin]
          have h0_eq : (eFin (Fin.natAdd (2 * s) 0)).val = 2 * s := by simp [eFin]
          have h1_not : ¬ ((eFin (Fin.natAdd (2 * s) 1)).val < 2 * s) := by simp [eFin]
          have h1_ne : (eFin (Fin.natAdd (2 * s) 1)).val ≠ 2 * s := by simp [eFin]
          simp [φ, ψ, h0_not, h0_eq, h1_not, h1_ne]
        rw [hL, hR, add_assoc]
      have hG_b2z : b2z (G u v) =
          b2z (α u) + b2z (β v) + ∑ i : Fin (2 * (s + 1)), b2z (φ u i) * b2z (ψ v i) := by
        rw [hG_xor u v, hF0_uv, hG0_val, hsum_split]
        rw [b2z_xor, b2z_and, b2z_xor, b2z_xor, b2z_xor, b2z_xor, b2z_z2b]
        simp only [α, β, b2z_xor, b2z_and]
        ring
      rw [← hG_b2z, z2b_b2z]


structure Build (N : ℕ) where
  gates : List Gate
  hfan : ∀ g ∈ gates, g.inputs.length ≤ 2
  hback : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < N + N + j

def Build.len {N : ℕ} (B : Build N) : ℕ := N + N + B.gates.length

def Build.val {N : ℕ} (B : Build N) (u v : Fin N) (w : ℕ) : Bool :=
  (B.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))])
    (oneEach u v)).getD w false

def Build.cost {N : ℕ} (B : Build N) : ℕ := B.gates.countP nonlinear

lemma foldl_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp; omega

lemma foldl_getD_append_gate (gs : List Gate) (g : Gate) (init : List Bool) :
    let ws := gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) init
    ((gs ++ [g]).foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) init) =
      ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))] := by
  simp [List.foldl_append]

def Build.push {N : ℕ} (B : Build N) (g : Gate)
    (hgf : g.inputs.length ≤ 2) (hgb : ∀ i ∈ g.inputs, i < B.len) : Build N where
  gates := B.gates ++ [g]
  hfan := by
    intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h1 | rfl
    · exact B.hfan g' h1
    · exact hgf
  hback := by
    intro j hj i hi
    by_cases hlt : j < B.gates.length
    · rw [List.getElem_append_left hlt] at hi
      exact B.hback j hlt i hi
    · have heq : j = B.gates.length := by simp at hj; omega
      subst heq
      rw [List.getElem_append_right (le_refl _)] at hi
      simp only [Nat.sub_self, List.getElem_singleton] at hi
      exact hgb i hi

lemma Build.push_len {N : ℕ} (B : Build N) (g : Gate) hgf hgb :
    (B.push g hgf hgb).len = B.len + 1 := by
  simp [Build.push, Build.len]; omega

lemma Build.push_cost {N : ℕ} (B : Build N) (g : Gate) hgf hgb :
    (B.push g hgf hgb).cost = B.cost + (if nonlinear g then 1 else 0) := by
  simp [Build.push, Build.cost, List.countP_append, List.countP_cons]

lemma Build.push_val_old {N : ℕ} (B : Build N) (g : Gate) hgf hgb
    (u v : Fin N) (w : ℕ) (hw : w < B.len) :
    (B.push g hgf hgb).val u v w = B.val u v w := by
  simp only [Build.val, Build.push, foldl_getD_append_gate]
  have hlen : (B.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))])
      (oneEach u v)).length = B.len := by
    rw [foldl_length]; simp [oneEach, Build.len]
  have hw' : w < (B.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))])
      (oneEach u v)).length := by rw [hlen]; exact hw
  rw [List.getD, List.getD, List.getElem?_append_left hw']

lemma Build.push_val_new {N : ℕ} (B : Build N) (g : Gate) hgf hgb (u v : Fin N) :
    (B.push g hgf hgb).val u v B.len = g.op.eval (g.inputs.map (B.val u v)) := by
  simp only [Build.val, Build.push, foldl_getD_append_gate]
  have hlen : (B.gates.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))])
      (oneEach u v)).length = B.len := by
    rw [foldl_length]; simp [oneEach, Build.len]
  simp only [List.getD, ← hlen, List.getElem?_append_right (le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]
  rfl

def Build.empty (N : ℕ) : Build N where
  gates := []
  hfan := by simp
  hback := by simp

lemma Build.empty_val_left {N : ℕ} (u v : Fin N) (i : ℕ) (hi : i < N) :
    (Build.empty N).val u v i = decide (i = u.val) := by
  simp only [Build.empty, Build.val, List.foldl_nil, oneEach, List.getD]
  have hlen : (List.ofFn (fun x : Fin N => decide (x = u))).length = N := by simp
  rw [List.getElem?_append_left (by omega)]
  simp [List.getElem?_ofFn, hi, Fin.ext_iff]

lemma Build.empty_val_right {N : ℕ} (u v : Fin N) (j : ℕ) (hj : j < N) :
    (Build.empty N).val u v (N + j) = decide (j = v.val) := by
  simp only [Build.empty, Build.val, List.foldl_nil, oneEach, List.getD]
  have hlen : (List.ofFn (fun x : Fin N => decide (x = u))).length = N := by simp
  rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
  simp [List.getElem?_ofFn, hj, Fin.ext_iff]

def mkFalse {N : ℕ} (B : Build N) : Build N × ℕ :=
  (B.push ⟨GateOp.or, []⟩ (by simp) (by simp), B.len)

def mkXor {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) : Build N × ℕ :=
  let B1 := B.push ⟨GateOp.mod 2, [w1, w2]⟩ (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega)
  let B2 := B1.push ⟨GateOp.not, [B.len]⟩ (by simp) (by intro i hi; simp at hi; subst hi; rw [Build.push_len]; omega)
  (B2, B1.len)

def mkAnd {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) : Build N × ℕ :=
  (B.push ⟨GateOp.and, [w1, w2]⟩ (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega), B.len)

lemma mkFalse_spec {N : ℕ} (B : Build N) :
    (mkFalse B).2 < (mkFalse B).1.len ∧
    B.len ≤ (mkFalse B).1.len ∧
    (mkFalse B).1.cost = B.cost ∧
    (∀ u v w, w < B.len → (mkFalse B).1.val u v w = B.val u v w) ∧
    (∀ u v, (mkFalse B).1.val u v (mkFalse B).2 = false) := by
  dsimp only [mkFalse]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Build.push_len]
  · simp [Build.push_len]
  · simp [Build.push_cost, nonlinear]
  · intro u v w hw; exact Build.push_val_old B _ _ _ u v w hw
  · intro u v; simp [Build.push_val_new, GateOp.eval]

lemma mkXor_spec {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) :
    (mkXor B w1 w2 h1 h2).2 < (mkXor B w1 w2 h1 h2).1.len ∧
    B.len ≤ (mkXor B w1 w2 h1 h2).1.len ∧
    (mkXor B w1 w2 h1 h2).1.cost = B.cost ∧
    (∀ u v w, w < B.len → (mkXor B w1 w2 h1 h2).1.val u v w = B.val u v w) ∧
    (∀ u v, (mkXor B w1 w2 h1 h2).1.val u v (mkXor B w1 w2 h1 h2).2 =
      xor (B.val u v w1) (B.val u v w2)) := by
  have hnl1 : nonlinear ⟨GateOp.mod 2, [w1, w2]⟩ = false := by simp [nonlinear, GateOp.eval]
  have hnl2 : nonlinear ⟨GateOp.not, [B.len]⟩ = false := by simp [nonlinear]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [mkXor, Build.push_len]; omega
  · simp only [mkXor, Build.push_len]; omega
  · simp only [mkXor, Build.push_cost, hnl1, hnl2]; simp
  · intro u v w hw
    dsimp only [mkXor]
    rw [Build.push_val_old _ _ _ _ u v w (by rw [Build.push_len]; omega),
      Build.push_val_old B _ _ _ u v w hw]
  · intro u v
    dsimp only [mkXor]
    rw [Build.push_val_new]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [Build.push_val_new]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    cases B.val u v w1 <;> cases B.val u v w2 <;> decide

lemma mkAnd_spec {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) :
    (mkAnd B w1 w2 h1 h2).2 < (mkAnd B w1 w2 h1 h2).1.len ∧
    B.len ≤ (mkAnd B w1 w2 h1 h2).1.len ∧
    (mkAnd B w1 w2 h1 h2).1.cost = B.cost + 1 ∧
    (∀ u v w, w < B.len → (mkAnd B w1 w2 h1 h2).1.val u v w = B.val u v w) ∧
    (∀ u v, (mkAnd B w1 w2 h1 h2).1.val u v (mkAnd B w1 w2 h1 h2).2 =
      (B.val u v w1 && B.val u v w2)) := by
  dsimp only [mkAnd]
  have hnl : nonlinear ⟨GateOp.and, [w1, w2]⟩ = true := by simp [nonlinear, GateOp.eval]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Build.push_len]
  · simp [Build.push_len]
  · simp [Build.push_cost, hnl]
  · intro u v w hw; exact Build.push_val_old B _ _ _ u v w hw
  · intro u v
    simp only [Build.push_val_new, List.map_cons, List.map_nil, GateOp.eval]
    cases B.val u v w1 <;> cases B.val u v w2 <;> decide

lemma exists_false {N : ℕ} (B : Build N) :
    ∃ (B' : Build N) (w : ℕ),
      w < B'.len ∧ B.len ≤ B'.len ∧ B'.cost = B.cost ∧
      (∀ u v w0, w0 < B.len → B'.val u v w0 = B.val u v w0) ∧
      (∀ u v, B'.val u v w = false) :=
  ⟨(mkFalse B).1, (mkFalse B).2, mkFalse_spec B⟩

lemma exists_xor {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) :
    ∃ (B' : Build N) (w : ℕ),
      w < B'.len ∧ B.len ≤ B'.len ∧ B'.cost = B.cost ∧
      (∀ u v w0, w0 < B.len → B'.val u v w0 = B.val u v w0) ∧
      (∀ u v, B'.val u v w = xor (B.val u v w1) (B.val u v w2)) :=
  ⟨(mkXor B w1 w2 h1 h2).1, (mkXor B w1 w2 h1 h2).2, mkXor_spec B w1 w2 h1 h2⟩

lemma exists_and {N : ℕ} (B : Build N) (w1 w2 : ℕ) (h1 : w1 < B.len) (h2 : w2 < B.len) :
    ∃ (B' : Build N) (w : ℕ),
      w < B'.len ∧ B.len ≤ B'.len ∧ B'.cost = B.cost + 1 ∧
      (∀ u v w0, w0 < B.len → B'.val u v w0 = B.val u v w0) ∧
      (∀ u v, B'.val u v w = (B.val u v w1 && B.val u v w2)) :=
  ⟨(mkAnd B w1 w2 h1 h2).1, (mkAnd B w1 w2 h1 h2).2, mkAnd_spec B w1 w2 h1 h2⟩

lemma build_exists_left {N : ℕ} (B0 : Build N) (f : Fin N → Bool)
    (hB0_in : ∀ u v (i : ℕ) (hi : i < N), B0.val u v i = decide (i = u.val)) :
    ∃ (B : Build N) (w : ℕ),
      w < B.len ∧ B0.len ≤ B.len ∧ B.cost = B0.cost ∧
      (∀ u v w0, w0 < B0.len → B.val u v w0 = B0.val u v w0) ∧
      (∀ u v, B.val u v w = f u) := by
  have hloop : ∀ m ≤ N,
      ∃ (B : Build N) (w : ℕ),
        w < B.len ∧ B0.len ≤ B.len ∧ B.cost = B0.cost ∧
        (∀ u v w0, w0 < B0.len → B.val u v w0 = B0.val u v w0) ∧
        (∀ u v, B.val u v w = if u.val < m then f u else false) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨h1, h2, h3, h4, h5⟩ := mkFalse_spec B0
      exact ⟨(mkFalse B0).1, (mkFalse B0).2, h1, h2, h3, h4, fun u v => by simp [h5 u v]⟩
    | succ m ih =>
      intro hm
      obtain ⟨B, w, hw, hlen, hcost, hold, hval⟩ := ih (by omega)
      by_cases hf : f ⟨m, by omega⟩ = true
      · have hm_lt : m < B.len := by
          have : m < B0.len := by simp [Build.len]; omega
          omega
        obtain ⟨h1, h2, h3, h4, h5⟩ := mkXor_spec B w m hw hm_lt
        refine ⟨(mkXor B w m hw hm_lt).1, (mkXor B w m hw hm_lt).2, h1, le_trans hlen h2,
          by rw [h3, hcost],
          fun u v w0 hw0 => by rw [h4 u v w0 (lt_of_lt_of_le hw0 hlen), hold u v w0 hw0],
          fun u v => ?_⟩
        rw [h5 u v, hval u v]
        have hm_b0 : m < B0.len := by simp [Build.len]; omega
        rw [hold u v m hm_b0, hB0_in u v m (by omega)]
        by_cases hu : u.val < m
        · have hne : m ≠ u.val := by omega
          have hlt : u.val < m + 1 := by omega
          simp [hu, hne, hlt]
        · by_cases heq : m = u.val
          · have hlt : u.val < m + 1 := by omega
            have hfu : f u = true := by
              have : u = ⟨m, by omega⟩ := Fin.ext heq.symm
              rw [this]; exact hf
            simp [hu, heq, hlt, hfu]
          · have hnot : ¬ (u.val < m + 1) := by omega
            simp [hu, heq, hnot]
      · refine ⟨B, w, hw, hlen, hcost, hold, fun u v => ?_⟩
        rw [hval u v]
        by_cases hu : u.val < m
        · have hlt : u.val < m + 1 := by omega
          simp [hu, hlt]
        · by_cases heq : u.val = m
          · have hlt : u.val < m + 1 := by omega
            have hfu : f u = false := by
              have : u = ⟨m, by omega⟩ := Fin.ext heq
              rw [this]
              cases h : f ⟨m, by omega⟩
              · rfl
              · exact absurd h hf
            simp [hu, hlt, hfu]
          · have hnot : ¬ (u.val < m + 1) := by omega
            simp [hu, hnot]
  obtain ⟨B, w, hw, hlen, hcost, hold, hval⟩ := hloop N (le_refl N)
  exact ⟨B, w, hw, hlen, hcost, hold, fun u v => by simpa [u.isLt] using hval u v⟩

lemma build_exists_right {N : ℕ} (B0 : Build N) (g : Fin N → Bool)
    (hB0_in : ∀ u v (j : ℕ) (hj : j < N), B0.val u v (N + j) = decide (j = v.val)) :
    ∃ (B : Build N) (w : ℕ),
      w < B.len ∧ B0.len ≤ B.len ∧ B.cost = B0.cost ∧
      (∀ u v w0, w0 < B0.len → B.val u v w0 = B0.val u v w0) ∧
      (∀ u v, B.val u v w = g v) := by
  have hloop : ∀ m ≤ N,
      ∃ (B : Build N) (w : ℕ),
        w < B.len ∧ B0.len ≤ B.len ∧ B.cost = B0.cost ∧
        (∀ u v w0, w0 < B0.len → B.val u v w0 = B0.val u v w0) ∧
        (∀ u v, B.val u v w = if v.val < m then g v else false) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨h1, h2, h3, h4, h5⟩ := mkFalse_spec B0
      exact ⟨(mkFalse B0).1, (mkFalse B0).2, h1, h2, h3, h4, fun u v => by simp [h5 u v]⟩
    | succ m ih =>
      intro hm
      obtain ⟨B, w, hw, hlen, hcost, hold, hval⟩ := ih (by omega)
      by_cases hg : g ⟨m, by omega⟩ = true
      · have hm_b0 : N + m < B0.len := by simp [Build.len]; omega
        have hm_lt : N + m < B.len := lt_of_lt_of_le hm_b0 hlen
        obtain ⟨h1, h2, h3, h4, h5⟩ := mkXor_spec B w (N + m) hw hm_lt
        refine ⟨(mkXor B w (N + m) hw hm_lt).1, (mkXor B w (N + m) hw hm_lt).2, h1, le_trans hlen h2,
          by rw [h3, hcost],
          fun u v w0 hw0 => by rw [h4 u v w0 (lt_of_lt_of_le hw0 hlen), hold u v w0 hw0],
          fun u v => ?_⟩
        rw [h5 u v, hval u v, hold u v (N + m) hm_b0, hB0_in u v m (by omega)]
        by_cases hv : v.val < m
        · have hne : m ≠ v.val := by omega
          have hlt : v.val < m + 1 := by omega
          simp [hv, hne, hlt]
        · by_cases heq : m = v.val
          · have hlt : v.val < m + 1 := by omega
            have hgv : g v = true := by
              have : v = ⟨m, by omega⟩ := Fin.ext heq.symm
              rw [this]; exact hg
            simp [hv, heq, hlt, hgv]
          · have hnot : ¬ (v.val < m + 1) := by omega
            simp [hv, heq, hnot]
      · refine ⟨B, w, hw, hlen, hcost, hold, fun u v => ?_⟩
        rw [hval u v]
        by_cases hv : v.val < m
        · have hlt : v.val < m + 1 := by omega
          simp [hv, hlt]
        · by_cases heq : v.val = m
          · have hlt : v.val < m + 1 := by omega
            have hgv : g v = false := by
              have : v = ⟨m, by omega⟩ := Fin.ext heq
              rw [this]
              cases h : g ⟨m, by omega⟩
              · rfl
              · exact absurd h hg
            simp [hv, hlt, hgv]
          · have hnot : ¬ (v.val < m + 1) := by omega
            simp [hv, hnot]
  obtain ⟨B, w, hw, hlen, hcost, hold, hval⟩ := hloop N (le_refl N)
  exact ⟨B, w, hw, hlen, hcost, hold, fun u v => by simpa [v.isLt] using hval u v⟩

lemma pair_trick (a b c d : Bool) :
    xor (xor (a && b) (c && d)) ((xor a d) && (xor b c)) = xor (a && c) (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma upper_pair_step {N : ℕ} (B : Build N) (wacc : ℕ) (hwacc : wacc < B.len) (m : ℕ)
    (hBL : ∀ u v (i : ℕ) (hi : i < N), B.val u v i = decide (i = u.val))
    (hBR : ∀ u v (j : ℕ) (hj : j < N), B.val u v (N + j) = decide (j = v.val)) :
    ∃ (B' : Build N) (wf : ℕ),
      wf < B'.len ∧ B.len ≤ B'.len ∧ B'.cost = B.cost + 1 ∧
      (∀ u v w0, w0 < B.len → B'.val u v w0 = B.val u v w0) ∧
      (∀ u v, B'.val u v wf = xor (B.val u v wacc)
        (xor (u.val.testBit (2 * m) && v.val.testBit (2 * m))
          (u.val.testBit (2 * m + 1) && v.val.testBit (2 * m + 1)))) := by
  have hBL_of : ∀ (B1 : Build N), B.len ≤ B1.len → (∀ u v w0, w0 < B.len → B1.val u v w0 = B.val u v w0) →
      ∀ u v (i : ℕ) (hi : i < N), B1.val u v i = decide (i = u.val) := by
    intro B1 _ hold u v i hi
    have hiB : i < B.len := by simp [Build.len]; omega
    rw [hold u v i hiB, hBL u v i hi]
  have hBR_of : ∀ (B1 : Build N), B.len ≤ B1.len → (∀ u v w0, w0 < B.len → B1.val u v w0 = B.val u v w0) →
      ∀ u v (j : ℕ) (hj : j < N), B1.val u v (N + j) = decide (j = v.val) := by
    intro B1 _ hold u v j hj
    have hjB : N + j < B.len := by simp [Build.len]; omega
    rw [hold u v (N + j) hjB, hBR u v j hj]
  obtain ⟨B1, wu1, hwu1, hlen1, hcost1, hold1, hval1⟩ :=
    build_exists_left B (fun u => u.val.testBit (2 * m)) hBL
  obtain ⟨B2, wu2, hwu2, hlen2, hcost2, hold2, hval2⟩ :=
    build_exists_left B1 (fun u => u.val.testBit (2 * m + 1)) (hBL_of B1 hlen1 hold1)
  have hold20 : ∀ u v w0, w0 < B.len → B2.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold2 u v w0 (lt_of_lt_of_le hw0 hlen1), hold1 u v w0 hw0]
  obtain ⟨B3, wv1, hwv1, hlen3, hcost3, hold3, hval3⟩ :=
    build_exists_right B2 (fun v => v.val.testBit (2 * m)) (hBR_of B2 (le_trans hlen1 hlen2) hold20)
  have hold30 : ∀ u v w0, w0 < B.len → B3.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold3 u v w0 (lt_of_lt_of_le hw0 (le_trans hlen1 hlen2)), hold20 u v w0 hw0]
  obtain ⟨B4, wv2, hwv2, hlen4, hcost4, hold4, hval4⟩ :=
    build_exists_right B3 (fun v => v.val.testBit (2 * m + 1)) (hBR_of B3 (le_trans (le_trans hlen1 hlen2) hlen3) hold30)
  have hold40 : ∀ u v w0, w0 < B.len → B4.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold4 u v w0 (by omega), hold30 u v w0 hw0]
  obtain ⟨B5, wu12, hwu12, hlen5, hcost5, hold5, hval5⟩ :=
    build_exists_left B4 (fun u => u.val.testBit (2 * m) && u.val.testBit (2 * m + 1)) (hBL_of B4 (by omega) hold40)
  have hold50 : ∀ u v w0, w0 < B.len → B5.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold5 u v w0 (by omega), hold40 u v w0 hw0]
  obtain ⟨B6, wv12, hwv12, hlen6, hcost6, hold6, hval6⟩ :=
    build_exists_right B5 (fun v => v.val.testBit (2 * m) && v.val.testBit (2 * m + 1)) (hBR_of B5 (by omega) hold50)
  have hold60 : ∀ u v w0, w0 < B.len → B6.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold6 u v w0 (by omega), hold50 u v w0 hw0]
  obtain ⟨B7, wx1, hwx1, hlen7, hcost7, hold7, hval7⟩ := exists_xor B6 wu1 wv2 (by omega) (by omega)
  obtain ⟨B8, wx2, hwx2, hlen8, hcost8, hold8, hval8⟩ := exists_xor B7 wu2 wv1 (by omega) (by omega)
  obtain ⟨B9, wp, hwp, hlen9, hcost9, hold9, hval9⟩ := exists_and B8 wx1 wx2 (by omega) hwx2
  obtain ⟨B10, wuv, hwuv, hlen10, hcost10, hold10, hval10⟩ := exists_xor B9 wu12 wv12 (by omega) (by omega)
  obtain ⟨B11, wt, hwt, hlen11, hcost11, hold11, hval11⟩ := exists_xor B10 wuv wp hwuv (by omega)
  obtain ⟨B12, wf, hwf, hlen12, hcost12, hold12, hval12⟩ := exists_xor B11 wacc wt (by omega) hwt
  have hhold : ∀ u v w0, w0 < B.len → B12.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold12 u v w0 (by omega), hold11 u v w0 (by omega), hold10 u v w0 (by omega),
      hold9 u v w0 (by omega), hold8 u v w0 (by omega), hold7 u v w0 (by omega), hold60 u v w0 hw0]
  refine ⟨B12, wf, hwf, by omega, by omega, hhold, fun u v => ?_⟩
  have h6_u1 : B6.val u v wu1 = u.val.testBit (2 * m) := by
    rw [hold6 u v wu1 (by omega), hold5 u v wu1 (by omega), hold4 u v wu1 (by omega),
      hold3 u v wu1 (by omega), hold2 u v wu1 hwu1, hval1 u v]
  have h6_u2 : B6.val u v wu2 = u.val.testBit (2 * m + 1) := by
    rw [hold6 u v wu2 (by omega), hold5 u v wu2 (by omega), hold4 u v wu2 (by omega),
      hold3 u v wu2 hwu2, hval2 u v]
  have h6_v1 : B6.val u v wv1 = v.val.testBit (2 * m) := by
    rw [hold6 u v wv1 (by omega), hold5 u v wv1 (by omega), hold4 u v wv1 hwv1, hval3 u v]
  have h6_v2 : B6.val u v wv2 = v.val.testBit (2 * m + 1) := by
    rw [hold6 u v wv2 (by omega), hold5 u v wv2 hwv2, hval4 u v]
  have h6_u12 : B6.val u v wu12 = (u.val.testBit (2 * m) && u.val.testBit (2 * m + 1)) := by
    rw [hold6 u v wu12 hwu12, hval5 u v]
  have h6_v12 : B6.val u v wv12 = (v.val.testBit (2 * m) && v.val.testBit (2 * m + 1)) := hval6 u v
  rw [hval12 u v, hold11 u v wacc (by omega), hold10 u v wacc (by omega),
    hold9 u v wacc (by omega), hold8 u v wacc (by omega), hold7 u v wacc (by omega),
    hold60 u v wacc hwacc, hval11 u v, hval10 u v, hold9 u v wu12 (by omega),
    hold8 u v wu12 (by omega), hold7 u v wu12 (by omega), h6_u12,
    hold9 u v wv12 (by omega), hold8 u v wv12 (by omega), hold7 u v wv12 hwv12, h6_v12,
    hold10 u v wp hwp, hval9 u v, hold8 u v wx1 hwx1, hval7 u v, h6_u1, h6_v2,
    hval8 u v, hold7 u v wu2 (by omega), hold7 u v wv1 (by omega), h6_u2, h6_v1, pair_trick]

lemma sum_range_two_mul {α : Type} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, add_assoc]

def dotB (k : ℕ) {N : ℕ} (x y : Fin N) : Bool :=
  ((Finset.univ : Finset (Fin k)).filter (fun i =>
    x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1

def IsAff {n : ℕ} (W : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, xor (W x) (W y) = xor (W (fun i => xor (x i) (y i))) (W (fun _ => false))

lemma had_of_half {N : ℕ} (G : Fin N → Fin N → Bool)
    (hG : ∀ u v : Fin N, u ≠ v →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G v c)).card = N) :
    IsHadamard G := by
  intro u1 u2 hne
  have h := hG u1 u2 hne
  have hterm : ∀ c : Fin N, signZ (xor (G u1 c) (G u2 c)) =
      (1 : ℤ) - 2 * (if G u1 c ≠ G u2 c then 1 else 0) := by
    intro c
    cases G u1 c <;> cases G u2 c <;> simp [signZ]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have h' : (2 : ℤ) * (((Finset.univ : Finset (Fin N)).filter (fun c => G u1 c ≠ G u2 c)).card : ℤ)
      = (N : ℤ) := by exact_mod_cast h
  linarith

lemma had_inj {α β : Type} [Fintype α] [Fintype β] {G : α → β → Bool}
    (hβ : 0 < Fintype.card β) (hH : IsHadamard G) {u1 u2 : α} (b : Bool)
    (h : ∀ v, G u1 v = xor (G u2 v) b) : u1 = u2 := by
  by_contra hne
  have hterm : ∀ v : β, signZ (xor (G u1 v) (G u2 v)) = signZ b := fun v => by
    rw [h v]
    cases G u2 v <;> cases b <;> rfl
  have hz := hH u1 u2 hne
  rw [Finset.sum_congr rfl (fun v _ => hterm v)] at hz
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hz
  have hsc : signZ b ≠ 0 := by cases b <;> decide
  have hcard0 : (Fintype.card β : ℤ) = 0 := (mul_eq_zero.mp hz).resolve_right hsc
  omega

lemma pow_two_mul (s : ℕ) : 2 ^ (2 * s) = 4 ^ s := by
  rw [pow_mul]; norm_num

lemma enc_bij (k : ℕ) :
    Function.Bijective (fun (m : Fin (2 ^ k)) (i : Fin k) => m.val.testBit i.val) := by
  have hinj : Function.Injective (fun (m : Fin (2 ^ k)) (i : Fin k) => m.val.testBit i.val) := by
    intro m1 m2 h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun h ⟨i, hi⟩
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le m1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le m2.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by simp⟩

lemma count_eq (s : ℕ) (G : Fin (2 ^ (2 * s)) → Fin (2 ^ (2 * s)) → Bool)
    (hH : IsHadamard G) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrep : Represents G C) (hc : C.gates.countP nonlinear ≤ s) :
    C.gates.countP nonlinear = s := by
  have hNL := circuit_hasNL C hfan hrep (le_refl (C.gates.countP nonlinear))
  have hpos : 0 < Fintype.card (Fin (2 ^ (2 * s))) := by simp
  have hle := hadamard_card_le hpos hH hNL
  rw [Fintype.card_fin, pow_two_mul] at hle
  by_contra hne
  have hlt : C.gates.countP nonlinear < s := lt_of_le_of_ne hc hne
  have := Nat.pow_lt_pow_right (by norm_num : 1 < 4) hlt
  omega

lemma fwd (s : ℕ) (G : Fin (2 ^ (2 * s)) → Fin (2 ^ (2 * s)) → Bool)
    (hH : IsHadamard G) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrep : Represents G C) (hc : C.gates.countP nonlinear ≤ s) :
    ∃ (row col : Equiv.Perm (Fin (2 ^ (2 * s)))) (Q R : Fin (2 ^ (2 * s)) → Bool),
      ∀ u v, G u v = xor (xor (Q u) (R v)) (dotB (2 * s) (row u) (col v)) := by
  have hNL : HasNL s G := circuit_hasNL C hfan hrep hc
  let e : Fin (4 ^ s) ≃ Fin (2 ^ (2 * s)) := finCongr (pow_two_mul s).symm
  let G' : Fin (4 ^ s) → Fin (4 ^ s) → Bool := fun u v => G (e u) (e v)
  have hH' : IsHadamard G' := by
    intro u1 u2 hne
    have := hH (e u1) (e u2) (fun h => hne (e.injective h))
    rw [← Fintype.sum_equiv e (fun v => signZ (xor (G' u1 v) (G' u2 v)))
      (fun v => signZ (xor (G (e u1) v) (G (e u2) v))) (fun _ => rfl)] at this
    exact this
  have hNL' : HasNL s G' := hasNL_comap hNL e e
  obtain ⟨α, β, φ, ψ, hIP⟩ := classification s G' hH' hNL'
  let P : (Fin (2 * s) → Bool) → (Fin (2 * s) → Bool) → Bool := fun f g =>
    z2b (∑ i : Fin (2 * s), b2z (f i) * b2z (g i))
  let Q : Fin (2 ^ (2 * s)) → Bool := fun u => α (e.symm u)
  let R : Fin (2 ^ (2 * s)) → Bool := fun v => β (e.symm v)
  let φ1 : Fin (2 ^ (2 * s)) → Fin (2 * s) → Bool := fun u => φ (e.symm u)
  let ψ1 : Fin (2 ^ (2 * s)) → Fin (2 * s) → Bool := fun v => ψ (e.symm v)
  have hG : ∀ u v, G u v = xor (xor (Q u) (R v)) (P (φ1 u) (ψ1 v)) := by
    intro u v
    have h1 := hIP (e.symm u) (e.symm v)
    simp only [G', Equiv.apply_symm_apply] at h1
    rw [h1, z2b_add, z2b_add, z2b_b2z, z2b_b2z]
  have hpos : 0 < Fintype.card (Fin (2 ^ (2 * s))) := by simp
  have hφinj : Function.Injective φ1 := by
    intro u1 u2 heq
    refine had_inj hpos hH (xor (Q u1) (Q u2)) (fun v => ?_)
    rw [hG u1 v, hG u2 v, heq]
    cases Q u1 <;> cases Q u2 <;> cases R v <;> cases P (φ1 u2) (ψ1 v) <;> rfl
  have hψinj : Function.Injective ψ1 := by
    intro v1 v2 heq
    refine had_inj hpos (hadamard_transpose (by simp) hH) (xor (R v1) (R v2)) (fun u => ?_)
    show G u v1 = xor (G u v2) (xor (R v1) (R v2))
    rw [hG u v1, hG u v2, heq]
    cases Q u <;> cases R v1 <;> cases R v2 <;> cases P (φ1 u) (ψ1 v2) <;> rfl
  have hcard : Fintype.card (Fin (2 ^ (2 * s))) = Fintype.card (Fin (2 * s) → Bool) := by simp
  let eφ := Equiv.ofBijective φ1 ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hφinj, hcard⟩)
  let eψ := Equiv.ofBijective ψ1 ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hψinj, hcard⟩)
  let eb := Equiv.ofBijective _ (enc_bij (2 * s))
  refine ⟨eφ.trans eb.symm, eψ.trans eb.symm, Q, R, fun u v => ?_⟩
  have hbr : ∀ i : Fin (2 * s), ((eφ.trans eb.symm) u).val.testBit i.val = φ1 u i := by
    intro i
    have h := congrFun (eb.apply_symm_apply (φ1 u)) i
    exact h
  have hbc : ∀ i : Fin (2 * s), ((eψ.trans eb.symm) v).val.testBit i.val = ψ1 v i := by
    intro i
    have h := congrFun (eb.apply_symm_apply (ψ1 v)) i
    exact h
  have hdot : dotB (2 * s) ((eφ.trans eb.symm) u) ((eψ.trans eb.symm) v) = P (φ1 u) (ψ1 v) := by
    simp only [dotB, P]
    rw [← z2b_sum_b2z_eq_card_mod2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [b2z_and, hbr i, hbc i]
  rw [hdot, hG u v]

lemma upper_pair_step2 {N : ℕ} (B : Build N) (wacc : ℕ) (hwacc : wacc < B.len) (m : ℕ)
    (ρ κ : Fin N → ℕ)
    (hBL : ∀ u v (i : ℕ) (hi : i < N), B.val u v i = decide (i = u.val))
    (hBR : ∀ u v (j : ℕ) (hj : j < N), B.val u v (N + j) = decide (j = v.val)) :
    ∃ (B' : Build N) (wf : ℕ),
      wf < B'.len ∧ B.len ≤ B'.len ∧ B'.cost = B.cost + 1 ∧
      (∀ u v w0, w0 < B.len → B'.val u v w0 = B.val u v w0) ∧
      (∀ u v, B'.val u v wf = xor (B.val u v wacc)
        (xor ((ρ u).testBit (2 * m) && (κ v).testBit (2 * m))
          ((ρ u).testBit (2 * m + 1) && (κ v).testBit (2 * m + 1)))) := by
  have hBL_of : ∀ (B1 : Build N), B.len ≤ B1.len → (∀ u v w0, w0 < B.len → B1.val u v w0 = B.val u v w0) →
      ∀ u v (i : ℕ) (hi : i < N), B1.val u v i = decide (i = u.val) := by
    intro B1 _ hold u v i hi
    have hiB : i < B.len := by simp [Build.len]; omega
    rw [hold u v i hiB, hBL u v i hi]
  have hBR_of : ∀ (B1 : Build N), B.len ≤ B1.len → (∀ u v w0, w0 < B.len → B1.val u v w0 = B.val u v w0) →
      ∀ u v (j : ℕ) (hj : j < N), B1.val u v (N + j) = decide (j = v.val) := by
    intro B1 _ hold u v j hj
    have hjB : N + j < B.len := by simp [Build.len]; omega
    rw [hold u v (N + j) hjB, hBR u v j hj]
  obtain ⟨B1, wu1, hwu1, hlen1, hcost1, hold1, hval1⟩ :=
    build_exists_left B (fun u => (ρ u).testBit (2 * m)) hBL
  obtain ⟨B2, wu2, hwu2, hlen2, hcost2, hold2, hval2⟩ :=
    build_exists_left B1 (fun u => (ρ u).testBit (2 * m + 1)) (hBL_of B1 hlen1 hold1)
  have hold20 : ∀ u v w0, w0 < B.len → B2.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold2 u v w0 (lt_of_lt_of_le hw0 hlen1), hold1 u v w0 hw0]
  obtain ⟨B3, wv1, hwv1, hlen3, hcost3, hold3, hval3⟩ :=
    build_exists_right B2 (fun v => (κ v).testBit (2 * m)) (hBR_of B2 (le_trans hlen1 hlen2) hold20)
  have hold30 : ∀ u v w0, w0 < B.len → B3.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold3 u v w0 (lt_of_lt_of_le hw0 (le_trans hlen1 hlen2)), hold20 u v w0 hw0]
  obtain ⟨B4, wv2, hwv2, hlen4, hcost4, hold4, hval4⟩ :=
    build_exists_right B3 (fun v => (κ v).testBit (2 * m + 1)) (hBR_of B3 (le_trans (le_trans hlen1 hlen2) hlen3) hold30)
  have hold40 : ∀ u v w0, w0 < B.len → B4.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold4 u v w0 (by omega), hold30 u v w0 hw0]
  obtain ⟨B5, wu12, hwu12, hlen5, hcost5, hold5, hval5⟩ :=
    build_exists_left B4 (fun u => (ρ u).testBit (2 * m) && (ρ u).testBit (2 * m + 1)) (hBL_of B4 (by omega) hold40)
  have hold50 : ∀ u v w0, w0 < B.len → B5.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold5 u v w0 (by omega), hold40 u v w0 hw0]
  obtain ⟨B6, wv12, hwv12, hlen6, hcost6, hold6, hval6⟩ :=
    build_exists_right B5 (fun v => (κ v).testBit (2 * m) && (κ v).testBit (2 * m + 1)) (hBR_of B5 (by omega) hold50)
  have hold60 : ∀ u v w0, w0 < B.len → B6.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold6 u v w0 (by omega), hold50 u v w0 hw0]
  obtain ⟨B7, wx1, hwx1, hlen7, hcost7, hold7, hval7⟩ := exists_xor B6 wu1 wv2 (by omega) (by omega)
  obtain ⟨B8, wx2, hwx2, hlen8, hcost8, hold8, hval8⟩ := exists_xor B7 wu2 wv1 (by omega) (by omega)
  obtain ⟨B9, wp, hwp, hlen9, hcost9, hold9, hval9⟩ := exists_and B8 wx1 wx2 (by omega) hwx2
  obtain ⟨B10, wuv, hwuv, hlen10, hcost10, hold10, hval10⟩ := exists_xor B9 wu12 wv12 (by omega) (by omega)
  obtain ⟨B11, wt, hwt, hlen11, hcost11, hold11, hval11⟩ := exists_xor B10 wuv wp hwuv (by omega)
  obtain ⟨B12, wf, hwf, hlen12, hcost12, hold12, hval12⟩ := exists_xor B11 wacc wt (by omega) hwt
  have hhold : ∀ u v w0, w0 < B.len → B12.val u v w0 = B.val u v w0 := fun u v w0 hw0 => by
    rw [hold12 u v w0 (by omega), hold11 u v w0 (by omega), hold10 u v w0 (by omega),
      hold9 u v w0 (by omega), hold8 u v w0 (by omega), hold7 u v w0 (by omega), hold60 u v w0 hw0]
  refine ⟨B12, wf, hwf, by omega, by omega, hhold, fun u v => ?_⟩
  have h6_u1 : B6.val u v wu1 = (ρ u).testBit (2 * m) := by
    rw [hold6 u v wu1 (by omega), hold5 u v wu1 (by omega), hold4 u v wu1 (by omega),
      hold3 u v wu1 (by omega), hold2 u v wu1 hwu1, hval1 u v]
  have h6_u2 : B6.val u v wu2 = (ρ u).testBit (2 * m + 1) := by
    rw [hold6 u v wu2 (by omega), hold5 u v wu2 (by omega), hold4 u v wu2 (by omega),
      hold3 u v wu2 hwu2, hval2 u v]
  have h6_v1 : B6.val u v wv1 = (κ v).testBit (2 * m) := by
    rw [hold6 u v wv1 (by omega), hold5 u v wv1 (by omega), hold4 u v wv1 hwv1, hval3 u v]
  have h6_v2 : B6.val u v wv2 = (κ v).testBit (2 * m + 1) := by
    rw [hold6 u v wv2 (by omega), hold5 u v wv2 hwv2, hval4 u v]
  have h6_u12 : B6.val u v wu12 = ((ρ u).testBit (2 * m) && (ρ u).testBit (2 * m + 1)) := by
    rw [hold6 u v wu12 hwu12, hval5 u v]
  have h6_v12 : B6.val u v wv12 = ((κ v).testBit (2 * m) && (κ v).testBit (2 * m + 1)) := hval6 u v
  rw [hval12 u v, hold11 u v wacc (by omega), hold10 u v wacc (by omega),
    hold9 u v wacc (by omega), hold8 u v wacc (by omega), hold7 u v wacc (by omega),
    hold60 u v wacc hwacc, hval11 u v, hval10 u v, hold9 u v wu12 (by omega),
    hold8 u v wu12 (by omega), hold7 u v wu12 (by omega), h6_u12,
    hold9 u v wv12 (by omega), hold8 u v wv12 (by omega), hold7 u v wv12 hwv12, h6_v12,
    hold10 u v wp hwp, hval9 u v, hold8 u v wx1 hwx1, hval7 u v, h6_u1, h6_v2,
    hval8 u v, hold7 u v wu2 (by omega), hold7 u v wv1 (by omega), h6_u2, h6_v1, pair_trick]

lemma dotB_eq (k : ℕ) {N : ℕ} (x y : Fin N) :
    dotB k x y = z2b (∑ i : Fin k, b2z (x.val.testBit i.val) * b2z (y.val.testBit i.val)) := by
  simp only [dotB]
  rw [← z2b_sum_b2z_eq_card_mod2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [b2z_and]

lemma conv (s : ℕ) (G : Fin (2 ^ (2 * s)) → Fin (2 ^ (2 * s)) → Bool)
    (h : ∃ (row col : Equiv.Perm (Fin (2 ^ (2 * s)))) (Q R : Fin (2 ^ (2 * s)) → Bool),
      ∀ u v, G u v = xor (xor (Q u) (R v)) (dotB (2 * s) (row u) (col v))) :
    ∃ C : Circuit, ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (2 ^ (2 * s) + 2 ^ (2 * s)) C ∧ Represents G C) ∧
      C.gates.countP nonlinear ≤ s := by
  obtain ⟨row, col, Q, R, hGf⟩ := h
  let ρ : Fin (2 ^ (2 * s)) → ℕ := fun u => (row u).val
  let κ : Fin (2 ^ (2 * s)) → ℕ := fun v => (col v).val
  let N := 2 ^ (2 * s)
  let B0 := Build.empty N
  have hB0_L : ∀ u v (i : ℕ) (hi : i < N), B0.val u v i = decide (i = u.val) :=
    Build.empty_val_left
  have hB0_R : ∀ u v (j : ℕ) (hj : j < N), B0.val u v (N + j) = decide (j = v.val) :=
    Build.empty_val_right
  have hloop : ∀ m ≤ s,
      ∃ (B : Build N) (w : ℕ),
        w < B.len ∧ B0.len ≤ B.len ∧ B.cost = m ∧
        (∀ u v w0, w0 < B0.len → B.val u v w0 = B0.val u v w0) ∧
        (∀ u v, B.val u v w = z2b (∑ j ∈ Finset.range m,
          (b2z ((ρ u).testBit (2 * j)) * b2z ((κ v).testBit (2 * j)) +
           b2z ((ρ u).testBit (2 * j + 1)) * b2z ((κ v).testBit (2 * j + 1))))) := by
    intro m
    induction m with
    | zero =>
      intro _
      obtain ⟨B1, w1, hw1, hlen1, hcost1, hold1, hval1⟩ := exists_false B0
      refine ⟨B1, w1, hw1, hlen1, ?_, hold1, fun u v => ?_⟩
      · rw [hcost1]; rfl
      · simp [hval1 u v, z2b]
    | succ m ih =>
      intro hm
      obtain ⟨B, wacc, hwacc, hlenB, hcostB, holdB, hvalB⟩ := ih (by omega)
      have hBL : ∀ u v (i : ℕ) (hi : i < N), B.val u v i = decide (i = u.val) := fun u v i hi => by
        rw [holdB u v i (by simp [B0, Build.empty, Build.len]; omega), hB0_L u v i hi]
      have hBR : ∀ u v (j : ℕ) (hj : j < N), B.val u v (N + j) = decide (j = v.val) := fun u v j hj => by
        rw [holdB u v (N + j) (by simp [B0, Build.empty, Build.len]; omega), hB0_R u v j hj]
      obtain ⟨B', wf, hwf, hlen', hcost', hold', hval'⟩ := upper_pair_step2 B wacc hwacc m ρ κ hBL hBR
      refine ⟨B', wf, hwf, le_trans hlenB hlen', by omega,
        fun u v w0 hw0 => by rw [hold' u v w0 (lt_of_lt_of_le hw0 hlenB), holdB u v w0 hw0],
        fun u v => ?_⟩
      rw [hval' u v, hvalB u v, Finset.sum_range_succ, z2b_add, z2b_add, ← b2z_and, ← b2z_and,
        z2b_b2z, z2b_b2z]
  obtain ⟨B, wacc, hwacc, hlenB, hcostB, holdB, hvalB⟩ := hloop s (le_refl s)
  have hBL : ∀ u v (i : ℕ) (hi : i < N), B.val u v i = decide (i = u.val) := fun u v i hi => by
    rw [holdB u v i (by simp [B0, Build.empty, Build.len]; omega), hB0_L u v i hi]
  have hBR : ∀ u v (j : ℕ) (hj : j < N), B.val u v (N + j) = decide (j = v.val) := fun u v j hj => by
    rw [holdB u v (N + j) (by simp [B0, Build.empty, Build.len]; omega), hB0_R u v j hj]
  obtain ⟨B1, wq, hwq, hlen1, hcost1, hold1, hval1⟩ := build_exists_left B Q hBL
  have hB1R : ∀ u v (j : ℕ) (hj : j < N), B1.val u v (N + j) = decide (j = v.val) := fun u v j hj => by
    have hj0 : N + j < B0.len := by simp [B0, Build.empty, Build.len]; omega
    rw [hold1 u v (N + j) (by omega), hBR u v j hj]
  obtain ⟨B2, wr, hwr, hlen2, hcost2, hold2, hval2⟩ := build_exists_right B1 R hB1R
  obtain ⟨B3, wqr, hwqr, hlen3, hcost3, hold3, hval3⟩ := exists_xor B2 wq wr (by omega) hwr
  obtain ⟨B4, wout, hwout, hlen4, hcost4, hold4, hval4⟩ := exists_xor B3 wqr wacc hwqr (by omega)
  refine ⟨⟨B4.gates, wout⟩, ⟨B4.hfan, ?_, ?_⟩, ?_⟩
  · intro j hj i hi
    have hj' : j < B4.gates.length := hj
    have hgt : gateAt ⟨B4.gates, wout⟩ j = B4.gates[j] := by
      simp [gateAt, List.getD, List.getElem?_eq_getElem hj']
    rw [hgt] at hi
    exact B4.hback j hj' i hi
  · intro u v
    have hval_out : (⟨B4.gates, wout⟩ : Circuit).eval (oneEach u v) = B4.val u v wout := rfl
    rw [hval_out, hval4 u v, hold3 u v wacc (by omega), hold2 u v wacc (by omega),
      hold1 u v wacc hwacc, hvalB u v, hval3 u v, hold2 u v wq hwq, hval1 u v, hval2 u v,
      hGf u v, dotB_eq]
    congr 1
    congr 1
    have hsum_pair :
        ∑ i : Fin (2 * s), b2z ((row u).val.testBit i.val) * b2z ((col v).val.testBit i.val) =
        ∑ j ∈ Finset.range s,
          (b2z ((ρ u).testBit (2 * j)) * b2z ((κ v).testBit (2 * j)) +
           b2z ((ρ u).testBit (2 * j + 1)) * b2z ((κ v).testBit (2 * j + 1))) := by
      let f : ℕ → ZMod 2 := fun i => b2z ((ρ u).testBit i) * b2z ((κ v).testBit i)
      exact (Fin.sum_univ_eq_sum_range f (2 * s)).trans (sum_range_two_mul f s)
    exact hsum_pair.symm
  · change B4.cost ≤ s
    omega

def chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma chi_add (x y : ZMod 2) : chi (x + y) = chi x * chi y := by
  fin_cases x <;> fin_cases y <;> decide

lemma chi_zero : chi 0 = 1 := by decide

lemma two_eq_zero (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma chi_sum {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ZMod 2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  refine Finset.induction_on s ?_ ?_
  · simp [chi]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma factor_eval (c d e : ZMod 2) :
    ∑ ab : ZMod 2 × ZMod 2, chi (c * ab.1 * ab.2 + d * ab.1 + e * ab.2) =
      if c = 1 then 2 * chi (d * e) else if d = 0 ∧ e = 0 then 4 else 0 := by
  rw [Fintype.sum_prod_type]
  fin_cases c <;> fin_cases d <;> fin_cases e <;> decide

lemma prod_formula {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ZMod 2 × ZMod 2 → ℤ) :
    ∑ o : ι → ZMod 2 × ZMod 2, ∏ q, g q (o q) = ∏ q, ∑ ab : ZMod 2 × ZMod 2, g q ab :=
  (Fintype.prod_sum g).symm

lemma flat {ι : Type} [Fintype ι] [DecidableEq ι] (D : (ι → ZMod 2 × ZMod 2) → ZMod 2)
    (hAC : ∀ a, a ≠ 0 → ∑ l, chi (D l + D (l + a)) = 0)
    (ℓ : (ι → ZMod 2 × ZMod 2) → ZMod 2) (hℓ : ∀ l m, ℓ (l + m) = ℓ l + ℓ m) :
    (∑ l, chi (D l + ℓ l)) ^ 2 = (Fintype.card (ι → ZMod 2 × ZMod 2) : ℤ) := by
  have hℓ0 : ℓ 0 = 0 := by
    have h := hℓ 0 0
    rw [add_zero, two_eq_zero] at h
    exact h
  have hf : ∀ l a, chi (D l + ℓ l) * chi (D (l + a) + ℓ (l + a)) =
      chi (ℓ a) * chi (D l + D (l + a)) := by
    intro l a
    rw [← chi_add, ← chi_add, hℓ]
    congr 1
    linear_combination two_eq_zero (ℓ l)
  rw [sq, Finset.sum_mul_sum]
  have hre : ∀ l, ∑ m, chi (D l + ℓ l) * chi (D m + ℓ m) =
      ∑ a, chi (ℓ a) * chi (D l + D (l + a)) := by
    intro l
    rw [← Fintype.sum_equiv (Equiv.addLeft l)
      (fun a => chi (D l + ℓ l) * chi (D (l + a) + ℓ (l + a)))
      (fun m => chi (D l + ℓ l) * chi (D m + ℓ m)) (fun a => rfl)]
    exact Finset.sum_congr rfl (fun a _ => hf l a)
  rw [Finset.sum_congr rfl (fun l _ => hre l), Finset.sum_comm]
  rw [Finset.sum_eq_single (0 : ι → ZMod 2 × ZMod 2)]
  · simp only [hℓ0, chi_zero, one_mul, add_zero, two_eq_zero]
    simp
  · intro a _ ha
    rw [← Finset.mul_sum, hAC a ha, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma prod_sq_forces {ι : Type} [Fintype ι] (f : ι → ℤ)
    (hf : ∀ q, f q ^ 2 = 4 ∨ f q ^ 2 = 16)
    (hprod : (∏ q, f q) ^ 2 = 4 ^ Fintype.card ι) :
    ∀ q, f q ^ 2 = 4 := by
  classical
  let m : ι → ℕ := fun q => if f q ^ 2 = 4 then 1 else 4
  have hm : ∀ q, f q ^ 2 = 4 * (m q : ℤ) := by
    intro q
    rcases hf q with h | h
    · simp [m, h]
    · have hne : ¬ f q ^ 2 = 4 := by rw [h]; norm_num
      simp only [m, hne, if_false]
      rw [h]; norm_num
  have h1 : (∏ q, f q) ^ 2 = 4 ^ Fintype.card ι * ((∏ q, m q : ℕ) : ℤ) := by
    rw [← Finset.prod_pow, Finset.prod_congr rfl (fun q _ => hm q), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    push_cast
    rfl
  rw [h1] at hprod
  have hpos : (0 : ℤ) < 4 ^ Fintype.card ι := by positivity
  have hm1 : ((∏ q, m q : ℕ) : ℤ) = 1 := by
    have h2 : (4 : ℤ) ^ Fintype.card ι * ((∏ q, m q : ℕ) : ℤ) = 4 ^ Fintype.card ι * 1 := by
      rw [hprod, mul_one]
    exact mul_left_cancel₀ (ne_of_gt hpos) h2
  have hm1' : (∏ q, m q) = 1 := by exact_mod_cast hm1
  intro q
  by_contra hq
  have hmq : m q = 4 := by simp [m, hq]
  have hle : m q ≤ ∏ q, m q :=
    Finset.single_le_prod' (fun i _ => by simp only [m]; split_ifs <;> norm_num) (Finset.mem_univ q)
  omega

lemma walsh {ι : Type} [Fintype ι] [DecidableEq ι] (r : ι → ℕ)
    (Φ : ι → (ι → ZMod 2 × ZMod 2) → ZMod 2) (κ : ι → ZMod 2)
    (c1 c2 : ι → ι → ZMod 2)
    (hc1 : ∀ p q, c1 p q ≠ 0 → r q < r p) (hc2 : ∀ p q, c2 p q ≠ 0 → r q < r p)
    (hΦ : ∀ p l, Φ p l = κ p + ((l p).1 + ∑ q, c1 p q * Φ q l) * ((l p).2 + ∑ q, c2 p q * Φ q l))
    (d : ι → ZMod 2)
    (hAC : ∀ a, a ≠ 0 → ∑ l, chi ((∑ q, d q * Φ q l) + (∑ q, d q * Φ q (l + a))) = 0) :
    ∀ p q, c1 p q = 0 ∧ c2 p q = 0 := by
  let T : (ι → ZMod 2 × ZMod 2) → (ι → ZMod 2 × ZMod 2) := fun l p =>
    ((l p).1 + ∑ q, c1 p q * Φ q l, (l p).2 + ∑ q, c2 p q * Φ q l)
  have hΦT : ∀ p l, Φ p l = κ p + (T l p).1 * (T l p).2 := fun p l => hΦ p l
  have hTinj : Function.Injective T := by
    intro l m hlm
    have key : ∀ n, ∀ p, r p = n → l p = m p ∧ Φ p l = Φ p m := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro p hp
        have hs1 : ∑ q, c1 p q * Φ q l = ∑ q, c1 p q * Φ q m := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases h : c1 p q = 0
          · rw [h, zero_mul, zero_mul]
          · rw [(ih (r q) (hp ▸ hc1 p q h) q rfl).2]
        have hs2 : ∑ q, c2 p q * Φ q l = ∑ q, c2 p q * Φ q m := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases h : c2 p q = 0
          · rw [h, zero_mul, zero_mul]
          · rw [(ih (r q) (hp ▸ hc2 p q h) q rfl).2]
        have hT := congrFun hlm p
        simp only [T, Prod.mk.injEq] at hT
        rw [hs1, hs2] at hT
        have e1 : (l p).1 = (m p).1 := add_right_cancel hT.1
        have e2 : (l p).2 = (m p).2 := add_right_cancel hT.2
        refine ⟨Prod.ext e1 e2, ?_⟩
        rw [hΦ p l, hΦ p m, hs1, hs2, e1, e2]
    funext p
    exact (key (r p) p rfl).1
  have hTbij : Function.Bijective T := Finite.injective_iff_bijective.mp hTinj
  have hreidx : ∀ F : (ι → ZMod 2 × ZMod 2) → ℤ, ∑ l, F (T l) = ∑ o, F o :=
    fun F => hTbij.sum_comp F
  have hcard : Fintype.card (ι → ZMod 2 × ZMod 2) = 4 ^ Fintype.card ι := by
    simp
  let D : (ι → ZMod 2 × ZMod 2) → ZMod 2 := fun l => ∑ q, d q * Φ q l
  have hDT : ∀ l, D l = ∑ q, (d q * κ q + d q * (T l q).1 * (T l q).2) := by
    intro l
    apply Finset.sum_congr rfl
    intro q _
    rw [hΦT q l]
    ring
  have hchi2 : ∀ x : ZMod 2, chi x ^ 2 = 1 := by
    intro x; fin_cases x <;> decide
  have hd : ∀ q, d q = 1 := by
    have h0 := flat D hAC (fun _ => 0) (fun _ _ => by ring)
    simp only [add_zero] at h0
    have hW : ∑ l, chi (D l) = ∏ q, ∑ ab : ZMod 2 × ZMod 2,
        chi (d q * κ q + d q * ab.1 * ab.2) := by
      rw [← prod_formula]
      rw [← hreidx (fun o => ∏ q, chi (d q * κ q + d q * (o q).1 * (o q).2))]
      apply Finset.sum_congr rfl
      intro l _
      rw [hDT l, chi_sum]
    have hfac : ∀ q, ∑ ab : ZMod 2 × ZMod 2, chi (d q * κ q + d q * ab.1 * ab.2) =
        chi (d q * κ q) * (if d q = 1 then 2 * chi (0 * 0) else if (0 : ZMod 2) = 0 ∧ (0 : ZMod 2) = 0 then 4 else 0) := by
      intro q
      rw [← factor_eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ab _
      rw [← chi_add]
      congr 1
      ring
    rw [hW, hcard] at h0
    have hsq := prod_sq_forces _ (fun q => by
      rw [hfac q, mul_pow, hchi2, one_mul]
      by_cases h1 : d q = 1
      · left; rw [if_pos h1, mul_zero, chi_zero]; norm_num
      · right; rw [if_neg h1, if_pos ⟨rfl, rfl⟩]; norm_num) h0
    intro q
    have h4 := hsq q
    rw [hfac q, mul_pow, hchi2, one_mul] at h4
    by_contra h1
    rw [if_neg h1, if_pos ⟨rfl, rfl⟩] at h4
    norm_num at h4
  have hstep : ∀ (p0 : ι) (cc : ι → ι → ZMod 2) (δ1 δ2 : ZMod 2),
      (δ1 = 1 ∧ δ2 = 0 ∧ cc = c1) ∨ (δ1 = 0 ∧ δ2 = 1 ∧ cc = c2) → ∀ q, cc p0 q = 0 := by
    intro p0 cc δ1 δ2 hδ
    have hccr : ∀ q, cc p0 q ≠ 0 → r q < r p0 := by
      rcases hδ with ⟨_, _, h3⟩ | ⟨_, _, h3⟩ <;> rw [h3]
      · exact hc1 p0
      · exact hc2 p0
    let ℓ : (ι → ZMod 2 × ZMod 2) → ZMod 2 := fun l => δ1 * (l p0).1 + δ2 * (l p0).2
    have hℓadd : ∀ l m, ℓ (l + m) = ℓ l + ℓ m := by
      intro l m
      simp only [ℓ, Pi.add_apply, Prod.fst_add, Prod.snd_add]
      ring
    have hℓT : ∀ l, ℓ l = δ1 * (T l p0).1 + δ2 * (T l p0).2 + ∑ q, cc p0 q * Φ q l := by
      intro l
      simp only [ℓ, T]
      rcases hδ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · rw [h1, h2, h3]
        linear_combination (-1 : ZMod 2) * two_eq_zero (∑ q, c1 p0 q * Φ q l)
      · rw [h1, h2, h3]
        linear_combination (-1 : ZMod 2) * two_eq_zero (∑ q, c2 p0 q * Φ q l)
    let f : ι → ZMod 2 × ZMod 2 → ZMod 2 := fun q ab =>
      (1 + cc p0 q) * κ q + ((1 + cc p0 q) * ab.1 * ab.2 +
        (if q = p0 then δ1 else 0) * ab.1 + (if q = p0 then δ2 else 0) * ab.2)
    have hsum : ∀ l, D l + ℓ l = ∑ q, f q (T l q) := by
      intro l
      have hD1 : D l = ∑ q, (κ q + (T l q).1 * (T l q).2) := by
        rw [hDT l]
        apply Finset.sum_congr rfl
        intro q _
        rw [hd q]; ring
      have hcc : ∑ q, cc p0 q * Φ q l = ∑ q, cc p0 q * (κ q + (T l q).1 * (T l q).2) := by
        apply Finset.sum_congr rfl
        intro q _
        rw [hΦT q l]
      have hite : δ1 * (T l p0).1 + δ2 * (T l p0).2 =
          ∑ q, ((if q = p0 then δ1 else 0) * (T l q).1 + (if q = p0 then δ2 else 0) * (T l q).2) := by
        rw [Finset.sum_add_distrib]
        simp
      rw [hℓT l, hD1, hcc, hite, ← add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _
      simp only [f]
      ring
    have hW : ∑ l, chi (D l + ℓ l) = ∏ q, ∑ ab : ZMod 2 × ZMod 2, chi (f q ab) := by
      rw [← prod_formula, ← hreidx (fun o => ∏ q, chi (f q (o q)))]
      apply Finset.sum_congr rfl
      intro l _
      rw [hsum l, chi_sum]
    have hfac : ∀ q, ∑ ab : ZMod 2 × ZMod 2, chi (f q ab) = chi ((1 + cc p0 q) * κ q) *
        (if 1 + cc p0 q = 1 then 2 * chi ((if q = p0 then δ1 else 0) * (if q = p0 then δ2 else 0))
         else if (if q = p0 then δ1 else 0) = 0 ∧ (if q = p0 then δ2 else 0) = 0 then 4 else 0) := by
      intro q
      rw [← factor_eval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ab _
      rw [← chi_add]
    have hp0 : cc p0 p0 = 0 := by
      by_contra h
      exact lt_irrefl _ (hccr p0 h)
    have h0 := flat D hAC ℓ hℓadd
    rw [hW, hcard] at h0
    have hsq := prod_sq_forces _ (fun q => by
      rw [hfac q, mul_pow, hchi2, one_mul]
      by_cases hq : q = p0
      · subst hq
        left
        rw [hp0, add_zero, if_pos rfl, mul_pow, hchi2]; norm_num
      · rw [if_neg hq, if_neg hq]
        have hz : (0 : ZMod 2) * 0 = 0 := by ring
        by_cases h1 : 1 + cc p0 q = 1
        · left; rw [if_pos h1, hz, chi_zero]; norm_num
        · right; rw [if_neg h1, if_pos ⟨rfl, rfl⟩]; norm_num) h0
    intro q
    by_cases hq : q = p0
    · rw [hq, hp0]
    · have h4 := hsq q
      rw [hfac q, mul_pow, hchi2, one_mul, if_neg hq, if_neg hq] at h4
      by_contra hne
      have h1 : ¬ (1 + cc p0 q = 1) := by
        intro h; apply hne; linear_combination h
      rw [if_neg h1, if_pos ⟨rfl, rfl⟩] at h4
      norm_num at h4
  intro p q
  exact ⟨hstep p c1 1 0 (Or.inl ⟨rfl, rfl, rfl⟩) q, hstep p c2 0 1 (Or.inr ⟨rfl, rfl, rfl⟩) q⟩

def wf (gs : List Gate) (l : List Bool) : List Bool :=
  gs.foldl (fun ws g => ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) l

lemma wf_length (gs : List Gate) (l : List Bool) : (wf gs l).length = l.length + gs.length :=
  foldl_length gs l

lemma wf_prefix (gs : List Gate) (l : List Bool) (i : ℕ) (hi : i < l.length) :
    (wf gs l).getD i false = l.getD i false := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    show (wf gs (l ++ [g.op.eval (g.inputs.map (fun i => l.getD i false))])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

lemma wf_append (gs1 gs2 : List Gate) (l : List Bool) : wf (gs1 ++ gs2) l = wf gs2 (wf gs1 l) := by
  simp [wf, List.foldl_append]

lemma wires_eq_wf (C : Circuit) (l : List Bool) : C.wires l = wf C.gates l := rfl

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD, List.getElem?_eq_getElem hj]

lemma val_gate (C : Circuit) (n : ℕ) (hback : ReadsBack n C) (l : List Bool) (hl : l.length = n)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires l).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (fun i => (C.wires l).getD i false)) := by
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j] :: C.gates.drop (j + 1)) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have hrb := hback j hj
  rw [gateAt_eq C j hj] at hrb ⊢
  set L := wf (C.gates.take j) l with hL
  have hLlen : L.length = n + j := by
    rw [hL, wf_length, hl, List.length_take, min_eq_left (le_of_lt hj)]
  set g := C.gates[j] with hg
  set val := g.op.eval (g.inputs.map (fun i => L.getD i false)) with hval
  have hW : C.wires l = wf (C.gates.drop (j + 1)) (L ++ [val]) := by
    have h1 : C.wires l = wf (C.gates.take j ++ (g :: C.gates.drop (j + 1))) l := by
      rw [wires_eq_wf]; exact congrArg (fun gs => wf gs l) hsplit
    rw [h1, wf_append]
    rfl
  have hagree : ∀ i, i < n + j + 1 → (C.wires l).getD i false = (L ++ [val]).getD i false := by
    intro i hi
    rw [hW, wf_prefix _ _ i (by simp; omega)]
  rw [hagree (n + j) (by omega)]
  have hlast : (L ++ [val]).getD (n + j) false = val := by
    rw [show n + j = L.length from hLlen.symm]
    simp [List.getD]
  rw [hlast, hval]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hrb i hi
  rw [hagree i (by omega)]
  simp [List.getD, List.getElem?_append_left (show i < L.length by omega)]

lemma val_input (C : Circuit) (l : List Bool) (i : ℕ) (hi : i < l.length) :
    (C.wires l).getD i false = l.getD i false := by
  rw [wires_eq_wf]; exact wf_prefix _ _ i hi

lemma val_big (C : Circuit) (l : List Bool) (w : ℕ) (hw : l.length + C.gates.length ≤ w) :
    (C.wires l).getD w false = false := by
  have hlen : (C.wires l).length = l.length + C.gates.length := by
    rw [wires_eq_wf, wf_length]
  simp [List.getD, List.getElem?_eq_none (show (C.wires l).length ≤ w by omega)]

def NLset (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun p => nonlinear (gateAt C p) = true)

def IsAffZ {n : ℕ} (A : (Fin n → Bool) → ZMod 2) : Prop :=
  ∀ x y, A x + A y = A (fun i => xor (x i) (y i)) + A (fun _ => false)

def vx (C : Circuit) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool := (C.wires (List.ofFn x)).getD w false

lemma decomp (C : Circuit) (n : ℕ) (hback : ReadsBack n C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ w, ∃ (A : (Fin n → Bool) → ZMod 2) (c : ℕ → ZMod 2), IsAffZ A ∧
      (∀ p, c p ≠ 0 → p ∈ NLset C ∧ n + p ≤ w) ∧
      ∀ x : Fin n → Bool, b2z (vx C x w) = A x + ∑ p ∈ NLset C, c p * b2z (vx C x (n + p)) := by
  intro w
  refine Nat.strong_induction_on w ?_
  intro w ih
  by_cases hwn : w < n
  · refine ⟨fun x => b2z (x ⟨w, hwn⟩), fun _ => 0, ?_, ?_, ?_⟩
    · intro x y
      simp only [b2z_xor]
      have : b2z false = 0 := rfl
      rw [this]; ring
    · intro p hp; exact absurd rfl hp
    · intro x
      simp only [zero_mul, Finset.sum_const_zero, add_zero, vx]
      rw [val_input C _ w (by simp; exact hwn)]
      simp [List.getD, List.getElem?_ofFn, hwn]
  by_cases hwl : n + C.gates.length ≤ w
  · refine ⟨fun _ => 0, fun _ => 0, fun x y => by ring, fun p hp => absurd rfl hp, ?_⟩
    intro x
    simp only [zero_mul, Finset.sum_const_zero, add_zero, vx]
    rw [val_big C _ w (by simp; omega)]
    rfl
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < C.gates.length := by omega
  have hvx : ∀ x : Fin n → Bool, vx C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map (vx C x)) := by
    intro x
    exact val_gate C n hback (List.ofFn x) (by simp) j hj
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hback j hj
  have hgmem : gateAt C j ∈ C.gates := by rw [gateAt_eq C j hj]; exact List.getElem_mem hj
  have hlen := hfan _ hgmem
  by_cases hnl : nonlinear (gateAt C j) = true
  · have hjmem : j ∈ NLset C := by
      simp [NLset, hj, hnl]
    refine ⟨fun _ => 0, fun p => if p = j then 1 else 0, fun x y => by ring, ?_, ?_⟩
    · intro p hp
      by_cases h : p = j
      · subst h; exact ⟨hjmem, le_refl _⟩
      · simp [h] at hp
    · intro x
      simp [ite_mul, Finset.sum_ite_eq', hjmem]
  · have hnlf : nonlinear (gateAt C j) = false := by simpa using hnl
    match hlist : (gateAt C j).inputs with
    | [] =>
      refine ⟨fun _ => b2z ((gateAt C j).op.eval []), fun _ => 0, fun x y => by ring,
        fun p hp => absurd rfl hp, ?_⟩
      intro x
      simp only [zero_mul, Finset.sum_const_zero, add_zero]
      rw [hvx x, hlist]
      rfl
    | [i1] =>
      have h1 : i1 < n + j := hrb i1 (by rw [hlist]; simp)
      obtain ⟨A1, cA, hA1, hcA, hdA⟩ := ih i1 h1
      obtain ⟨c0, c1, hf0⟩ := affine_gate_1 (fun x => (gateAt C j).op.eval [x])
      have hf : ∀ a, (gateAt C j).op.eval [a] = xor c0 (c1 && a) := hf0
      refine ⟨fun x => b2z c0 + b2z c1 * A1 x, fun p => b2z c1 * cA p, ?_, ?_, ?_⟩
      · intro x y
        have := hA1 x y
        linear_combination (b2z c1) * this
      · intro p hp
        have hp' : cA p ≠ 0 := by
          intro h; apply hp; show b2z c1 * cA p = 0; rw [h, mul_zero]
        obtain ⟨hm, hle⟩ := hcA p hp'
        exact ⟨hm, by omega⟩
      · intro x
        rw [hvx x, hlist]
        simp only [List.map_cons, List.map_nil]
        beta_reduce
        rw [hf, b2z_xor, b2z_and, hdA x, mul_add, Finset.mul_sum]
        simp only [mul_assoc]
        ring
    | [i1, i2] =>
      have h1 : i1 < n + j := hrb i1 (by rw [hlist]; simp)
      have h2 : i2 < n + j := hrb i2 (by rw [hlist]; simp)
      obtain ⟨A1, cA, hA1, hcA, hdA⟩ := ih i1 h1
      obtain ⟨A2, cB, hA2, hcB, hdB⟩ := ih i2 h2
      have hlin : xor (xor ((gateAt C j).op.eval [false, false]) ((gateAt C j).op.eval [false, true]))
          (xor ((gateAt C j).op.eval [true, false]) ((gateAt C j).op.eval [true, true])) = false := by
        simpa [nonlinear, hlist] using hnlf
      obtain ⟨c0, c1, c2, hf0⟩ := affine_gate_2 (fun x y => (gateAt C j).op.eval [x, y]) hlin
      have hf : ∀ a b, (gateAt C j).op.eval [a, b] = xor c0 (xor (c1 && a) (c2 && b)) := hf0
      refine ⟨fun x => b2z c0 + b2z c1 * A1 x + b2z c2 * A2 x,
        fun p => b2z c1 * cA p + b2z c2 * cB p, ?_, ?_, ?_⟩
      · intro x y
        have e1 := hA1 x y
        have e2 := hA2 x y
        linear_combination (b2z c1) * e1 + (b2z c2) * e2
      · intro p hp
        by_cases ha : cA p = 0
        · have hb : cB p ≠ 0 := by
            intro hb; apply hp; show b2z c1 * cA p + b2z c2 * cB p = 0; rw [ha, hb]; ring
          obtain ⟨hm, hle⟩ := hcB p hb
          exact ⟨hm, by omega⟩
        · obtain ⟨hm, hle⟩ := hcA p ha
          exact ⟨hm, by omega⟩
      · intro x
        rw [hvx x, hlist]
        simp only [List.map_cons, List.map_nil]
        beta_reduce
        rw [hf, b2z_xor, b2z_xor, b2z_and, b2z_and, hdA x, hdB x]
        have hs : ∑ p ∈ NLset C, (b2z c1 * cA p + b2z c2 * cB p) * b2z (vx C x (n + p)) =
            b2z c1 * ∑ p ∈ NLset C, cA p * b2z (vx C x (n + p)) +
            b2z c2 * ∑ p ∈ NLset C, cB p * b2z (vx C x (n + p)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p _
          ring
        rw [hs]
        ring
    | _ :: _ :: _ :: _ =>
      rw [hlist] at hlen
      simp at hlen

def PhiF {ι : Type} [Fintype ι] (κ : ι → ZMod 2) (c1 c2 : ι → ι → ZMod 2) :
    ℕ → ι → (ι → ZMod 2 × ZMod 2) → ZMod 2
  | 0, _, _ => 0
  | f + 1, p, l => κ p + ((l p).1 + ∑ q, c1 p q * PhiF κ c1 c2 f q l) *
      ((l p).2 + ∑ q, c2 p q * PhiF κ c1 c2 f q l)

lemma PhiF_stable {ι : Type} [Fintype ι] (r : ι → ℕ) (κ : ι → ZMod 2) (c1 c2 : ι → ι → ZMod 2)
    (hc1 : ∀ p q, c1 p q ≠ 0 → r q < r p) (hc2 : ∀ p q, c2 p q ≠ 0 → r q < r p)
    (l : ι → ZMod 2 × ZMod 2) :
    ∀ f p, r p < f → PhiF κ c1 c2 f p l = PhiF κ c1 c2 (r p + 1) p l := by
  intro f
  refine Nat.strong_induction_on f ?_
  intro f ih p hp
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  show κ p + ((l p).1 + ∑ q, c1 p q * PhiF κ c1 c2 f' q l) *
      ((l p).2 + ∑ q, c2 p q * PhiF κ c1 c2 f' q l) =
    κ p + ((l p).1 + ∑ q, c1 p q * PhiF κ c1 c2 (r p) q l) *
      ((l p).2 + ∑ q, c2 p q * PhiF κ c1 c2 (r p) q l)
  have key : ∀ q, r q < r p →
      PhiF κ c1 c2 f' q l = PhiF κ c1 c2 (r p) q l := by
    intro q hq
    rw [ih f' (by omega) q (by omega), ih (r p) (by omega) q hq]
  have s1 : ∑ q, c1 p q * PhiF κ c1 c2 f' q l = ∑ q, c1 p q * PhiF κ c1 c2 (r p) q l := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : c1 p q = 0
    · rw [h, zero_mul, zero_mul]
    · rw [key q (hc1 p q h)]
  have s2 : ∑ q, c2 p q * PhiF κ c1 c2 f' q l = ∑ q, c2 p q * PhiF κ c1 c2 (r p) q l := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : c2 p q = 0
    · rw [h, zero_mul, zero_mul]
    · rw [key q (hc2 p q h)]
  rw [s1, s2]

lemma exists_Phi {ι : Type} [Fintype ι] (r : ι → ℕ) (κ : ι → ZMod 2) (c1 c2 : ι → ι → ZMod 2)
    (hc1 : ∀ p q, c1 p q ≠ 0 → r q < r p) (hc2 : ∀ p q, c2 p q ≠ 0 → r q < r p) :
    ∃ Φ : ι → (ι → ZMod 2 × ZMod 2) → ZMod 2, ∀ p l,
      Φ p l = κ p + ((l p).1 + ∑ q, c1 p q * Φ q l) * ((l p).2 + ∑ q, c2 p q * Φ q l) := by
  refine ⟨fun p l => PhiF κ c1 c2 (r p + 1) p l, fun p l => ?_⟩
  show κ p + ((l p).1 + ∑ q, c1 p q * PhiF κ c1 c2 (r p) q l) *
      ((l p).2 + ∑ q, c2 p q * PhiF κ c1 c2 (r p) q l) = _
  have s1 : ∑ q, c1 p q * PhiF κ c1 c2 (r p) q l = ∑ q, c1 p q * PhiF κ c1 c2 (r q + 1) q l := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : c1 p q = 0
    · rw [h, zero_mul, zero_mul]
    · rw [PhiF_stable r κ c1 c2 hc1 hc2 l (r p) q (hc1 p q h)]
  have s2 : ∑ q, c2 p q * PhiF κ c1 c2 (r p) q l = ∑ q, c2 p q * PhiF κ c1 c2 (r q + 1) q l := by
    apply Finset.sum_congr rfl
    intro q _
    by_cases h : c2 p q = 0
    · rw [h, zero_mul, zero_mul]
    · rw [PhiF_stable r κ c1 c2 hc1 hc2 l (r p) q (hc2 p q h)]
  rw [s1, s2]

lemma chi_b2z (x : Bool) : chi (b2z x) = signZ x := by
  cases x <;> rfl

lemma card_filter_getD (f : Gate → Bool) (d : Gate) :
    ∀ gs : List Gate,
      ((Finset.range gs.length).filter (fun p => f (gs.getD p d) = true)).card = gs.countP f
  | [] => by simp
  | a :: gs => by
    rw [Finset.card_filter, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [← Finset.card_filter, card_filter_getD f d gs, List.countP_cons]

lemma nl_card (C : Circuit) : (NLset C).card = C.gates.countP nonlinear :=
  card_filter_getD nonlinear ⟨GateOp.or, []⟩ C.gates

def ohF {N : ℕ} (u v : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun i => decide (i = u)) (fun j => decide (j = v))

def eUF {N : ℕ} (u : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun i => decide (i = u)) (fun _ => false)

def eVF {N : ℕ} (v : Fin N) : Fin (N + N) → Bool :=
  Fin.append (fun _ => false) (fun j => decide (j = v))

lemma ohF_xor {N : ℕ} (u v : Fin N) : ohF u v = fun i => xor (eUF u i) (eVF v i) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [ohF, eUF, eVF, Fin.append_left, Bool.xor_false]
  · simp only [ohF, eUF, eVF, Fin.append_right, Bool.false_xor]

lemma ofFn_ohF {N : ℕ} (u v : Fin N) : List.ofFn (ohF u v) = oneEach u v := by
  simp [ohF, oneEach, List.ofFn_fin_append]

lemma aff_onehot {N : ℕ} (A : (Fin (N + N) → Bool) → ZMod 2) (hA : IsAffZ A) (u v : Fin N) :
    A (ohF u v) = (A (eUF u) + A (fun _ => false)) + A (eVF v) := by
  have h := hA (eUF u) (eVF v)
  rw [← ohF_xor] at h
  linear_combination (-1 : ZMod 2) * h - two_eq_zero (A (fun _ => false))

lemma aff (s : ℕ) (hs : 0 < s) (G : Fin (2 ^ (2 * s)) → Fin (2 ^ (2 * s)) → Bool)
    (hH : IsHadamard G) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hback : ReadsBack (2 ^ (2 * s) + 2 ^ (2 * s)) C)
    (hrep : Represents G C) (hc : C.gates.countP nonlinear ≤ s) :
    ∀ g ∈ C.gates, nonlinear g = true → ∀ w ∈ g.inputs,
      IsAff (fun x : Fin (2 ^ (2 * s) + 2 ^ (2 * s)) → Bool => (C.wires (List.ofFn x)).getD w false) := by
  classical
  have hcount : C.gates.countP nonlinear = s := count_eq s G hH C hfan hrep hc
  choose A cf hA hcf hdec using decomp C (2 ^ (2 * s) + 2 ^ (2 * s)) hback hfan
  let ι := {p // p ∈ NLset C}
  have hιcard : Fintype.card ι = s := by
    rw [Fintype.card_coe, nl_card, hcount]
  have hmemNL : ∀ p : ι, p.1 < C.gates.length ∧ nonlinear (gateAt C p.1) = true := by
    intro p
    have h := p.2
    simp only [NLset, Finset.mem_filter, Finset.mem_range] at h
    exact h
  have hlen2 : ∀ p : ι, (gateAt C p.1).inputs.length = 2 := by
    intro p
    have h := (hmemNL p).2
    simp only [nonlinear, Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have hnl2 : ∀ p : ι, xor (xor ((gateAt C p.1).op.eval [false, false]) ((gateAt C p.1).op.eval [false, true]))
      (xor ((gateAt C p.1).op.eval [true, false]) ((gateAt C p.1).op.eval [true, true])) = true := by
    intro p
    have h := (hmemNL p).2
    simp only [nonlinear, Bool.and_eq_true] at h
    exact h.2
  choose k0 k1 k2 hk using fun p : ι => nonlinear_gate_2 (fun x y => (gateAt C p.1).op.eval [x, y]) (hnl2 p)
  let opd : ι → Bool → ℕ := fun p k => (gateAt C p.1).inputs.getD (if k then 1 else 0) 0
  have hinputs : ∀ p : ι, (gateAt C p.1).inputs = [opd p false, opd p true] := by
    intro p
    have h := hlen2 p
    simp only [opd]
    match hl : (gateAt C p.1).inputs with
    | [i1, i2] => rfl
    | [] => rw [hl] at h; simp at h
    | [_] => rw [hl] at h; simp at h
    | _ :: _ :: _ :: _ => rw [hl] at h; simp at h
  have hopd_lt : ∀ p : ι, ∀ k, opd p k < (2 ^ (2 * s) + 2 ^ (2 * s)) + p.1 := by
    intro p k
    have hrb := hback p.1 (hmemNL p).1
    apply hrb
    rw [hinputs p]
    cases k <;> simp
  let a : ℕ → Fin (2 ^ (2 * s)) → ZMod 2 := fun w u => A w (eUF u) + A w (fun _ => false)
  let b : ℕ → Fin (2 ^ (2 * s)) → ZMod 2 := fun w v => A w (eVF v)
  let Y : Fin (2 ^ (2 * s)) → (ι → ZMod 2 × ZMod 2) := fun u p =>
    (a (opd p false) u + b2z (k1 p), a (opd p true) u + b2z (k2 p))
  let Z : Fin (2 ^ (2 * s)) → (ι → ZMod 2 × ZMod 2) := fun v p => (b (opd p false) v, b (opd p true) v)
  let c1 : ι → ι → ZMod 2 := fun p q => cf (opd p false) q.1
  let c2 : ι → ι → ZMod 2 := fun p q => cf (opd p true) q.1
  have hc1 : ∀ p q, c1 p q ≠ 0 → q.1 < p.1 := by
    intro p q h
    have h1 := (hcf (opd p false) q.1 h).2
    have h2 := hopd_lt p false
    omega
  have hc2 : ∀ p q, c2 p q ≠ 0 → q.1 < p.1 := by
    intro p q h
    have h1 := (hcf (opd p true) q.1 h).2
    have h2 := hopd_lt p true
    omega
  obtain ⟨Φ, hΦ⟩ := exists_Phi (fun q : ι => q.1) (fun p => b2z (k0 p)) c1 c2 hc1 hc2
  have hsumι : ∀ (w : ℕ) (F : ℕ → ZMod 2),
      ∑ q ∈ NLset C, cf w q * F q = ∑ q : ι, cf w q.1 * F q.1 := by
    intro w F
    exact (Finset.sum_coe_sort (NLset C) (fun q => cf w q * F q)).symm
  have hwire : ∀ (w : ℕ) (u v : Fin (2 ^ (2 * s))), b2z (vx C (ohF u v) w) =
      a w u + b w v + ∑ q : ι, cf w q.1 * b2z (vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + q.1)) := by
    intro w u v
    rw [hdec w (ohF u v), aff_onehot (A w) (hA w) u v, hsumι]
  have hgate : ∀ (p : ι) (u v : Fin (2 ^ (2 * s))), b2z (vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + p.1)) =
      b2z (k0 p) + (b2z (vx C (ohF u v) (opd p false)) + b2z (k1 p)) *
        (b2z (vx C (ohF u v) (opd p true)) + b2z (k2 p)) := by
    intro p u v
    have h := val_gate C (2 ^ (2 * s) + 2 ^ (2 * s)) hback (List.ofFn (ohF u v)) (by simp) p.1 (hmemNL p).1
    have h' : vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + p.1) =
        (gateAt C p.1).op.eval [vx C (ohF u v) (opd p false), vx C (ohF u v) (opd p true)] := by
      rw [vx, h, hinputs p]
      rfl
    have hk' : ∀ x y, (gateAt C p.1).op.eval [x, y] = xor (k0 p) ((xor x (k1 p)) && (xor y (k2 p))) :=
      hk p
    rw [h', hk', b2z_xor, b2z_and, b2z_xor, b2z_xor]
  have hval : ∀ (m : ℕ) (p : ι), p.1 = m → ∀ (u v : Fin (2 ^ (2 * s))),
      b2z (vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + p.1)) = Φ p (Y u + Z v) := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih p hr u v
    have hsum1 : ∑ q : ι, cf (opd p false) q.1 * b2z (vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + q.1)) =
        ∑ q : ι, c1 p q * Φ q (Y u + Z v) := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : c1 p q = 0
      · rw [show cf (opd p false) q.1 = c1 p q from rfl, h, zero_mul, zero_mul]
      · rw [ih q.1 (hr ▸ hc1 p q h) q rfl u v]
    have hsum2 : ∑ q : ι, cf (opd p true) q.1 * b2z (vx C (ohF u v) ((2 ^ (2 * s) + 2 ^ (2 * s)) + q.1)) =
        ∑ q : ι, c2 p q * Φ q (Y u + Z v) := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases h : c2 p q = 0
      · rw [show cf (opd p true) q.1 = c2 p q from rfl, h, zero_mul, zero_mul]
      · rw [ih q.1 (hr ▸ hc2 p q h) q rfl u v]
    rw [hgate p u v, hwire (opd p false) u v, hwire (opd p true) u v, hsum1, hsum2, hΦ p (Y u + Z v)]
    simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, Y, Z]
    ring
  let dd : ι → ZMod 2 := fun q => cf C.output q.1
  let D : (ι → ZMod 2 × ZMod 2) → ZMod 2 := fun l => ∑ q, dd q * Φ q l
  have hG : ∀ u v, b2z (G u v) = a C.output u + b C.output v + D (Y u + Z v) := by
    intro u v
    have h1 : G u v = vx C (ohF u v) C.output := by
      rw [← hrep u v]
      simp only [vx, Circuit.eval, ofFn_ohF]
    rw [h1, hwire C.output u v]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    rw [hval q.1 q rfl u v]
  have hNpos : 0 < Fintype.card (Fin (2 ^ (2 * s))) := by simp
  have hYinj : Function.Injective Y := by
    intro u1 u2 heq
    refine had_inj hNpos hH (z2b (a C.output u1 + a C.output u2)) (fun v => ?_)
    have e1 := hG u1 v
    have e2 := hG u2 v
    rw [heq] at e1
    rw [← z2b_b2z (G u1 v), e1, ← z2b_b2z (G u2 v), e2, ← z2b_add]
    congr 1
    linear_combination (-1 : ZMod 2) * two_eq_zero (a C.output u2)
  have hYbij : Function.Bijective Y := by
    refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hYinj, ?_⟩
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_prod, ZMod.card, hιcard]
    rw [pow_mul]; norm_num
  have hAC : ∀ l0, l0 ≠ 0 → ∑ l, chi (D l + D (l + l0)) = 0 := by
    intro l0 hl0
    have hshift : ∀ v : Fin (2 ^ (2 * s)), ∑ l, chi (D l + D (l + l0)) =
        ∑ u : Fin (2 ^ (2 * s)), chi (D (Y u + Z v) + D (Y u + Z v + l0)) := by
      intro v
      rw [← Fintype.sum_equiv (Equiv.addRight (Z v)) (fun l => chi (D (l + Z v) + D (l + Z v + l0)))
        (fun l => chi (D l + D (l + l0))) (fun l => rfl)]
      exact (hYbij.sum_comp (fun l => chi (D (l + Z v) + D (l + Z v + l0)))).symm
    have hrow : ∀ u : Fin (2 ^ (2 * s)), ∑ v : Fin (2 ^ (2 * s)), chi (D (Y u + Z v) + D (Y u + Z v + l0)) = 0 := by
      intro u
      obtain ⟨u', hu'⟩ := hYbij.2 (Y u + l0)
      have hne : u ≠ u' := by
        intro h
        apply hl0
        rw [← h] at hu'
        have h2 : Y u + l0 - Y u = Y u - Y u := by rw [← hu']
        simpa using h2
      have hterm : ∀ v, chi (D (Y u + Z v) + D (Y u + Z v + l0)) =
          chi (a C.output u + a C.output u') * signZ (xor (G u v) (G u' v)) := by
        intro v
        have e1 := hG u v
        have e2 := hG u' v
        rw [hu'] at e2
        rw [← chi_b2z, ← chi_add, b2z_xor]
        congr 1
        rw [show Y u + Z v + l0 = Y u + l0 + Z v by abel]
        linear_combination (-1 : ZMod 2) * e1 - e2 - two_eq_zero (a C.output u)
          - two_eq_zero (a C.output u') - two_eq_zero (b C.output v)
      rw [Finset.sum_congr rfl (fun v _ => hterm v), ← Finset.mul_sum, hH u u' hne, mul_zero]
    have htot : ∑ v : Fin (2 ^ (2 * s)), ∑ l, chi (D l + D (l + l0)) = 0 := by
      rw [Finset.sum_congr rfl (fun v _ => hshift v), Finset.sum_comm]
      exact Finset.sum_eq_zero (fun u _ => hrow u)
    rw [Finset.sum_const, Finset.card_univ] at htot
    rcases smul_eq_zero.mp htot with h | h
    · exact absurd h (ne_of_gt hNpos)
    · exact h
  have hW := walsh (fun q : ι => q.1) Φ (fun p => b2z (k0 p)) c1 c2 hc1 hc2 hΦ dd hAC
  intro g hg hgnl w hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hjNL : j ∈ NLset C := by
    simp only [NLset, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, by rw [gateAt_eq C j hj]; exact hgnl⟩
  let p : ι := ⟨j, hjNL⟩
  have hw' : w = opd p false ∨ w = opd p true := by
    have h : (gateAt C j).inputs = [opd p false, opd p true] := hinputs p
    rw [gateAt_eq C j hj] at h
    rw [h] at hw
    simpa using hw
  have hzero : ∀ q, cf w q = 0 := by
    intro q
    by_contra hq
    have hqNL := (hcf w q hq).1
    have hpq := hW p ⟨q, hqNL⟩
    rcases hw' with rfl | rfl
    · exact hq hpq.1
    · exact hq hpq.2
  have hWA : ∀ x, b2z (vx C x w) = A w x := by
    intro x
    rw [hdec w x]
    simp [hzero]
  intro x y
  show xor (vx C x w) (vx C y w) = xor (vx C (fun i => xor (x i) (y i)) w) (vx C (fun _ => false) w)
  rw [← z2b_b2z (xor (vx C x w) (vx C y w)), b2z_xor, hWA, hWA, hA w x y, ← hWA, ← hWA, ← b2z_xor,
    z2b_b2z]

end PEqualNP.Outside.L_meta_25663

theorem PEqualNP.Outside.L_meta_25663 : (∀ s : ℕ, 0 < s →
  let k := 2 * s
  let N := 2 ^ k
  let dot := fun (x y : Fin N) =>
    ((Finset.univ : Finset (Fin k)).filter (fun i =>
      x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∀ G : Fin N → Fin N → Bool,
  (∀ u v : Fin N, u ≠ v →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G v c)).card = N) →
  let represents := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
    PEqualNP.Represents.Represents G C
  ((∃ C, represents C ∧ C.gates.countP nonlinear ≤ s) ↔
    ∃ (row col : Equiv.Perm (Fin N)) (Q R : Fin N → Bool),
      ∀ u v, G u v = xor (xor (Q u) (R v)) (dot (row u) (col v))) ∧
  (∀ C, represents C → C.gates.countP nonlinear ≤ s →
    C.gates.countP nonlinear = s ∧
    ∀ g ∈ C.gates, nonlinear g = true → ∀ w ∈ g.inputs,
      let W := fun (x : Fin (N+N) → Bool) => (C.wires (List.ofFn x)).getD w false
      ∀ x y, xor (W x) (W y) =
        xor (W (fun i => xor (x i) (y i))) (W (fun _ => false)))) := by
  intro s hs k N dot nl G hG represents
  have hH : L_meta_25663.IsHadamard G := L_meta_25663.had_of_half G hG
  refine ⟨⟨fun ⟨C, hC, hc⟩ => L_meta_25663.fwd s G hH C hC.1 hC.2.2 hc, fun h => L_meta_25663.conv s G h⟩, ?_⟩
  intro C hC hc
  exact ⟨L_meta_25663.count_eq s G hH C hC.1 hC.2.2 hc, L_meta_25663.aff s hs G hH C hC.1 hC.2.1 hC.2.2 hc⟩
