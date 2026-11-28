import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.Outside.L_pcx_410

def prodFinEquiv (a b : ℕ) : Fin a × Fin b ≃ Fin (a * b) where
  toFun p := ⟨p.1.val * b + p.2.val, by
    have h1 : p.1.val + 1 ≤ a := p.1.isLt
    have h2 : (p.1.val + 1) * b ≤ a * b := Nat.mul_le_mul_right b h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega⟩
  invFun i :=
    have hb : 0 < b := by
      cases b with
      | zero => simp at i; exact Fin.elim0 i
      | succ _ => exact Nat.succ_pos _
    (⟨i.val / b, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq i.isLt (Nat.mul_comm a b))⟩,
     ⟨i.val % b, Nat.mod_lt _ hb⟩)
  left_inv p := by
    rcases p with ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hb : 0 < b := Nat.lt_of_le_of_lt (Nat.zero_le y) hy
    ext
    · dsimp only
      rw [Nat.mul_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hy, Nat.add_zero]
    · dsimp only
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  right_inv i := by
    ext
    dsimp only
    rw [Nat.mul_comm, Nat.div_add_mod]

def boolNotEquiv : Equiv.Perm Bool where
  toFun := (!·)
  invFun := (!·)
  left_inv := Bool.not_not
  right_inv := Bool.not_not

lemma xor_not_l (a b : Bool) : xor (!a) b = !(xor a b) := by
  cases a <;> cases b <;> rfl

lemma sum_fin3 (f : Fin 3 → ℕ) : (∑ j : Fin 3, f j) = f 0 + f 1 + f 2 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Fin.reduceEq, or_self, not_false_eq_true, Nat.add_assoc]

def cycPerm : (m : ℕ) → Equiv.Perm (Fin m)
  | 0 => Equiv.refl (Fin 0)
  | n + 1 =>
    { toFun := fun i => ⟨(i.val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
      invFun := fun i => ⟨(i.val + n) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩
      left_inv := fun i => by
        ext
        dsimp only
        by_cases h : i.val + 1 < n + 1
        · rw [Nat.mod_eq_of_lt h, show i.val + 1 + n = i.val + (n + 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        · have hi : i.val = n := by omega
          rw [hi, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_succ_self n)]
      right_inv := fun i => by
        ext
        dsimp only
        by_cases h : i.val = 0
        · rw [h, Nat.zero_add, Nat.mod_eq_of_lt (Nat.lt_succ_self n), Nat.mod_self]
        · have h1 : (i.val + n) % (n + 1) = i.val - 1 := by
            rw [show i.val + n = (i.val - 1) + (n + 1) by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)]
          rw [h1, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt] }

lemma cycPerm_const (m : ℕ) (g : Fin m → Bool) (hg : ∀ i, g (cycPerm m i) = g i)
    (a b : Fin m) : g a = g b := by
  cases m with
  | zero => exact Fin.elim0 a
  | succ n =>
    have key : ∀ (j : ℕ) (hj : j < n + 1), g ⟨j, hj⟩ = g ⟨0, Nat.succ_pos n⟩ := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hstep : cycPerm (n + 1) ⟨j, by omega⟩ = ⟨j + 1, hj⟩ := by
          ext
          exact Nat.mod_eq_of_lt hj
        rw [← hstep, hg, ih (by omega)]
    rw [key a.val a.isLt, key b.val b.isLt]

lemma fiberPerm {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) :
    ∃ ρ : Equiv.Perm α, (∀ a, f (ρ a) = f a) ∧
      ∀ g : α → Bool, (∀ a, g (ρ a) = g a) → ∀ a b, f a = f b → g a = g b := by
  classical
  let F := Equiv.sigmaFiberEquiv f
  let φ : ∀ b, {a // f a = b} ≃ Fin (Fintype.card {a // f a = b}) := fun b => Fintype.equivFin _
  let τ : ∀ b, Equiv.Perm {a // f a = b} := fun b => (φ b).trans ((cycPerm _).trans (φ b).symm)
  let ρ : Equiv.Perm α := F.symm.trans ((Equiv.sigmaCongrRight τ).trans F)
  have hρ : ∀ b (a : {a // f a = b}), ρ a.1 = (τ b a).1 := by
    rintro b ⟨a, rfl⟩
    rfl
  refine ⟨ρ, fun a => ?_, fun g hg a b hab => ?_⟩
  · rw [hρ (f a) ⟨a, rfl⟩]
    exact (τ (f a) ⟨a, rfl⟩).2
  · have := cycPerm_const _ (fun i => g ((φ (f b)).symm i).1) (fun i => by
      have h1 := hg ((φ (f b)).symm i).1
      rw [hρ (f b)] at h1
      simpa [τ] using h1) (φ (f b) ⟨a, hab⟩) (φ (f b) ⟨b, rfl⟩)
    simpa using this

lemma negate_half {A : Type} [Fintype A] (f : A → Bool) (e : Equiv.Perm A)
    (h : ∀ x, f (e x) = !(f x)) :
    2 * (Finset.univ.filter (fun x => f x = true)).card = Fintype.card A := by
  classical
  have eq : (Finset.univ.filter (fun x => f x = true)).card =
      (Finset.univ.filter (fun x => f x = false)).card := by
    apply Finset.card_equiv e
    intro x
    cases hh : f x <;> simp [h, hh]
  have add : (Finset.univ.filter (fun x => f x = true)).card +
      (Finset.univ.filter (fun x => f x = false)).card = Fintype.card A := by
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : A, (1 : ℕ) := Finset.sum_congr rfl (fun x _ => by cases f x <;> simp)
      _ = _ := by simp
  omega

def triCost6 (f0 t0 f1 t1 f2 t2 : Bool) : ℕ :=
  (if f0 ≠ t0 then 1 else 0) + (if f1 ≠ t1 then 1 else 0) + (if f2 ≠ t2 then 1 else 0) +
  (if f0 = t1 then 1 else 0) + (if f1 = t2 then 1 else 0) + (if f2 = t0 then 1 else 0)

lemma triCost6_ge_one (f0 t0 f1 t1 f2 t2 : Bool) : 1 ≤ triCost6 f0 t0 f1 t1 f2 t2 := by
  revert f0 t0 f1 t1 f2 t2
  decide

lemma triCost6_eq_one_diag (v0 v1 v2 : Bool) :
    triCost6 v0 v0 v1 v1 v2 v2 = 1 ↔ ¬ (v0 = v1 ∧ v1 = v2) := by
  revert v0 v1 v2
  decide

def nae3 (a b c : Bool) : Prop := ¬ (a = b ∧ b = c)

lemma nae3_xor (s a b c : Bool) : nae3 (xor s a) (xor s b) (xor s c) ↔ nae3 a b c := by
  unfold nae3
  revert s a b c
  decide

lemma nand_iff_nae (a b z : Bool) :
    (nae3 a b z ∧ nae3 a z false ∧ nae3 b z false) ↔ z = !(a && b) := by
  unfold nae3
  revert a b z
  decide

lemma xor_via_nand (a b : Bool) : (!(!(!a && b) && !(a && !b))) = xor a b := by
  revert a b
  decide

def next3 (j : Fin 3) : Fin 3 := ⟨(j.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def prev3 (j : Fin 3) : Fin 3 := ⟨(j.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

lemma prev3_next3 (j : Fin 3) : prev3 (next3 j) = j := by
  revert j
  decide

lemma next3_prev3 (j : Fin 3) : next3 (prev3 j) = j := by
  revert j
  decide

section LayeredCore

variable {r : ℕ} {LVar LTri LEdge ICarry : Type}

abbrev HubCore (LVar LTri LEdge ICarry : Type) :=
  LVar ⊕ ((LEdge × Bool) ⊕ (ICarry ⊕ (ICarry ⊕ (LTri × Fin 3))))

abbrev CornerCore (LTri : Type) := Bool × (LTri × Fin 3)

abbrev LCore (LVar LTri LEdge ICarry : Type) :=
  HubCore LVar LTri LEdge ICarry ⊕ CornerCore LTri

abbrev LSite (LVar LTri LEdge ICarry : Type) :=
  LCore LVar LTri LEdge ICarry × Bool

abbrev Site (r : ℕ) (LVar LTri LEdge ICarry : Type) :=
  Fin (r + 1) × LSite LVar LTri LEdge ICarry

def hubInfo (triVar : Fin (r + 1) → LTri → Fin 3 → LVar)
    (triSign : Fin (r + 1) → LTri → Fin 3 → Bool)
    (edgeEnd : Fin (r + 1) → LEdge → Bool → LVar × Bool)
    (carrySrc carryDst : ICarry → LVar)
    (ℓ : Fin (r + 1)) : HubCore LVar LTri LEdge ICarry → LVar × Bool
  | .inl v => (v, false)
  | .inr (.inl (e, side)) => edgeEnd ℓ e side
  | .inr (.inr (.inl c)) => (carrySrc c, false)
  | .inr (.inr (.inr (.inl c))) => (carryDst c, false)
  | .inr (.inr (.inr (.inr (t, j)))) => (triVar ℓ t j, !(triSign ℓ t j))

def flipLSite : LSite LVar LTri LEdge ICarry → LSite LVar LTri LEdge ICarry
  | (c, s) => (c, !s)

def flipSite : Site r LVar LTri LEdge ICarry → Site r LVar LTri LEdge ICarry
  | (ℓ, u) => (ℓ, flipLSite u)

lemma flipSite_inv : Function.Involutive (@flipSite r LVar LTri LEdge ICarry) := by
  rintro ⟨ℓ, c, s⟩
  simp [flipSite, flipLSite]

def tauTo : Site r LVar LTri LEdge ICarry → Site r LVar LTri LEdge ICarry
  | (ℓ, .inl (.inl v), s) => (ℓ, .inl (.inl v), !s)
  | (ℓ, .inl (.inr (.inl (e, side))), s) => (ℓ, .inl (.inr (.inl (e, !side))), s)
  | (ℓ, .inl (.inr (.inr (.inl c))), s) =>
      if h : ℓ.val < r then
        (⟨ℓ.val + 1, by omega⟩, .inl (.inr (.inr (.inr (.inl c)))), !s)
      else
        (ℓ, .inl (.inr (.inr (.inl c))), !s)
  | (ℓ, .inl (.inr (.inr (.inr (.inl c)))), s) =>
      if h : 0 < ℓ.val then
        (⟨ℓ.val - 1, by omega⟩, .inl (.inr (.inr (.inl c))), !s)
      else
        (ℓ, .inl (.inr (.inr (.inr (.inl c)))), !s)
  | (ℓ, .inl (.inr (.inr (.inr (.inr tj)))), s) => (ℓ, .inr (false, tj), s)
  | (ℓ, .inr (false, tj), s) => (ℓ, .inl (.inr (.inr (.inr (.inr tj)))), s)
  | (ℓ, .inr (true, (t, j)), s) => (ℓ, .inr (true, (t, next3 j)), s)

def tauInv : Site r LVar LTri LEdge ICarry → Site r LVar LTri LEdge ICarry
  | (ℓ, .inl (.inl v), s) => (ℓ, .inl (.inl v), !s)
  | (ℓ, .inl (.inr (.inl (e, side))), s) => (ℓ, .inl (.inr (.inl (e, !side))), s)
  | (ℓ, .inl (.inr (.inr (.inl c))), s) =>
      if h : ℓ.val < r then
        (⟨ℓ.val + 1, by omega⟩, .inl (.inr (.inr (.inr (.inl c)))), !s)
      else
        (ℓ, .inl (.inr (.inr (.inl c))), !s)
  | (ℓ, .inl (.inr (.inr (.inr (.inl c)))), s) =>
      if h : 0 < ℓ.val then
        (⟨ℓ.val - 1, by omega⟩, .inl (.inr (.inr (.inl c))), !s)
      else
        (ℓ, .inl (.inr (.inr (.inr (.inl c)))), !s)
  | (ℓ, .inl (.inr (.inr (.inr (.inr tj)))), s) => (ℓ, .inr (false, tj), s)
  | (ℓ, .inr (false, tj), s) => (ℓ, .inl (.inr (.inr (.inr (.inr tj)))), s)
  | (ℓ, .inr (true, (t, j)), s) => (ℓ, .inr (true, (t, prev3 j)), s)

def tauSite : Equiv.Perm (Site r LVar LTri LEdge ICarry) where
  toFun := tauTo
  invFun := tauInv
  left_inv x := by
    rcases x with ⟨ℓ, ((v | (⟨e, side⟩ | (c | (c | tj)))) | ⟨b, ⟨t, j⟩⟩), s⟩
    · simp [tauTo, tauInv]
    · simp [tauTo, tauInv]
    · dsimp only [tauTo]
      split_ifs with h
      · have hpos : 0 < ℓ.val + 1 := Nat.succ_pos _
        dsimp only [tauInv]
        simp only [hpos, ↓reduceDIte]
        exact Prod.ext (Fin.ext (by dsimp only; omega)) (Prod.ext rfl (Bool.not_not s))
      · dsimp only [tauInv]
        simp only [h, ↓reduceDIte, Bool.not_not]
    · dsimp only [tauTo]
      split_ifs with h
      · have hlt : ℓ.val - 1 < r := by omega
        dsimp only [tauInv]
        simp only [hlt, ↓reduceDIte]
        exact Prod.ext (Fin.ext (by dsimp only; omega)) (Prod.ext rfl (Bool.not_not s))
      · dsimp only [tauInv]
        simp only [h, ↓reduceDIte, Bool.not_not]
    · simp [tauTo, tauInv]
    · cases b <;> simp [tauTo, tauInv, prev3_next3]
  right_inv x := by
    rcases x with ⟨ℓ, ((v | (⟨e, side⟩ | (c | (c | tj)))) | ⟨b, ⟨t, j⟩⟩), s⟩
    · simp [tauTo, tauInv]
    · simp [tauTo, tauInv]
    · dsimp only [tauInv]
      split_ifs with h
      · have hpos : 0 < ℓ.val + 1 := Nat.succ_pos _
        dsimp only [tauTo]
        simp only [hpos, ↓reduceDIte]
        exact Prod.ext (Fin.ext (by dsimp only; omega)) (Prod.ext rfl (Bool.not_not s))
      · dsimp only [tauTo]
        simp only [h, ↓reduceDIte, Bool.not_not]
    · dsimp only [tauInv]
      split_ifs with h
      · have hlt : ℓ.val - 1 < r := by omega
        dsimp only [tauTo]
        simp only [hlt, ↓reduceDIte]
        exact Prod.ext (Fin.ext (by dsimp only; omega)) (Prod.ext rfl (Bool.not_not s))
      · dsimp only [tauTo]
        simp only [h, ↓reduceDIte, Bool.not_not]
    · simp [tauTo, tauInv]
    · cases b <;> simp [tauTo, tauInv, next3_prev3]

lemma tauSite_local (p : Site r LVar LTri LEdge ICarry) :
    p.1.val ≤ (tauSite p).1.val + 1 ∧ (tauSite p).1.val ≤ p.1.val + 1 := by
  rcases p with ⟨ℓ, ((v | (⟨e, side⟩ | (c | (c | tj)))) | ⟨b, ⟨t, j⟩⟩), s⟩
  · dsimp only [tauSite, Equiv.coe_fn_mk, tauTo]; omega
  · dsimp only [tauSite, Equiv.coe_fn_mk, tauTo]; omega
  · dsimp only [tauSite, Equiv.coe_fn_mk, tauTo]; split_ifs <;> dsimp only <;> omega
  · dsimp only [tauSite, Equiv.coe_fn_mk, tauTo]; split_ifs <;> dsimp only <;> omega
  · dsimp only [tauSite, Equiv.coe_fn_mk, tauTo]; omega
  · cases b <;> dsimp only [tauSite, Equiv.coe_fn_mk, tauTo] <;> omega

def ValidSpec (triVar : Fin (r + 1) → LTri → Fin 3 → LVar)
    (triSign : Fin (r + 1) → LTri → Fin 3 → Bool)
    (edgeEnd : Fin (r + 1) → LEdge → Bool → LVar × Bool)
    (carrySrc carryDst : ICarry → LVar)
    (V : Fin (r + 1) → LVar → Bool) : Prop :=
  (∀ ℓ e, xor (edgeEnd ℓ e false).2 (V ℓ (edgeEnd ℓ e false).1) ≠
          xor (edgeEnd ℓ e true).2 (V ℓ (edgeEnd ℓ e true).1)) ∧
  (∀ (ℓ : Fin (r + 1)) (h : ℓ.val < r) (c : ICarry),
    V ℓ (carrySrc c) = V ⟨ℓ.val + 1, by omega⟩ (carryDst c)) ∧
  (∀ ℓ t, nae3
    (xor (triSign ℓ t 0) (V ℓ (triVar ℓ t 0)))
    (xor (triSign ℓ t 1) (V ℓ (triVar ℓ t 1)))
    (xor (triSign ℓ t 2) (V ℓ (triVar ℓ t 2))))

def siteVal (triVar : Fin (r + 1) → LTri → Fin 3 → LVar)
    (triSign : Fin (r + 1) → LTri → Fin 3 → Bool)
    (edgeEnd : Fin (r + 1) → LEdge → Bool → LVar × Bool)
    (carrySrc carryDst : ICarry → LVar)
    (V : Fin (r + 1) → LVar → Bool) : Site r LVar LTri LEdge ICarry → Bool
  | (ℓ, .inl hc, s) =>
      let p := hubInfo triVar triSign edgeEnd carrySrc carryDst ℓ hc
      xor s (xor p.2 (V ℓ p.1))
  | (ℓ, .inr (_, (t, j)), s) =>
      xor s (xor (triSign ℓ t j) (V ℓ (triVar ℓ t j)))

lemma siteVal_flip (triVar : Fin (r + 1) → LTri → Fin 3 → LVar)
    (triSign : Fin (r + 1) → LTri → Fin 3 → Bool)
    (edgeEnd : Fin (r + 1) → LEdge → Bool → LVar × Bool)
    (carrySrc carryDst : ICarry → LVar)
    (V : Fin (r + 1) → LVar → Bool) (x : Site r LVar LTri LEdge ICarry) :
    siteVal triVar triSign edgeEnd carrySrc carryDst V (flipSite x) =
      !(siteVal triVar triSign edgeEnd carrySrc carryDst V x) := by
  rcases x with ⟨ℓ, (hc | ⟨b, t, j⟩), s⟩ <;>
    simp [siteVal, flipSite, flipLSite]

end LayeredCore

section Layered

variable {r : ℕ} {LVar LTri LEdge ICarry : Type}
  [Fintype LVar] [DecidableEq LVar]
  [Fintype LTri] [DecidableEq LTri]
  [Fintype LEdge] [DecidableEq LEdge]
  [Fintype ICarry] [DecidableEq ICarry]

def crossCount {n : ℕ} (π : Equiv.Perm (Fin n)) (q : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => decide (i.val < q) ≠ decide ((π i).val < q))).card

omit [DecidableEq LVar] [DecidableEq LTri] [DecidableEq LEdge] [DecidableEq ICarry] in
lemma cross_le_three_mul (πSite : Equiv.Perm (Site r LVar LTri LEdge ICarry))
    (hloc : ∀ p, p.1.val ≤ (πSite p).1.val + 1 ∧ (πSite p).1.val ≤ p.1.val + 1)
    (eL : LSite LVar LTri LEdge ICarry ≃ Fin (Fintype.card (LSite LVar LTri LEdge ICarry)))
    (q : ℕ) :
    let S := Fintype.card (LSite LVar LTri LEdge ICarry)
    let eFin : Site r LVar LTri LEdge ICarry ≃ Fin ((r + 1) * S) :=
      (Equiv.prodCongr (Equiv.refl (Fin (r + 1))) eL).trans (prodFinEquiv (r + 1) S)
    crossCount (eFin.symm.trans (πSite.trans eFin)) q ≤ 3 * S := by
  classical
  intro S eFin
  by_cases hS : S = 0
  · have hn : (r + 1) * S = 0 := by rw [hS, Nat.mul_zero]
    unfold crossCount
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun i _ =>
      Fin.elim0 (hn ▸ i))]
    exact Nat.zero_le _
  · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
    let ℓ0 := q / S
    have hq_lo : ℓ0 * S ≤ q := Nat.div_mul_le_self q S
    have hq_hi : q < (ℓ0 + 1) * S := by
      rw [Nat.add_mul, Nat.one_mul]
      have hdm : S * ℓ0 + q % S = q := Nat.div_add_mod q S
      have hml : q % S < S := Nat.mod_lt q hSpos
      rw [Nat.mul_comm] at hdm
      omega
    let π := eFin.symm.trans (πSite.trans eFin)
    have hcard_eq : crossCount π q =
        (Finset.univ.filter (fun p : Site r LVar LTri LEdge ICarry =>
          decide ((eFin p).val < q) ≠ decide ((eFin (πSite p)).val < q))).card := by
      unfold crossCount
      apply Finset.card_equiv eFin.symm
      intro i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, π, Equiv.trans_apply, Equiv.apply_symm_apply]
      exact Iff.rfl
    rw [hcard_eq]
    let band : Finset (Fin (r + 1)) :=
      Finset.univ.filter (fun ℓ : Fin (r + 1) => ℓ0 ≤ ℓ.val + 1 ∧ ℓ.val ≤ ℓ0 + 1)
    have hsub : Finset.univ.filter (fun p : Site r LVar LTri LEdge ICarry =>
          decide ((eFin p).val < q) ≠ decide ((eFin (πSite p)).val < q)) ⊆
        band ×ˢ (Finset.univ : Finset (LSite LVar LTri LEdge ICarry)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, Finset.mem_univ _⟩
      · by_contra hlt
        have hp1 : p.1.val + 1 < ℓ0 := by omega
        have hp2 : (πSite p).1.val + 1 ≤ ℓ0 := by have := (hloc p).2; omega
        have hv1 : (eFin p).val < q := by
          have hv : (eFin p).val = p.1.val * S + (eL p.2).val := rfl
          have hmul : (p.1.val + 1) * S ≤ ℓ0 * S := Nat.mul_le_mul_right S (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hmul
          have hltS := (eL p.2).isLt
          omega
        have hv2 : (eFin (πSite p)).val < q := by
          have hv : (eFin (πSite p)).val = (πSite p).1.val * S + (eL (πSite p).2).val := rfl
          have hmul : ((πSite p).1.val + 1) * S ≤ ℓ0 * S := Nat.mul_le_mul_right S hp2
          rw [Nat.add_mul, Nat.one_mul] at hmul
          have hltS := (eL (πSite p).2).isLt
          omega
        exact hp.2 (by rw [decide_eq_true hv1, decide_eq_true hv2])
      · by_contra hgt
        have hp1 : ℓ0 + 1 < p.1.val := by omega
        have hp2 : ℓ0 + 1 ≤ (πSite p).1.val := by have := (hloc p).1; omega
        have hv1 : ¬ ((eFin p).val < q) := by
          have hv : (eFin p).val = p.1.val * S + (eL p.2).val := rfl
          have hmul : (ℓ0 + 1) * S ≤ p.1.val * S := Nat.mul_le_mul_right S (by omega)
          omega
        have hv2 : ¬ ((eFin (πSite p)).val < q) := by
          have hv : (eFin (πSite p)).val = (πSite p).1.val * S + (eL (πSite p).2).val := rfl
          have hmul : (ℓ0 + 1) * S ≤ (πSite p).1.val * S := Nat.mul_le_mul_right S hp2
          omega
        exact hp.2 (by rw [decide_eq_false hv1, decide_eq_false hv2])
    have hband : band.card ≤ 3 := by
      have hinj : band.card ≤ (Finset.univ : Finset (Fin 3)).card := by
        apply Finset.card_le_card_of_injOn (fun ℓ : Fin (r + 1) =>
          (⟨(ℓ.val + 1 - ℓ0) % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3))
        · intro _ _; exact Finset.mem_univ _
        · intro a ha b hb hab
          rw [Finset.mem_coe, Finset.mem_filter] at ha hb
          have hv : (a.val + 1 - ℓ0) % 3 = (b.val + 1 - ℓ0) % 3 := congrArg Fin.val hab
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
          exact Fin.ext (by omega)
      simpa using hinj
    calc
      _ ≤ (band ×ˢ (Finset.univ : Finset (LSite LVar LTri LEdge ICarry))).card :=
          Finset.card_le_card hsub
      _ = band.card * S := by rw [Finset.card_product, Finset.card_univ]
      _ ≤ 3 * S := Nat.mul_le_mul_right S hband

theorem compileLayered
    (triVar : Fin (r + 1) → LTri → Fin 3 → LVar)
    (triSign : Fin (r + 1) → LTri → Fin 3 → Bool)
    (edgeEnd : Fin (r + 1) → LEdge → Bool → LVar × Bool)
    (carrySrc carryDst : ICarry → LVar) :
    let S := Fintype.card (LSite LVar LTri LEdge ICarry)
    let n := (r + 1) * S
    let T := 2 * (r + 1) * Fintype.card LTri
    ∃ (eFin : Site r LVar LTri LEdge ICarry ≃ Fin n)
      (σ τ : Equiv.Perm (Fin n)),
      (∀ q : ℕ, crossCount σ q + crossCount τ q ≤ 6 * S) ∧
      let V := Bool × Fin n
      let Y := V → Bool
      let cost := fun (y : Y) =>
        (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, σ i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card
      (∀ y : Y, T ≤ cost y) ∧
      (∀ y : Y, cost y = T →
        (Finset.univ.filter (fun p : V => y p = true)).card = n ∧
        ∀ x : Site r LVar LTri LEdge ICarry,
          y (false, eFin (flipSite x)) = !(y (false, eFin x))) ∧
      (∀ y : Y, cost y = T ↔
        ∃ A : Fin (r + 1) → LVar → Bool,
          ValidSpec triVar triSign edgeEnd carrySrc carryDst A ∧
          y = fun p => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2)) := by
  classical
  intro S n T
  let eL : LSite LVar LTri LEdge ICarry ≃ Fin S := Fintype.equivFin _
  let eFin : Site r LVar LTri LEdge ICarry ≃ Fin n :=
    (Equiv.prodCongr (Equiv.refl (Fin (r + 1))) eL).trans (prodFinEquiv (r + 1) S)
  let hVar := fun (ℓ : Fin (r + 1)) (hc : HubCore LVar LTri LEdge ICarry) =>
    (hubInfo triVar triSign edgeEnd carrySrc carryDst ℓ hc).1
  let hPol := fun (ℓ : Fin (r + 1)) (hc : HubCore LVar LTri LEdge ICarry) =>
    (hubInfo triVar triSign edgeEnd carrySrc carryDst ℓ hc).2
  choose ρ hρ_eq hρ_tr using fun ℓ : Fin (r + 1) => fiberPerm (hVar ℓ)
  let twist : Fin (r + 1) → Equiv.Perm (HubCore LVar LTri LEdge ICarry × Bool) := fun ℓ =>
    { toFun := fun p => (p.1, xor (hPol ℓ p.1) p.2)
      invFun := fun p => (p.1, xor (hPol ℓ p.1) p.2)
      left_inv := fun ⟨c, s⟩ => by
        dsimp only
        cases hPol ℓ c <;> cases s <;> simp
      right_inv := fun ⟨c, s⟩ => by
        dsimp only
        cases hPol ℓ c <;> cases s <;> simp }
  let σHub : Fin (r + 1) → Equiv.Perm (HubCore LVar LTri LEdge ICarry × Bool) := fun ℓ =>
    (twist ℓ).trans ((Equiv.prodCongr (ρ ℓ) (Equiv.refl Bool)).trans (twist ℓ))
  let σCorner : Equiv.Perm (CornerCore LTri × Bool) :=
    Equiv.prodCongr (Equiv.prodCongr boolNotEquiv (Equiv.refl _)) (Equiv.refl Bool)
  let σLayer : Fin (r + 1) → Equiv.Perm (LSite LVar LTri LEdge ICarry) := fun ℓ =>
    (Equiv.sumProdDistrib _ _ _).trans
      ((Equiv.sumCongr (σHub ℓ) σCorner).trans (Equiv.sumProdDistrib _ _ _).symm)
  let σSite : Equiv.Perm (Site r LVar LTri LEdge ICarry) :=
    { toFun := fun p => (p.1, σLayer p.1 p.2)
      invFun := fun p => (p.1, (σLayer p.1).symm p.2)
      left_inv := fun ⟨ℓ, u⟩ => by simp
      right_inv := fun ⟨ℓ, u⟩ => by simp }
  let τSite : Equiv.Perm (Site r LVar LTri LEdge ICarry) := tauSite
  let σ : Equiv.Perm (Fin n) := eFin.symm.trans (σSite.trans eFin)
  let τ : Equiv.Perm (Fin n) := eFin.symm.trans (τSite.trans eFin)
  have hσ_loc : ∀ p : Site r LVar LTri LEdge ICarry,
      p.1.val ≤ (σSite p).1.val + 1 ∧ (σSite p).1.val ≤ p.1.val + 1 := fun p => by
    dsimp only [σSite, Equiv.coe_fn_mk]
    omega
  have hcross : ∀ q : ℕ, crossCount σ q + crossCount τ q ≤ 6 * S := fun q => by
    have h1 : crossCount σ q ≤ 3 * S := cross_le_three_mul σSite hσ_loc eL q
    have h2 : crossCount τ q ≤ 3 * S := cross_le_three_mul τSite tauSite_local eL q
    omega
  refine ⟨eFin, σ, τ, hcross, ?_⟩
  intro V Y cost
  let pull : Y → (Bool × Site r LVar LTri LEdge ICarry → Bool) := fun y u => y (u.1, eFin u.2)
  have hcost_pull : ∀ y : Y, cost y =
      (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
        pull y (false, x) ≠ pull y (true, x))).card +
      (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
        pull y (false, x) ≠ pull y (true, σSite x))).card +
      (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
        pull y (false, x) = pull y (true, τSite x))).card := by
    intro y
    dsimp only [cost, pull]
    have c0 : (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, i))).card =
        (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
          y (false, eFin x) ≠ y (true, eFin x))).card := by
      apply Finset.card_equiv eFin.symm
      intro i
      simp
    have c1 : (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, σ i))).card =
        (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
          y (false, eFin x) ≠ y (true, eFin (σSite x)))).card := by
      apply Finset.card_equiv eFin.symm
      intro i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    have c2 : (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card =
        (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
          y (false, eFin x) = y (true, eFin (τSite x)))).card := by
      apply Finset.card_equiv eFin.symm
      intro i
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, τ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [c0, c1, c2]
  let term02 : (Bool × Site r LVar LTri LEdge ICarry → Bool) → Site r LVar LTri LEdge ICarry → ℕ :=
    fun z x => (if z (false, x) ≠ z (true, x) then 1 else 0) +
      (if z (false, x) = z (true, τSite x) then 1 else 0)
  let hubSum : (Bool × Site r LVar LTri LEdge ICarry → Bool) → ℕ := fun z =>
    ∑ ℓ : Fin (r + 1), ∑ hc : HubCore LVar LTri LEdge ICarry, ∑ s : Bool,
      term02 z (ℓ, .inl hc, s)
  let linkSum : (Bool × Site r LVar LTri LEdge ICarry → Bool) → ℕ := fun z =>
    ∑ ℓ : Fin (r + 1), ∑ tj : LTri × Fin 3, ∑ s : Bool,
      term02 z (ℓ, .inr (false, tj), s)
  let triBlock : (Bool × Site r LVar LTri LEdge ICarry → Bool) →
      Fin (r + 1) → LTri → Bool → ℕ := fun z ℓ t s =>
    triCost6
      (z (false, (ℓ, .inr (true, (t, 0)), s))) (z (true, (ℓ, .inr (true, (t, 0)), s)))
      (z (false, (ℓ, .inr (true, (t, 1)), s))) (z (true, (ℓ, .inr (true, (t, 1)), s)))
      (z (false, (ℓ, .inr (true, (t, 2)), s))) (z (true, (ℓ, .inr (true, (t, 2)), s)))
  let triSum : (Bool × Site r LVar LTri LEdge ICarry → Bool) → ℕ := fun z =>
    ∑ ℓ : Fin (r + 1), ∑ t : LTri, ∑ s : Bool, triBlock z ℓ t s
  have hsplit : ∀ z : Bool × Site r LVar LTri LEdge ICarry → Bool,
      (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry => z (false, x) ≠ z (true, x))).card +
      (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry => z (false, x) = z (true, τSite x))).card =
        hubSum z + linkSum z + triSum z := by
    intro z
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    change (∑ x : Site r LVar LTri LEdge ICarry, term02 z x) = _
    rw [Fintype.sum_prod_type]
    have hlayer : ∀ ℓ : Fin (r + 1),
        (∑ u : LSite LVar LTri LEdge ICarry, term02 z (ℓ, u)) =
        (∑ hc : HubCore LVar LTri LEdge ICarry, ∑ s : Bool, term02 z (ℓ, .inl hc, s)) +
        (∑ tj : LTri × Fin 3, ∑ s : Bool, term02 z (ℓ, .inr (false, tj), s)) +
        (∑ t : LTri, ∑ s : Bool, triBlock z ℓ t s) := by
      intro ℓ
      rw [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool]
      have htri : (∑ tj : LTri × Fin 3, ∑ s : Bool, term02 z (ℓ, .inr (true, tj), s)) =
          ∑ t : LTri, ∑ s : Bool, triBlock z ℓ t s := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [sum_fin3]
        have h0 : τSite (ℓ, .inr (true, (t, 0)), s) = (ℓ, .inr (true, (t, 1)), s) := rfl
        have h1 : τSite (ℓ, .inr (true, (t, 1)), s) = (ℓ, .inr (true, (t, 2)), s) := rfl
        have h2 : τSite (ℓ, .inr (true, (t, 2)), s) = (ℓ, .inr (true, (t, 0)), s) := rfl
        dsimp only [term02, triBlock, triCost6]
        simp only [h0, h1, h2]
        omega
      rw [htri]
      omega
    simp_rw [hlayer, Finset.sum_add_distrib]
    rfl
  have hT_sum : T = ∑ _ℓ : Fin (r + 1), ∑ _t : LTri, ∑ _s : Bool, (1 : ℕ) := by
    have hbool : (∑ _s : Bool, (1 : ℕ)) = 2 := by decide
    simp_rw [hbool]
    have hltri : (∑ _t : LTri, (2 : ℕ)) = Fintype.card LTri * 2 := by
      rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ]
    simp_rw [hltri]
    rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
    dsimp only [T]
    rw [Nat.mul_comm (Fintype.card LTri) 2, ← Nat.mul_assoc, Nat.mul_comm (r + 1) 2]
  have htri_ge : ∀ z, T ≤ triSum z := by
    intro z
    rw [hT_sum]
    refine Finset.sum_le_sum fun ℓ _ => Finset.sum_le_sum fun t _ =>
      Finset.sum_le_sum fun s _ => triCost6_ge_one _ _ _ _ _ _
  have hlb : ∀ y : Y, T ≤ cost y := by
    intro y
    rw [hcost_pull]
    have hs := hsplit (pull y)
    have ht := htri_ge (pull y)
    omega
  have hσ_hub_eval : ∀ (ℓ : Fin (r + 1)) (hc : HubCore LVar LTri LEdge ICarry) (s : Bool),
      σHub ℓ (hc, s) = (ρ ℓ hc, xor (hPol ℓ (ρ ℓ hc)) (xor (hPol ℓ hc) s)) := by
    intro ℓ hc s
    dsimp only [σHub, twist, Equiv.trans_apply, Equiv.coe_fn_mk]
    rw [Equiv.prodCongr_apply]
    rfl
  have hσ_hub_key : ∀ (ℓ : Fin (r + 1)) (hc : HubCore LVar LTri LEdge ICarry) (s : Bool),
      hVar ℓ ((σHub ℓ (hc, s)).1) = hVar ℓ hc ∧
      xor (hPol ℓ ((σHub ℓ (hc, s)).1)) (σHub ℓ (hc, s)).2 = xor (hPol ℓ hc) s := by
    intro ℓ hc s
    rw [hσ_hub_eval]
    refine ⟨hρ_eq ℓ hc, ?_⟩
    cases hPol ℓ (ρ ℓ hc) <;> cases hPol ℓ hc <;> cases s <;> rfl
  have hσ_hub_const : ∀ (ℓ : Fin (r + 1)) (g : HubCore LVar LTri LEdge ICarry × Bool → Bool),
      (∀ p, g (σHub ℓ p) = g p) →
      ∀ p q, hVar ℓ p.1 = hVar ℓ q.1 → xor (hPol ℓ p.1) p.2 = xor (hPol ℓ q.1) q.2 →
        g p = g q := by
    intro ℓ g hg ⟨c1, s1⟩ ⟨c2, s2⟩ hv hp
    let g' : Bool → HubCore LVar LTri LEdge ICarry → Bool := fun s c => g (twist ℓ (c, s))
    have h1 : ∀ s c, g' s (ρ ℓ c) = g' s c := by
      intro s c
      have hstep := hg (twist ℓ (c, s))
      have htw : σHub ℓ (twist ℓ (c, s)) = twist ℓ (ρ ℓ c, s) := by
        dsimp only [σHub, Equiv.trans_apply]
        have hl : twist ℓ (twist ℓ (c, s)) = (c, s) := (twist ℓ).left_inv (c, s)
        rw [hl, Equiv.prodCongr_apply]
        rfl
      rw [htw] at hstep
      exact hstep
    have heq := hρ_tr ℓ (g' (xor (hPol ℓ c1) s1)) (h1 _) c1 c2 hv
    have htw1 : twist ℓ (c1, xor (hPol ℓ c1) s1) = (c1, s1) := (twist ℓ).left_inv (c1, s1)
    have htw2 : twist ℓ (c2, xor (hPol ℓ c1) s1) = (c2, s2) := by
      rw [hp]
      exact (twist ℓ).left_inv (c2, s2)
    simpa [g', htw1, htw2] using heq
  have hchar : ∀ y : Y, cost y = T ↔
      ∃ A : Fin (r + 1) → LVar → Bool,
        ValidSpec triVar triSign edgeEnd carrySrc carryDst A ∧
        y = fun p => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2) := by
    intro y
    constructor
    · intro hcost
      rw [hcost_pull] at hcost
      have hs := hsplit (pull y)
      have ht := htri_ge (pull y)
      have he1 : (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
          pull y (false, x) ≠ pull y (true, σSite x))).card = 0 := by omega
      have hhub0 : hubSum (pull y) = 0 := by omega
      have hlink0 : linkSum (pull y) = 0 := by omega
      have htri_eq : triSum (pull y) = T := by omega
      have he1_all : ∀ x, pull y (false, x) = pull y (true, σSite x) := by
        intro x
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at he1
        exact Classical.not_not.mp (he1 (Finset.mem_univ x))
      have hhub_all : ∀ ℓ hc s, term02 (pull y) (ℓ, .inl hc, s) = 0 := by
        intro ℓ hc s
        have h1 := Finset.sum_eq_zero_iff.mp hhub0 ℓ (Finset.mem_univ ℓ)
        have h2 := Finset.sum_eq_zero_iff.mp h1 hc (Finset.mem_univ hc)
        exact Finset.sum_eq_zero_iff.mp h2 s (Finset.mem_univ s)
      have hlink_all : ∀ ℓ tj s, term02 (pull y) (ℓ, .inr (false, tj), s) = 0 := by
        intro ℓ tj s
        have h1 := Finset.sum_eq_zero_iff.mp hlink0 ℓ (Finset.mem_univ ℓ)
        have h2 := Finset.sum_eq_zero_iff.mp h1 tj (Finset.mem_univ tj)
        exact Finset.sum_eq_zero_iff.mp h2 s (Finset.mem_univ s)
      have htri_one : ∀ ℓ t s, triBlock (pull y) ℓ t s = 1 := by
        have h1 : ∀ ℓ ∈ (Finset.univ : Finset (Fin (r + 1))),
            (∑ t : LTri, ∑ s : Bool, (1 : ℕ)) ≤ ∑ t : LTri, ∑ s : Bool, triBlock (pull y) ℓ t s :=
          fun ℓ _ => Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun s _ =>
            triCost6_ge_one _ _ _ _ _ _
        have heq1 := (Finset.sum_eq_sum_iff_of_le h1).mp (hT_sum.symm.trans htri_eq.symm)
        intro ℓ t s
        have h2 : ∀ t ∈ (Finset.univ : Finset LTri),
            (∑ s : Bool, (1 : ℕ)) ≤ ∑ s : Bool, triBlock (pull y) ℓ t s :=
          fun t _ => Finset.sum_le_sum fun s _ => triCost6_ge_one _ _ _ _ _ _
        have heq2 := (Finset.sum_eq_sum_iff_of_le h2).mp (heq1 ℓ (Finset.mem_univ ℓ))
        have h3 : ∀ s ∈ (Finset.univ : Finset Bool), 1 ≤ triBlock (pull y) ℓ t s :=
          fun s _ => triCost6_ge_one _ _ _ _ _ _
        exact ((Finset.sum_eq_sum_iff_of_le h3).mp (heq2 t (Finset.mem_univ t)) s (Finset.mem_univ s)).symm
      have he0_hub : ∀ ℓ hc s, pull y (false, (ℓ, .inl hc, s)) = pull y (true, (ℓ, .inl hc, s)) := by
        intro ℓ hc s
        have h := hhub_all ℓ hc s
        dsimp only [term02] at h
        split_ifs at h with h1 <;> first | exact Classical.not_not.mp h1 | omega
      have he2_hub : ∀ ℓ hc s,
          pull y (false, (ℓ, .inl hc, s)) ≠ pull y (true, τSite (ℓ, .inl hc, s)) := by
        intro ℓ hc s
        have h := hhub_all ℓ hc s
        dsimp only [term02] at h
        split_ifs at h with _ h2 <;> first | exact h2 | omega
      have he0_link : ∀ ℓ tj s,
          pull y (false, (ℓ, .inr (false, tj), s)) = pull y (true, (ℓ, .inr (false, tj), s)) := by
        intro ℓ tj s
        have h := hlink_all ℓ tj s
        dsimp only [term02] at h
        split_ifs at h with h1 <;> first | exact Classical.not_not.mp h1 | omega
      have he2_link : ∀ ℓ tj s,
          pull y (false, (ℓ, .inr (false, tj), s)) ≠ pull y (true, τSite (ℓ, .inr (false, tj), s)) := by
        intro ℓ tj s
        have h := hlink_all ℓ tj s
        dsimp only [term02] at h
        split_ifs at h with _ h2 <;> first | exact h2 | omega
      have hσ_cor : ∀ ℓ b tj s,
          σSite (ℓ, .inr (b, tj), s) = (ℓ, .inr (!b, tj), s) := by
        intro ℓ b tj s
        rfl
      have he0_tri : ∀ ℓ tj s,
          pull y (false, (ℓ, .inr (true, tj), s)) = pull y (true, (ℓ, .inr (true, tj), s)) ∧
          pull y (false, (ℓ, .inr (true, tj), s)) = pull y (false, (ℓ, .inr (false, tj), s)) := by
        intro ℓ tj s
        have h1 := he1_all (ℓ, .inr (true, tj), s)
        have h2 := he1_all (ℓ, .inr (false, tj), s)
        rw [hσ_cor] at h1 h2
        simp only [Bool.not_true, Bool.not_false] at h1 h2
        have h3 := he0_link ℓ tj s
        exact ⟨h1.trans (h3.symm.trans h2), h1.trans h3.symm⟩
      have he0_all : ∀ x, pull y (false, x) = pull y (true, x) := by
        rintro ⟨ℓ, (hc | ⟨b, tj⟩), s⟩
        · exact he0_hub ℓ hc s
        · cases b
          · exact he0_link ℓ tj s
          · exact (he0_tri ℓ tj s).1
      let A : Fin (r + 1) → LVar → Bool := fun ℓ v => pull y (false, (ℓ, .inl (.inl v), false))
      have hant : ∀ ℓ v s, pull y (false, (ℓ, .inl (.inl v), s)) = xor s (A ℓ v) := by
        intro ℓ v s
        cases s
        · rw [Bool.false_xor]
        · have hne := he2_hub ℓ (.inl v) false
          have htau : τSite (ℓ, .inl (.inl v), false) = (ℓ, .inl (.inl v), true) := rfl
          rw [htau, ← he0_all] at hne
          change A ℓ v ≠ pull y (false, (ℓ, .inl (.inl v), true)) at hne
          cases hA : A ℓ v <;> cases hT : pull y (false, (ℓ, .inl (.inl v), true)) <;>
            simp [hA, hT] at hne ⊢
      have hhub_val : ∀ ℓ hc s,
          pull y (false, (ℓ, .inl hc, s)) =
            siteVal triVar triSign edgeEnd carrySrc carryDst A (ℓ, .inl hc, s) := by
        intro ℓ hc s
        have hinv : ∀ p : HubCore LVar LTri LEdge ICarry × Bool,
            pull y (false, (ℓ, .inl (σHub ℓ p).1, (σHub ℓ p).2)) =
              pull y (false, (ℓ, .inl p.1, p.2)) := by
          intro p
          have h1 := he1_all (ℓ, .inl p.1, p.2)
          have h2 : σSite (ℓ, .inl p.1, p.2) = (ℓ, .inl (σHub ℓ p).1, (σHub ℓ p).2) := rfl
          rw [h2, ← he0_all] at h1
          exact h1.symm
        have heq := hσ_hub_const ℓ (fun p => pull y (false, (ℓ, .inl p.1, p.2))) hinv
          (hc, s) (.inl (hVar ℓ hc), xor (hPol ℓ hc) s) rfl (by simp [hPol, hubInfo])
        rw [heq, hant]
        dsimp only [siteVal, hVar, hPol]
        cases s <;> cases (hubInfo triVar triSign edgeEnd carrySrc carryDst ℓ hc).2 <;>
          cases A ℓ (hubInfo triVar triSign edgeEnd carrySrc carryDst ℓ hc).1 <;> rfl
      have hlink_val : ∀ ℓ t j s,
          pull y (false, (ℓ, .inr (false, (t, j)), s)) =
            xor s (xor (triSign ℓ t j) (A ℓ (triVar ℓ t j))) := by
        intro ℓ t j s
        have hne := he2_link ℓ (t, j) s
        have htau : τSite (ℓ, .inr (false, (t, j)), s) =
            (ℓ, .inl (.inr (.inr (.inr (.inr (t, j))))), s) := rfl
        rw [htau, ← he0_all, hhub_val] at hne
        dsimp only [siteVal, hubInfo] at hne
        generalize pull y (false, (ℓ, .inr (false, (t, j)), s)) = v at hne ⊢
        generalize triSign ℓ t j = ts at hne ⊢
        generalize A ℓ (triVar ℓ t j) = av at hne ⊢
        revert hne
        cases v <;> cases s <;> cases ts <;> cases av <;> decide
      have hall_val : ∀ x, pull y (false, x) =
          siteVal triVar triSign edgeEnd carrySrc carryDst A x := by
        rintro ⟨ℓ, (hc | ⟨b, t, j⟩), s⟩
        · exact hhub_val ℓ hc s
        · cases b
          · exact hlink_val ℓ t j s
          · exact (he0_tri ℓ (t, j) s).2.trans (hlink_val ℓ t j s)
      have hvalid : ValidSpec triVar triSign edgeEnd carrySrc carryDst A := by
        refine ⟨?_, ?_, ?_⟩
        · intro ℓ e
          have hne := he2_hub ℓ (.inr (.inl (e, false))) false
          have htau : τSite (ℓ, .inl (.inr (.inl (e, false))), false) =
              (ℓ, .inl (.inr (.inl (e, true))), false) := rfl
          rw [htau, ← he0_all, hhub_val, hhub_val] at hne
          simpa [siteVal, hubInfo] using hne
        · intro ℓ hℓ c
          have hne := he2_hub ℓ (.inr (.inr (.inl c))) false
          have htau : τSite (ℓ, .inl (.inr (.inr (.inl c))), false) =
              (⟨ℓ.val + 1, by omega⟩, .inl (.inr (.inr (.inr (.inl c)))), true) := by
            dsimp only [τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            simp only [hℓ, ↓reduceDIte]
            rfl
          rw [htau, ← he0_all, hhub_val, hhub_val] at hne
          dsimp only [siteVal, hubInfo] at hne
          cases h1 : A ℓ (carrySrc c) <;>
            cases h2 : A ⟨ℓ.val + 1, by omega⟩ (carryDst c) <;>
            simp [h1, h2] at hne ⊢
        · intro ℓ t
          have h1 := htri_one ℓ t false
          dsimp only [triBlock] at h1
          rw [← he0_all, ← he0_all, ← he0_all, hall_val, hall_val, hall_val] at h1
          dsimp only [siteVal] at h1
          simp only [Bool.false_xor] at h1
          exact (triCost6_eq_one_diag _ _ _).mp h1
      refine ⟨A, hvalid, ?_⟩
      funext ⟨b, i⟩
      have hx : y (b, i) = pull y (b, eFin.symm i) := by simp [pull]
      rw [hx]
      cases b
      · exact hall_val (eFin.symm i)
      · exact (he0_all (eFin.symm i)).symm.trans (hall_val (eFin.symm i))
    · rintro ⟨A, hvalid, rfl⟩
      rw [hcost_pull (fun p => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2))]
      have hpull : pull (fun p => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2)) =
          fun u => siteVal triVar triSign edgeEnd carrySrc carryDst A u.2 := by
        funext ⟨b, x⟩
        simp [pull]
      rw [hpull]
      let sv := siteVal triVar triSign edgeEnd carrySrc carryDst A
      have he1 : (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry =>
          sv x ≠ sv (σSite x))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro ⟨ℓ, c, s⟩ _
        rw [Classical.not_not]
        rcases c with hc | ⟨b, t, j⟩
        · have h1 := hσ_hub_key ℓ hc s
          dsimp only [sv, siteVal]
          change xor s (xor (hPol ℓ hc) (A ℓ (hVar ℓ hc))) =
            xor (σHub ℓ (hc, s)).2 (xor (hPol ℓ (σHub ℓ (hc, s)).1) (A ℓ (hVar ℓ (σHub ℓ (hc, s)).1)))
          rw [h1.1]
          have h2 := h1.2
          generalize (σHub ℓ (hc, s)).2 = s2 at h2 ⊢
          generalize hPol ℓ hc = p1 at h2 ⊢
          generalize hPol ℓ (σHub ℓ (hc, s)).1 = p2 at h2 ⊢
          generalize A ℓ (hVar ℓ hc) = av
          revert h2
          cases s <;> cases s2 <;> cases p1 <;> cases p2 <;> cases av <;> decide
        · rfl
      have hhub0 : hubSum (fun u => sv u.2) = 0 := by
        refine Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun hc _ =>
          Finset.sum_eq_zero fun s _ => ?_
        dsimp only [term02]
        have hneq : sv (ℓ, .inl hc, s) ≠ sv (τSite (ℓ, .inl hc, s)) := by
          rcases hc with v | (⟨e, side⟩ | (c | (c | ⟨t, j⟩)))
          · dsimp only [sv, siteVal, hubInfo, τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            cases s <;> cases A ℓ v <;> decide
          · have hne := hvalid.1 ℓ e
            dsimp only [sv, siteVal, hubInfo, τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            cases side <;> cases s <;>
              cases h1 : (edgeEnd ℓ e false).2 <;> cases h2 : (edgeEnd ℓ e true).2 <;>
              cases h3 : A ℓ (edgeEnd ℓ e false).1 <;> cases h4 : A ℓ (edgeEnd ℓ e true).1 <;>
              simp [h1, h2, h3, h4] at hne ⊢
          · dsimp only [τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            split_ifs with hℓ
            · have heq := hvalid.2.1 ℓ hℓ c
              dsimp only [sv, siteVal, hubInfo]
              rw [heq]
              cases s <;> cases A ⟨ℓ.val + 1, by omega⟩ (carryDst c) <;> decide
            · dsimp only [sv, siteVal, hubInfo]
              cases s <;> cases A ℓ (carrySrc c) <;> decide
          · dsimp only [τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            split_ifs with hℓ
            · have heq := hvalid.2.1 ⟨ℓ.val - 1, by omega⟩ (show ℓ.val - 1 < r by omega) c
              have hℓeq : (⟨ℓ.val - 1 + 1, by omega⟩ : Fin (r + 1)) = ℓ := by
                ext; dsimp only; omega
              rw [hℓeq] at heq
              dsimp only [sv, siteVal, hubInfo]
              rw [← heq]
              cases s <;> cases A ⟨ℓ.val - 1, by omega⟩ (carrySrc c) <;> decide
            · dsimp only [sv, siteVal, hubInfo]
              cases s <;> cases A ℓ (carryDst c) <;> decide
          · dsimp only [sv, siteVal, hubInfo, τSite, tauSite, Equiv.coe_fn_mk, tauTo]
            cases s <;> cases triSign ℓ t j <;> cases A ℓ (triVar ℓ t j) <;> decide
        split_ifs with h1 <;> first | exact absurd rfl h1 | exact absurd ‹_› hneq | rfl
      have hlink0 : linkSum (fun u => sv u.2) = 0 := by
        refine Finset.sum_eq_zero fun ℓ _ => Finset.sum_eq_zero fun ⟨t, j⟩ _ =>
          Finset.sum_eq_zero fun s _ => ?_
        dsimp only [term02]
        have hneq : sv (ℓ, .inr (false, (t, j)), s) ≠ sv (τSite (ℓ, .inr (false, (t, j)), s)) := by
          dsimp only [sv, siteVal, hubInfo, τSite, tauSite, Equiv.coe_fn_mk, tauTo]
          cases s <;> cases triSign ℓ t j <;> cases A ℓ (triVar ℓ t j) <;> decide
        split_ifs with h1 <;> first | exact absurd rfl h1 | exact absurd ‹_› hneq | rfl
      have htri_eq : triSum (fun u => sv u.2) = T := by
        rw [hT_sum]
        refine Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun t _ =>
          Finset.sum_congr rfl fun s _ => ?_
        dsimp only [triBlock, sv, siteVal]
        rw [triCost6_eq_one_diag]
        exact (nae3_xor s _ _ _).mpr (hvalid.2.2 ℓ t)
      have hs := hsplit (fun u => sv u.2)
      dsimp only at hs
      change (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry => sv x ≠ sv x)).card +
        (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry => sv x ≠ sv (σSite x))).card +
        (Finset.univ.filter (fun x : Site r LVar LTri LEdge ICarry => sv x = sv (τSite x))).card = T
      omega
  refine ⟨hlb, ?_, hchar⟩
  intro y hy
  obtain ⟨A, _, rfl⟩ := (hchar y).mp hy
  refine ⟨?_, ?_⟩
  · let flipPerm : Equiv.Perm (Site r LVar LTri LEdge ICarry) :=
      ⟨flipSite, flipSite, flipSite_inv, flipSite_inv⟩
    let E : Equiv.Perm V :=
      Equiv.prodCongr (Equiv.refl Bool) (eFin.symm.trans (flipPerm.trans eFin))
    have ht := negate_half
      (fun p : V => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2)) E (by
        rintro ⟨b, i⟩
        change siteVal triVar triSign edgeEnd carrySrc carryDst A
          (eFin.symm (eFin (flipSite (eFin.symm i)))) = _
        rw [Equiv.symm_apply_apply]
        exact siteVal_flip _ _ _ _ _ A (eFin.symm i))
    have hc : Fintype.card (Bool × Fin n) = 2 * n := by
      rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    have ht' : 2 * (Finset.univ.filter (fun p : V =>
        (fun p => siteVal triVar triSign edgeEnd carrySrc carryDst A (eFin.symm p.2)) p = true)).card = 2 * n := by
      rw [← hc, ← ht]
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) ht'
  · intro x
    simp only [Equiv.symm_apply_apply]
    exact siteVal_flip _ _ _ _ _ A x

end Layered

def rot (k s x : ℕ) : ℕ :=
  ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k

def step (k x : ℕ) : ℕ :=
  (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

def cVal (k j : ℕ) : ℕ :=
  3 ^ (k + j) % 2 ^ k

def rotIdx (k s : ℕ) (i : Fin k) : Fin k :=
  ⟨(i.val + k - s % k) % k,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

def addIdx (k d : ℕ) (i : Fin k) : Fin k :=
  ⟨(i.val + d) % k,
    Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

lemma rot_lt (k s x : ℕ) : rot k s x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_pack (f : ℕ → Bool) (n j : ℕ) :
    ((List.range n).foldl (fun acc m => acc ||| ((f m).toNat <<< m)) 0).testBit j =
      (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.shiftLeft_eq]
    by_cases h : n = j
    · subst h; cases f n <;> simp
    · have hcmp : j < n + 1 ↔ j < n := by omega
      cases f n <;> simp [h, hcmp]

lemma step_lt (k x : ℕ) : step k x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold step
  rw [testBit_pack]
  simp [Nat.not_lt_of_ge hj]

lemma testBit_rot (k s x : ℕ) (hx : x < 2 ^ k) (i : Fin k) :
    (rot k s x).testBit i.val = x.testBit (rotIdx k s i).val := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  let m := s % k
  have hm : m < k := Nat.mod_lt s hk
  unfold rot rotIdx
  change (((x <<< m) ||| (x >>> (k - m))) % 2 ^ k).testBit i.val =
    x.testBit ((i.val + k - m) % k)
  rw [Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : m ≤ i.val
  · have hhi : x.testBit (k - m + i.val) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    have hidx : (i.val + k - m) % k = i.val - m := by
      rw [show i.val + k - m = (i.val - m) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true h, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hidx : (i.val + k - m) % k = k - m + i.val := by
      rw [show i.val + k - m = k - m + i.val by omega, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false h, Bool.false_and, Bool.false_or, hidx]

lemma testBit_step (k x : ℕ) (i : Fin k) :
    (step k x).testBit i.val =
      xor (x.testBit i.val)
        (!(x.testBit (addIdx k 1 i).val) && x.testBit (addIdx k 2 i).val) := by
  unfold step addIdx
  rw [testBit_pack, decide_eq_true i.isLt, Bool.true_and]

lemma lt_two_pow_iff_bits {k m v : ℕ} (hv : v < 2 ^ k) :
    v < 2 ^ m ↔ ∀ i : Fin k, m ≤ i.val → v.testBit i.val = false := by
  constructor
  · intro hlt i hi
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hi))
  · intro hbits
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_cases hjk : j < k
    · exact hbits ⟨j, hjk⟩ hj
    · have hkj : k ≤ j := Nat.le_of_not_lt hjk
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hkj))

def packNat (k : ℕ) (b : Fin k → Bool) : ℕ :=
  (List.range k).foldl (fun acc m =>
    acc ||| ((if h : m < k then b ⟨m, h⟩ else false).toNat <<< m)) 0

lemma testBit_packNat (k : ℕ) (b : Fin k → Bool) (i : Fin k) :
    (packNat k b).testBit i.val = b i := by
  unfold packNat
  rw [testBit_pack, decide_eq_true i.isLt, Bool.true_and]
  simp only [i.isLt, ↓reduceDIte]

lemma packNat_lt (k : ℕ) (b : Fin k → Bool) : packNat k b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold packNat
  rw [testBit_pack]
  simp [Nat.not_lt_of_ge hj]

def packFin (k : ℕ) (b : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨packNat k b, packNat_lt k b⟩

lemma packFin_bits (k : ℕ) (v : Fin (2 ^ k)) :
    packFin k (fun i => v.val.testBit i.val) = v := by
  ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hjk : j < k
  · exact testBit_packNat k (fun i => v.val.testBit i.val) ⟨j, hjk⟩
  · have hkj : k ≤ j := Nat.le_of_not_lt hjk
    have h1 : (packFin k (fun i => v.val.testBit i.val)).val.testBit j = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (packFin k _).isLt (Nat.pow_le_pow_right (by omega : 0 < 2) hkj))
    have h2 : v.val.testBit j = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by omega : 0 < 2) hkj))
    rw [h1, h2]

def chanIter (k r : ℕ) (side : Bool) (x : Fin 3 → Fin (2 ^ k)) (m : ℕ) : ℕ :=
  let w := (x 2).val
  let d1 := if side then 2 else 1
  let d2 := if side then k - 2 else k - 1
  let s0 := if side then 3 else 1
  let k0 : Fin 3 := if side then 1 else 0
  (List.range m).foldl (fun (p i : ℕ) =>
    let t := i + 1
    let sw := if side then 3 * t + 1 else 2 * (t - 1)
    let cj := if side then r + t else t
    step k (p ^^^ rot k d1 p ^^^ rot k d2 p) ^^^ rot k sw w ^^^ cVal k cj)
    (rot k s0 w ^^^ (x k0).val)

lemma chanIter_zero (k r : ℕ) (side : Bool) (x : Fin 3 → Fin (2 ^ k)) :
    chanIter k r side x 0 =
      rot k (if side then 3 else 1) (x 2).val ^^^ (x (if side then 1 else 0)).val := rfl

lemma chanIter_succ (k r : ℕ) (side : Bool) (x : Fin 3 → Fin (2 ^ k)) (m : ℕ) :
    chanIter k r side x (m + 1) =
      let p := chanIter k r side x m
      let t := m + 1
      step k (p ^^^ rot k (if side then 2 else 1) p ^^^ rot k (if side then k - 2 else k - 1) p) ^^^
        rot k (if side then 3 * t + 1 else 2 * (t - 1)) (x 2).val ^^^
        cVal k (if side then r + t else t) := by
  unfold chanIter
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma chanIter_lt (k r : ℕ) (side : Bool) (x : Fin 3 → Fin (2 ^ k)) (m : ℕ) :
    chanIter k r side x m < 2 ^ k := by
  cases m with
  | zero =>
    rw [chanIter_zero]
    exact Nat.xor_lt_two_pow (rot_lt k _ _) (x _).isLt
  | succ m =>
    rw [chanIter_succ]
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k _ _))
      (Nat.mod_lt _ (Nat.two_pow_pos k))

abbrev VVar (k : ℕ) := Unit ⊕ ((Fin 3 × Fin k) ⊕ (Bool × Fin 14 × Fin k))
abbrev VTri (k : ℕ) := (Bool × Fin 13 × Fin k) × Fin 3
abbrev VEdge (k : ℕ) := Bool × Bool × Fin k
abbrev VCarry (k : ℕ) := Unit ⊕ ((Fin 3 × Fin k) ⊕ (Bool × Fin k))

abbrev refV {k : ℕ} : VVar k := .inl ()
abbrev keyV {k : ℕ} (a : Fin 3) (i : Fin k) : VVar k := .inr (.inl (a, i))
abbrev chV {k : ℕ} (side : Bool) (q : Fin 14) (i : Fin k) : VVar k := .inr (.inr (side, q, i))

def fin14Succ (q : Fin 13) : Fin 14 := ⟨q.val + 1, by have := q.isLt; omega⟩

def d1Of (side : Bool) : ℕ := if side then 2 else 1
def d2Of (k : ℕ) (side : Bool) : ℕ := if side then k - 2 else k - 1

def inALit (k r : ℕ) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : VVar k × Bool :=
  if ℓ.val = 0 then (keyV (if side then 1 else 0) i, false)
  else (chV side 10 i, false)

def inBLit (k r : ℕ) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : VVar k × Bool :=
  if ℓ.val = 0 then (keyV 2 (rotIdx k (if side then 3 else 1) i), false)
  else
    let sw := if side then 3 * ℓ.val + 1 else 2 * (ℓ.val - 1)
    let cj := if side then r + ℓ.val else ℓ.val
    (keyV 2 (rotIdx k sw i), (cVal k cj).testBit i.val)

def gateInputs (k r : ℕ) (ℓ : Fin (r + 1)) (side : Bool) (q : Fin 13) (i : Fin k) :
    (VVar k × Bool) × (VVar k × Bool) :=
  match q with
  | ⟨0, _⟩ => ((chV side 0 i, true), (chV side 0 (rotIdx k (d1Of side) i), false))
  | ⟨1, _⟩ => ((chV side 0 i, false), (chV side 0 (rotIdx k (d1Of side) i), true))
  | ⟨2, _⟩ => ((chV side 1 i, false), (chV side 2 i, false))
  | ⟨3, _⟩ => ((chV side 3 i, true), (chV side 0 (rotIdx k (d2Of k side) i), false))
  | ⟨4, _⟩ => ((chV side 3 i, false), (chV side 0 (rotIdx k (d2Of k side) i), true))
  | ⟨5, _⟩ => ((chV side 4 i, false), (chV side 5 i, false))
  | ⟨6, _⟩ => ((chV side 6 (addIdx k 1 i), true), (chV side 6 (addIdx k 2 i), false))
  | ⟨7, _⟩ => ((chV side 6 i, true), (chV side 7 i, true))
  | ⟨8, _⟩ => ((chV side 6 i, false), (chV side 7 i, false))
  | ⟨9, _⟩ => ((chV side 8 i, false), (chV side 9 i, false))
  | ⟨10, _⟩ => (((inALit k r ℓ side i).1, !(inALit k r ℓ side i).2), inBLit k r ℓ side i)
  | ⟨11, _⟩ => (inALit k r ℓ side i, ((inBLit k r ℓ side i).1, !(inBLit k r ℓ side i).2))
  | ⟨12, _⟩ => ((chV side 11 i, false), (chV side 12 i, false))

def vTriLit (k r : ℕ) (ℓ : Fin (r + 1)) (t : VTri k) (j : Fin 3) : VVar k × Bool :=
  let ins := gateInputs k r ℓ t.1.1 t.1.2.1 t.1.2.2
  let outLit : VVar k × Bool := (chV t.1.1 (fin14Succ t.1.2.1) t.1.2.2, false)
  let refLit : VVar k × Bool := (refV, false)
  match t.2, j with
  | ⟨0, _⟩, ⟨0, _⟩ => ins.1
  | ⟨0, _⟩, ⟨1, _⟩ => ins.2
  | ⟨0, _⟩, ⟨2, _⟩ => outLit
  | ⟨1, _⟩, ⟨0, _⟩ => ins.1
  | ⟨1, _⟩, ⟨1, _⟩ => outLit
  | ⟨1, _⟩, ⟨2, _⟩ => refLit
  | ⟨2, _⟩, ⟨0, _⟩ => ins.2
  | ⟨2, _⟩, ⟨1, _⟩ => outLit
  | ⟨2, _⟩, ⟨2, _⟩ => refLit

def vTriVar (k r : ℕ) (ℓ : Fin (r + 1)) (t : VTri k) (j : Fin 3) : VVar k :=
  (vTriLit k r ℓ t j).1

def vTriSign (k r : ℕ) (ℓ : Fin (r + 1)) (t : VTri k) (j : Fin 3) : Bool :=
  (vTriLit k r ℓ t j).2

def vEdgeEnd (k r : ℕ) (ℓ : Fin (r + 1)) (e : VEdge k) (endSide : Bool) : VVar k × Bool :=
  match e with
  | (false, side, i) =>
      if ℓ.val = 0 then
        match endSide with
        | true => (refV, true)
        | false => (chV side 0 i, false)
      else
        (refV, endSide)
  | (true, side, i) =>
      if ℓ.val = r ∧ k - (k + 1) / 2 ≤ i.val then
        match endSide with
        | true => (refV, true)
        | false => (chV side 13 i, false)
      else
        (refV, endSide)

def vCarrySrc {k : ℕ} : VCarry k → VVar k
  | .inl () => refV
  | .inr (.inl (a, i)) => keyV a i
  | .inr (.inr (side, i)) => chV side 13 i

def vCarryDst {k : ℕ} : VCarry k → VVar k
  | .inl () => refV
  | .inr (.inl (a, i)) => keyV a i
  | .inr (.inr (side, i)) => chV side 0 i

def prevBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  if ℓ.val = 0 then false else (chanIter k r side x (ℓ.val - 1)).testBit i.val

def aBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  xor (prevBit k r x ℓ side i) (prevBit k r x ℓ side (rotIdx k (d1Of side) i))

def mBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  xor (aBit k r x ℓ side i) (prevBit k r x ℓ side (rotIdx k (d2Of k side) i))

def chiBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  !(!(mBit k r x ℓ side (addIdx k 1 i)) && mBit k r x ℓ side (addIdx k 2 i))

def sBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  xor (mBit k r x ℓ side i) (!(chiBit k r x ℓ side i))

def inABit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  if ℓ.val = 0 then (x (if side then 1 else 0)).val.testBit i.val else sBit k r x ℓ side i

def inBBit (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) : Bool :=
  if ℓ.val = 0 then
    (x 2).val.testBit (rotIdx k (if side then 3 else 1) i).val
  else
    let sw := if side then 3 * ℓ.val + 1 else 2 * (ℓ.val - 1)
    let cj := if side then r + ℓ.val else ℓ.val
    xor ((cVal k cj).testBit i.val) ((x 2).val.testBit (rotIdx k sw i).val)

def evalChanWire (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool)
    (q : Fin 14) (i : Fin k) : Bool :=
  match q with
  | ⟨0, _⟩ => prevBit k r x ℓ side i
  | ⟨1, _⟩ => !(!(prevBit k r x ℓ side i) && prevBit k r x ℓ side (rotIdx k (d1Of side) i))
  | ⟨2, _⟩ => !(prevBit k r x ℓ side i && !(prevBit k r x ℓ side (rotIdx k (d1Of side) i)))
  | ⟨3, _⟩ => aBit k r x ℓ side i
  | ⟨4, _⟩ => !(!(aBit k r x ℓ side i) && prevBit k r x ℓ side (rotIdx k (d2Of k side) i))
  | ⟨5, _⟩ => !(aBit k r x ℓ side i && !(prevBit k r x ℓ side (rotIdx k (d2Of k side) i)))
  | ⟨6, _⟩ => mBit k r x ℓ side i
  | ⟨7, _⟩ => chiBit k r x ℓ side i
  | ⟨8, _⟩ => !(!(mBit k r x ℓ side i) && !(chiBit k r x ℓ side i))
  | ⟨9, _⟩ => !(mBit k r x ℓ side i && chiBit k r x ℓ side i)
  | ⟨10, _⟩ => sBit k r x ℓ side i
  | ⟨11, _⟩ => !(!(inABit k r x ℓ side i) && inBBit k r x ℓ side i)
  | ⟨12, _⟩ => !(inABit k r x ℓ side i && !(inBBit k r x ℓ side i))
  | ⟨13, _⟩ => xor (inABit k r x ℓ side i) (inBBit k r x ℓ side i)

def evalTrace (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) : VVar k → Bool
  | .inl () => false
  | .inr (.inl (a, i)) => (x a).val.testBit i.val
  | .inr (.inr (side, q, i)) => evalChanWire k r x ℓ side q i

lemma evalChanWire_out (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool)
    (i : Fin k) :
    evalChanWire k r x ℓ side 13 i = (chanIter k r side x ℓ.val).testBit i.val := by
  change xor (inABit k r x ℓ side i) (inBBit k r x ℓ side i) = _
  cases hℓ : ℓ.val with
  | zero =>
    unfold inABit inBBit
    simp only [hℓ, ↓reduceIte]
    rw [chanIter_zero, Nat.testBit_xor, testBit_rot k _ _ (x 2).isLt i, Bool.xor_comm]
  | succ m =>
    have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
    unfold inABit inBBit sBit chiBit
    simp only [hℓ, hne, ↓reduceIte, Nat.add_sub_cancel, Bool.not_not]
    have hprev : ∀ j : Fin k, prevBit k r x ℓ side j = (chanIter k r side x m).testBit j.val := by
      intro j
      unfold prevBit
      simp only [hℓ, hne, ↓reduceIte, Nat.add_sub_cancel]
    have hlt := chanIter_lt k r side x m
    have hmix_bit : ∀ j : Fin k,
        mBit k r x ℓ side j =
        (chanIter k r side x m ^^^
          rot k (if side then 2 else 1) (chanIter k r side x m) ^^^
          rot k (if side then k - 2 else k - 1) (chanIter k r side x m)).testBit j.val := by
      intro j
      unfold mBit aBit d1Of d2Of
      rw [hprev j, hprev _, hprev _, Nat.testBit_xor, Nat.testBit_xor,
        testBit_rot k _ _ hlt j, testBit_rot k _ _ hlt j]
    rw [chanIter_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step,
      hmix_bit i, hmix_bit (addIdx k 1 i), hmix_bit (addIdx k 2 i),
      testBit_rot k _ _ (x 2).isLt i,
      Bool.xor_comm ((cVal k _).testBit i.val)]
    simp only [Nat.add_sub_cancel, Bool.xor_assoc]

lemma gate_ok_iff (k r : ℕ) (A : Fin (r + 1) → VVar k → Bool)
    (ℓ : Fin (r + 1)) (href : A ℓ refV = false) (side : Bool) (q : Fin 13) (i : Fin k) :
    (∀ kTri : Fin 3, nae3
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 0) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 0)))
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 1) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 1)))
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 2) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 2)))) ↔
    A ℓ (chV side (fin14Succ q) i) =
      !(xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1) &&
        xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1)) := by
  have hall : (∀ kTri : Fin 3, nae3
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 0) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 0)))
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 1) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 1)))
      (xor (vTriSign k r ℓ ((side, q, i), kTri) 2) (A ℓ (vTriVar k r ℓ ((side, q, i), kTri) 2)))) ↔
      (nae3 (xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1))
            (xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1))
            (A ℓ (chV side (fin14Succ q) i)) ∧
       nae3 (xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1))
            (A ℓ (chV side (fin14Succ q) i))
            false ∧
       nae3 (xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1))
            (A ℓ (chV side (fin14Succ q) i))
            false) := by
    constructor
    · intro h
      have h0 : nae3 (xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1))
          (xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1))
          (xor false (A ℓ (chV side (fin14Succ q) i))) := h 0
      have h1 : nae3 (xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1))
          (xor false (A ℓ (chV side (fin14Succ q) i)))
          (xor false (A ℓ refV)) := h 1
      have h2 : nae3 (xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1))
          (xor false (A ℓ (chV side (fin14Succ q) i)))
          (xor false (A ℓ refV)) := h 2
      rw [Bool.false_xor] at h0
      rw [Bool.false_xor, Bool.false_xor, href] at h1 h2
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩ ⟨v, hv⟩
      match v, hv with
      | 0, _ =>
        change nae3 _ _ (xor false (A ℓ (chV side (fin14Succ q) i)))
        rw [Bool.false_xor]
        exact h0
      | 1, _ =>
        change nae3 _ (xor false (A ℓ (chV side (fin14Succ q) i))) (xor false (A ℓ refV))
        rw [Bool.false_xor, Bool.false_xor, href]
        exact h1
      | 2, _ =>
        change nae3 _ (xor false (A ℓ (chV side (fin14Succ q) i))) (xor false (A ℓ refV))
        rw [Bool.false_xor, Bool.false_xor, href]
        exact h2
  rw [hall, nand_iff_nae]

lemma evalTrace_inA (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) :
    xor (inALit k r ℓ side i).2 (evalTrace k r x ℓ (inALit k r ℓ side i).1) =
      inABit k r x ℓ side i := by
  unfold inALit inABit
  by_cases hℓ : ℓ.val = 0
  · simp only [hℓ, ↓reduceIte, evalTrace, Bool.false_xor]
  · simp only [hℓ, ↓reduceIte, evalTrace, evalChanWire, Bool.false_xor]

lemma evalTrace_inB (k r : ℕ) (x : Fin 3 → Fin (2 ^ k)) (ℓ : Fin (r + 1)) (side : Bool) (i : Fin k) :
    xor (inBLit k r ℓ side i).2 (evalTrace k r x ℓ (inBLit k r ℓ side i).1) =
      inBBit k r x ℓ side i := by
  unfold inBLit inBBit
  by_cases hℓ : ℓ.val = 0
  · simp only [hℓ, ↓reduceIte, evalTrace, Bool.false_xor]
  · simp only [hℓ, ↓reduceIte, evalTrace]

lemma evalTrace_valid (k r : ℕ) (x : Fin 3 → Fin (2 ^ k))
    (hok : chanIter k r false x r < 2 ^ (k - (k + 1) / 2) ∧
           chanIter k r true x r < 2 ^ (k - (k + 1) / 2)) :
    ValidSpec (vTriVar k r) (vTriSign k r) (vEdgeEnd k r) vCarrySrc vCarryDst
      (evalTrace k r x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ ⟨b, side, i⟩
    cases b
    · dsimp only [vEdgeEnd]
      by_cases hℓ : ℓ.val = 0
      · simp only [hℓ, ↓reduceIte, evalTrace, evalChanWire, prevBit]
        decide
      · simp only [hℓ, ↓reduceIte, evalTrace]
        decide
    · dsimp only [vEdgeEnd]
      by_cases hℓ : ℓ.val = r ∧ k - (k + 1) / 2 ≤ i.val
      · simp only [hℓ, and_self, ↓reduceIte, evalTrace]
        rw [evalChanWire_out, hℓ.1]
        have hb : (chanIter k r side x r).testBit i.val = false := by
          have hlt := chanIter_lt k r side x r
          cases side
          · exact (lt_two_pow_iff_bits hlt).mp hok.1 i hℓ.2
          · exact (lt_two_pow_iff_bits hlt).mp hok.2 i hℓ.2
        rw [hb]; decide
      · simp only [hℓ, ↓reduceIte, evalTrace]
        decide
  · intro ℓ hℓ c
    rcases c with ⟨⟩ | ⟨a, i⟩ | ⟨side, i⟩
    · rfl
    · rfl
    · dsimp only [vCarrySrc, vCarryDst, evalTrace]
      rw [evalChanWire_out]
      change _ = prevBit k r x ⟨ℓ.val + 1, by omega⟩ side i
      unfold prevBit
      have hne : ℓ.val + 1 ≠ 0 := Nat.succ_ne_zero ℓ.val
      simp only [hne, ↓reduceIte, Nat.add_sub_cancel]
  · intro ℓ ⟨⟨side, q, i⟩, kTri⟩
    have hiff := gate_ok_iff k r (evalTrace k r x) ℓ rfl side q i
    have hgate : evalTrace k r x ℓ (chV side (fin14Succ q) i) =
        !(xor (gateInputs k r ℓ side q i).1.2 (evalTrace k r x ℓ (gateInputs k r ℓ side q i).1.1) &&
          xor (gateInputs k r ℓ side q i).2.2 (evalTrace k r x ℓ (gateInputs k r ℓ side q i).2.1)) := by
      rcases q with ⟨qv, hqv⟩
      match qv, hqv with
      | 0, _ =>
        change (!(!(prevBit k r x ℓ side i) && prevBit k r x ℓ side (rotIdx k (d1Of side) i))) =
          !(xor true (prevBit k r x ℓ side i) && xor false (prevBit k r x ℓ side (rotIdx k (d1Of side) i)))
        rw [Bool.true_xor, Bool.false_xor]
      | 1, _ =>
        change (!(prevBit k r x ℓ side i && !(prevBit k r x ℓ side (rotIdx k (d1Of side) i)))) =
          !(xor false (prevBit k r x ℓ side i) && xor true (prevBit k r x ℓ side (rotIdx k (d1Of side) i)))
        rw [Bool.false_xor, Bool.true_xor]
      | 2, _ =>
        change aBit k r x ℓ side i =
          !(xor false (evalChanWire k r x ℓ side 1 i) && xor false (evalChanWire k r x ℓ side 2 i))
        rw [Bool.false_xor, Bool.false_xor]
        exact (xor_via_nand _ _).symm
      | 3, _ =>
        change (!(!(aBit k r x ℓ side i) && prevBit k r x ℓ side (rotIdx k (d2Of k side) i))) =
          !(xor true (aBit k r x ℓ side i) && xor false (prevBit k r x ℓ side (rotIdx k (d2Of k side) i)))
        rw [Bool.true_xor, Bool.false_xor]
      | 4, _ =>
        change (!(aBit k r x ℓ side i && !(prevBit k r x ℓ side (rotIdx k (d2Of k side) i)))) =
          !(xor false (aBit k r x ℓ side i) && xor true (prevBit k r x ℓ side (rotIdx k (d2Of k side) i)))
        rw [Bool.false_xor, Bool.true_xor]
      | 5, _ =>
        change mBit k r x ℓ side i =
          !(xor false (evalChanWire k r x ℓ side 4 i) && xor false (evalChanWire k r x ℓ side 5 i))
        rw [Bool.false_xor, Bool.false_xor]
        exact (xor_via_nand _ _).symm
      | 6, _ =>
        change chiBit k r x ℓ side i =
          !(xor true (mBit k r x ℓ side (addIdx k 1 i)) && xor false (mBit k r x ℓ side (addIdx k 2 i)))
        rw [Bool.true_xor, Bool.false_xor]
        rfl
      | 7, _ =>
        change (!(!(mBit k r x ℓ side i) && !(chiBit k r x ℓ side i))) =
          !(xor true (mBit k r x ℓ side i) && xor true (chiBit k r x ℓ side i))
        rw [Bool.true_xor, Bool.true_xor]
      | 8, _ =>
        change (!(mBit k r x ℓ side i && chiBit k r x ℓ side i)) =
          !(xor false (mBit k r x ℓ side i) && xor false (chiBit k r x ℓ side i))
        rw [Bool.false_xor, Bool.false_xor]
      | 9, _ =>
        change sBit k r x ℓ side i =
          !(xor false (evalChanWire k r x ℓ side 8 i) && xor false (evalChanWire k r x ℓ side 9 i))
        rw [Bool.false_xor, Bool.false_xor]
        have h : ∀ a b : Bool, (!(!(!a && !b) && !(a && b))) = xor a (!b) := by decide
        exact (h _ _).symm
      | 10, _ =>
        change (!(!(inABit k r x ℓ side i) && inBBit k r x ℓ side i)) =
          !(xor (!(inALit k r ℓ side i).2) (evalTrace k r x ℓ (inALit k r ℓ side i).1) &&
            xor (inBLit k r ℓ side i).2 (evalTrace k r x ℓ (inBLit k r ℓ side i).1))
        rw [xor_not_l, evalTrace_inA, evalTrace_inB]
      | 11, _ =>
        change (!(inABit k r x ℓ side i && !(inBBit k r x ℓ side i))) =
          !(xor (inALit k r ℓ side i).2 (evalTrace k r x ℓ (inALit k r ℓ side i).1) &&
            xor (!(inBLit k r ℓ side i).2) (evalTrace k r x ℓ (inBLit k r ℓ side i).1))
        rw [xor_not_l, evalTrace_inA, evalTrace_inB]
      | 12, _ =>
        change xor (inABit k r x ℓ side i) (inBBit k r x ℓ side i) =
          !(xor false (evalChanWire k r x ℓ side 11 i) && xor false (evalChanWire k r x ℓ side 12 i))
        rw [Bool.false_xor, Bool.false_xor]
        exact (xor_via_nand _ _).symm
    exact (hiff.mpr hgate) kTri

lemma valid_imp_evalTrace (k r : ℕ) (A : Fin (r + 1) → VVar k → Bool)
    (hv : ValidSpec (vTriVar k r) (vTriSign k r) (vEdgeEnd k r) vCarrySrc vCarryDst A)
    (href0 : A 0 refV = false) :
    let x : Fin 3 → Fin (2 ^ k) := fun a => packFin k (fun i => A 0 (keyV a i))
    (chanIter k r false x r < 2 ^ (k - (k + 1) / 2) ∧
     chanIter k r true x r < 2 ^ (k - (k + 1) / 2)) ∧
    A = evalTrace k r x := by
  intro x
  have hkey0 : ∀ a i, A 0 (keyV a i) = (x a).val.testBit i.val := fun a i =>
    (testBit_packNat k (fun j => A 0 (keyV a j)) i).symm
  have href : ∀ ℓ : Fin (r + 1), A ℓ refV = false := by
    intro ⟨m, hm⟩
    induction m with
    | zero => exact href0
    | succ m ih =>
      have h1 := hv.2.1 ⟨m, by omega⟩ (show m < r by omega) (.inl ())
      exact h1.symm.trans (ih (by omega))
  have hkey : ∀ (ℓ : Fin (r + 1)) (a : Fin 3) (i : Fin k),
      A ℓ (keyV a i) = (x a).val.testBit i.val := by
    intro ⟨m, hm⟩ a i
    induction m with
    | zero => exact hkey0 a i
    | succ m ih =>
      have h1 := hv.2.1 ⟨m, by omega⟩ (show m < r by omega) (.inr (.inl (a, i)))
      exact h1.symm.trans (ih (by omega))
  have hstep_layer : ∀ (ℓ : Fin (r + 1)) (side : Bool),
      (∀ i : Fin k, A ℓ (chV side 0 i) = prevBit k r x ℓ side i) →
      ∀ (q : Fin 14) (i : Fin k), A ℓ (chV side q i) = evalChanWire k r x ℓ side q i := by
    intro ℓ side h0
    have hg : ∀ (q : Fin 13) (i : Fin k),
        A ℓ (chV side (fin14Succ q) i) =
          !(xor (gateInputs k r ℓ side q i).1.2 (A ℓ (gateInputs k r ℓ side q i).1.1) &&
            xor (gateInputs k r ℓ side q i).2.2 (A ℓ (gateInputs k r ℓ side q i).2.1)) :=
      fun q i => (gate_ok_iff k r A ℓ (href ℓ) side q i).mp
        (fun kTri => hv.2.2 ℓ ((side, q, i), kTri))
    have h1 : ∀ i, A ℓ (chV side 1 i) = evalChanWire k r x ℓ side 1 i := fun i => by
      have hg0 : A ℓ (chV side 1 i) =
          !(xor true (A ℓ (chV side 0 i)) && xor false (A ℓ (chV side 0 (rotIdx k (d1Of side) i)))) :=
        hg 0 i
      rw [hg0, Bool.true_xor, Bool.false_xor, h0, h0]
      rfl
    have h2 : ∀ i, A ℓ (chV side 2 i) = evalChanWire k r x ℓ side 2 i := fun i => by
      have hg1 : A ℓ (chV side 2 i) =
          !(xor false (A ℓ (chV side 0 i)) && xor true (A ℓ (chV side 0 (rotIdx k (d1Of side) i)))) :=
        hg 1 i
      rw [hg1, Bool.false_xor, Bool.true_xor, h0, h0]
      rfl
    have h3 : ∀ i, A ℓ (chV side 3 i) = aBit k r x ℓ side i := fun i => by
      have hg2 : A ℓ (chV side 3 i) =
          !(xor false (A ℓ (chV side 1 i)) && xor false (A ℓ (chV side 2 i))) := hg 2 i
      rw [hg2, Bool.false_xor, Bool.false_xor, h1, h2]
      exact xor_via_nand _ _
    have h4 : ∀ i, A ℓ (chV side 4 i) = evalChanWire k r x ℓ side 4 i := fun i => by
      have hg3 : A ℓ (chV side 4 i) =
          !(xor true (A ℓ (chV side 3 i)) && xor false (A ℓ (chV side 0 (rotIdx k (d2Of k side) i)))) :=
        hg 3 i
      rw [hg3, Bool.true_xor, Bool.false_xor, h3, h0]
      rfl
    have h5 : ∀ i, A ℓ (chV side 5 i) = evalChanWire k r x ℓ side 5 i := fun i => by
      have hg4 : A ℓ (chV side 5 i) =
          !(xor false (A ℓ (chV side 3 i)) && xor true (A ℓ (chV side 0 (rotIdx k (d2Of k side) i)))) :=
        hg 4 i
      rw [hg4, Bool.false_xor, Bool.true_xor, h3, h0]
      rfl
    have h6 : ∀ i, A ℓ (chV side 6 i) = mBit k r x ℓ side i := fun i => by
      have hg5 : A ℓ (chV side 6 i) =
          !(xor false (A ℓ (chV side 4 i)) && xor false (A ℓ (chV side 5 i))) := hg 5 i
      rw [hg5, Bool.false_xor, Bool.false_xor, h4, h5]
      exact xor_via_nand _ _
    have h7 : ∀ i, A ℓ (chV side 7 i) = chiBit k r x ℓ side i := fun i => by
      have hg6 : A ℓ (chV side 7 i) =
          !(xor true (A ℓ (chV side 6 (addIdx k 1 i))) && xor false (A ℓ (chV side 6 (addIdx k 2 i)))) :=
        hg 6 i
      rw [hg6, Bool.true_xor, Bool.false_xor, h6, h6]
      rfl
    have h8 : ∀ i, A ℓ (chV side 8 i) = evalChanWire k r x ℓ side 8 i := fun i => by
      have hg7 : A ℓ (chV side 8 i) =
          !(xor true (A ℓ (chV side 6 i)) && xor true (A ℓ (chV side 7 i))) := hg 7 i
      rw [hg7, Bool.true_xor, Bool.true_xor, h6, h7]
      rfl
    have h9 : ∀ i, A ℓ (chV side 9 i) = evalChanWire k r x ℓ side 9 i := fun i => by
      have hg8 : A ℓ (chV side 9 i) =
          !(xor false (A ℓ (chV side 6 i)) && xor false (A ℓ (chV side 7 i))) := hg 8 i
      rw [hg8, Bool.false_xor, Bool.false_xor, h6, h7]
      rfl
    have h10 : ∀ i, A ℓ (chV side 10 i) = sBit k r x ℓ side i := fun i => by
      have hg9 : A ℓ (chV side 10 i) =
          !(xor false (A ℓ (chV side 8 i)) && xor false (A ℓ (chV side 9 i))) := hg 9 i
      rw [hg9, Bool.false_xor, Bool.false_xor, h8, h9]
      have h : ∀ a b : Bool, (!(!(!a && !b) && !(a && b))) = xor a (!b) := by decide
      exact h _ _
    have hA_inA : ∀ i, xor (inALit k r ℓ side i).2 (A ℓ (inALit k r ℓ side i).1) =
        inABit k r x ℓ side i := fun i => by
      unfold inALit inABit
      by_cases hℓ : ℓ.val = 0
      · simp only [hℓ, ↓reduceIte, hkey, Bool.false_xor]
      · simp only [hℓ, ↓reduceIte, h10, Bool.false_xor]
    have hA_inB : ∀ i, xor (inBLit k r ℓ side i).2 (A ℓ (inBLit k r ℓ side i).1) =
        inBBit k r x ℓ side i := fun i => by
      unfold inBLit inBBit
      by_cases hℓ : ℓ.val = 0
      · simp only [hℓ, ↓reduceIte, hkey, Bool.false_xor]
      · simp only [hℓ, ↓reduceIte, hkey]
    have h11 : ∀ i, A ℓ (chV side 11 i) = evalChanWire k r x ℓ side 11 i := fun i => by
      have hg10 : A ℓ (chV side 11 i) =
          !(xor (!(inALit k r ℓ side i).2) (A ℓ (inALit k r ℓ side i).1) &&
            xor (inBLit k r ℓ side i).2 (A ℓ (inBLit k r ℓ side i).1)) := hg 10 i
      rw [hg10, xor_not_l, hA_inA, hA_inB]
      rfl
    have h12 : ∀ i, A ℓ (chV side 12 i) = evalChanWire k r x ℓ side 12 i := fun i => by
      have hg11 : A ℓ (chV side 12 i) =
          !(xor (inALit k r ℓ side i).2 (A ℓ (inALit k r ℓ side i).1) &&
            xor (!(inBLit k r ℓ side i).2) (A ℓ (inBLit k r ℓ side i).1)) := hg 11 i
      rw [hg11, xor_not_l, hA_inA, hA_inB]
      rfl
    have h13 : ∀ i, A ℓ (chV side 13 i) = evalChanWire k r x ℓ side 13 i := fun i => by
      have hg12 : A ℓ (chV side 13 i) =
          !(xor false (A ℓ (chV side 11 i)) && xor false (A ℓ (chV side 12 i))) := hg 12 i
      rw [hg12, Bool.false_xor, Bool.false_xor, h11, h12]
      exact xor_via_nand _ _
    intro ⟨qv, hqv⟩ i
    match qv, hqv with
    | 0, _ => exact h0 i
    | 1, _ => exact h1 i
    | 2, _ => exact h2 i
    | 3, _ => exact h3 i
    | 4, _ => exact h4 i
    | 5, _ => exact h5 i
    | 6, _ => exact h6 i
    | 7, _ => exact h7 i
    | 8, _ => exact h8 i
    | 9, _ => exact h9 i
    | 10, _ => exact h10 i
    | 11, _ => exact h11 i
    | 12, _ => exact h12 i
    | 13, _ => exact h13 i
  have hch_all : ∀ (m : ℕ) (hm : m < r + 1) (side : Bool) (q : Fin 14) (i : Fin k),
      A ⟨m, hm⟩ (chV side q i) = evalChanWire k r x ⟨m, hm⟩ side q i := by
    intro m
    induction m with
    | zero =>
      intro hm side
      apply hstep_layer ⟨0, hm⟩ side
      intro i
      have he := hv.1 ⟨0, hm⟩ (false, side, i)
      dsimp only [vEdgeEnd] at he
      simp only [↓reduceIte, Bool.true_xor, href] at he
      have he' : A ⟨0, hm⟩ (chV side 0 i) ≠ true := by
        simpa only [Bool.false_xor, Bool.not_false] using he
      unfold prevBit
      simp only [↓reduceIte]
      cases hA : A ⟨0, hm⟩ (chV side 0 i)
      · rfl
      · exact absurd hA he'
    | succ m ih =>
      intro hm side
      apply hstep_layer ⟨m + 1, hm⟩ side
      intro i
      have hc := hv.2.1 ⟨m, by omega⟩ (show m < r by omega) (.inr (.inr (side, i)))
      dsimp only [vCarrySrc, vCarryDst] at hc
      rw [← hc, ih (by omega) side 13 i, evalChanWire_out]
      unfold prevBit
      have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
      simp only [hne, ↓reduceIte, Nat.add_sub_cancel]
  have hAeq : A = evalTrace k r x := by
    funext ℓ v
    rcases v with ⟨⟩ | ⟨a, i⟩ | ⟨side, q, i⟩
    · exact href ℓ
    · exact hkey ℓ a i
    · exact hch_all ℓ.val ℓ.isLt side q i
  have hok_side : ∀ side : Bool, chanIter k r side x r < 2 ^ (k - (k + 1) / 2) := by
    intro side
    rw [lt_two_pow_iff_bits (chanIter_lt k r side x r)]
    intro i hi
    have he := hv.1 ⟨r, Nat.lt_succ_self r⟩ (true, side, i)
    dsimp only [vEdgeEnd] at he
    simp only [hi, and_self, ↓reduceIte, Bool.true_xor, href] at he
    rw [hAeq] at he
    have he' : evalChanWire k r x ⟨r, Nat.lt_succ_self r⟩ side 13 i ≠ true := by
      simpa only [evalTrace, Bool.false_xor, Bool.not_false] using he
    rw [evalChanWire_out] at he'
    cases hb : (chanIter k r side x r).testBit i.val
    · rfl
    · exact absurd hb he'
  exact ⟨⟨hok_side false, hok_side true⟩, hAeq⟩

lemma card_lsite (k : ℕ) :
    Fintype.card (LSite (VVar k) (VTri k) (VEdge k) (VCarry k)) = 6 + 1502 * k := by
  simp only [LSite, LCore, HubCore, CornerCore, VVar, VTri, VEdge, VCarry,
    Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, Fintype.card_unit]
  omega

end PEqualNP.Outside.L_pcx_410

theorem PEqualNP.Outside.L_pcx_410 : ∃ C : ℕ, 0 < C ∧ ∀ k r : ℕ,
  let rot := fun (s x : ℕ) => ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2^k
  let step := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1)%k)) && x.testBit ((i+2)%k))).toNat <<< i)) 0
  let c := fun (j : ℕ) => 3^(k+j) % 2^k
  let X := Fin 3 → Fin (2^k)
  let ok := fun (x : X) =>
    let w := (x 2).val
    let f := (List.range r).foldl (fun (p i : ℕ) =>
      let t := i+1
      step (p ^^^ rot 1 p ^^^ rot (k-1) p) ^^^ rot (2*(t-1)) w ^^^ c t)
      (rot 1 w ^^^ (x 0).val)
    let g := (List.range r).foldl (fun (p i : ℕ) =>
      let t := i+1
      step (p ^^^ rot 2 p ^^^ rot (k-2) p) ^^^ rot (3*t+1) w ^^^ c (r+t))
      (rot 3 w ^^^ (x 1).val)
    f < 2^(k-(k+1)/2) ∧ g < 2^(k-(k+1)/2)
  ∃ n T : ℕ, n ≤ C*(k+1)*(r+1) ∧
    let V := Bool × Fin n
    let Y := V → Bool
    ∃ (σ τ : Equiv.Perm (Fin n)) (mark : ((Fin 3 × Fin k) × Bool) ↪ Fin n) (anchor : Fin n),
      (∀ j, mark j ≠ anchor) ∧
      (∀ q : ℕ,
        let cross := fun (π : Equiv.Perm (Fin n)) => (Finset.univ.filter (fun i : Fin n =>
          decide (i.val < q) ≠ decide ((π i).val < q))).card
        cross σ + cross τ ≤ C*(k+1)) ∧
      let cost := fun (y : Y) =>
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
      (∀ y : Y, T ≤ cost y) ∧
      (∀ y : Y, cost y = T → y (false,anchor) = false →
        (Finset.univ.filter (fun p : V => y p = true)).card = n ∧
        ∀ j : Fin 3 × Fin k, y (false,mark (j,true)) = !(y (false,mark (j,false)))) ∧
      ∀ pins : Fin 3 × Fin k → Option Bool,
        (Finset.univ.filter (fun y : Y => cost y = T ∧ y (false,anchor) = false ∧
          ∀ j s, pins j = some s → y (false,mark (j,s)) = false)).card =
        (Finset.univ.filter (fun x : X => ok x ∧
          ∀ j s, pins j = some s → ((x j.1).val.testBit j.2.val) = s)).card := by
  classical
  refine ⟨10000, by decide, ?_⟩
  intro k r rot0 step0 c0 X ok0
  let S := Fintype.card (PEqualNP.Outside.L_pcx_410.LSite
    (PEqualNP.Outside.L_pcx_410.VVar k)
    (PEqualNP.Outside.L_pcx_410.VTri k)
    (PEqualNP.Outside.L_pcx_410.VEdge k)
    (PEqualNP.Outside.L_pcx_410.VCarry k))
  have hS : S = 6 + 1502 * k := PEqualNP.Outside.L_pcx_410.card_lsite k
  let n := (r + 1) * S
  let T := 2 * (r + 1) * Fintype.card (PEqualNP.Outside.L_pcx_410.VTri k)
  have hn : n ≤ 10000 * (k + 1) * (r + 1) := by
    have h1 : S ≤ 10000 * (k + 1) := by omega
    calc n = S * (r + 1) := Nat.mul_comm _ _
      _ ≤ (10000 * (k + 1)) * (r + 1) := Nat.mul_le_mul_right _ h1
  refine ⟨n, T, hn, ?_⟩
  intro V Y
  obtain ⟨eFin, σ, τ, hcross, hlb, hbal, hchar⟩ :=
    PEqualNP.Outside.L_pcx_410.compileLayered
      (PEqualNP.Outside.L_pcx_410.vTriVar k r)
      (PEqualNP.Outside.L_pcx_410.vTriSign k r)
      (PEqualNP.Outside.L_pcx_410.vEdgeEnd k r)
      (@PEqualNP.Outside.L_pcx_410.vCarrySrc k)
      (@PEqualNP.Outside.L_pcx_410.vCarryDst k)
  let mark : ((Fin 3 × Fin k) × Bool) ↪ Fin n :=
    ⟨fun p => eFin (0, .inl (.inl (PEqualNP.Outside.L_pcx_410.keyV p.1.1 p.1.2)), p.2), by
      rintro ⟨⟨a1, i1⟩, s1⟩ ⟨⟨a2, i2⟩, s2⟩ h
      have h1 := eFin.injective h
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h1
      rcases h1 with ⟨_, ⟨⟨rfl, rfl⟩, rfl⟩⟩
      rfl⟩
  let anchor : Fin n := eFin (0, .inl (.inl PEqualNP.Outside.L_pcx_410.refV), false)
  have hdisj : ∀ j, mark j ≠ anchor := by
    rintro ⟨⟨a, i⟩, s⟩ h
    have h1 := eFin.injective h
    simp at h1
  have hcross' : ∀ q : ℕ,
      (Finset.univ.filter (fun i : Fin n =>
        decide (i.val < q) ≠ decide ((σ i).val < q))).card +
      (Finset.univ.filter (fun i : Fin n =>
        decide (i.val < q) ≠ decide ((τ i).val < q))).card ≤ 10000 * (k + 1) := by
    intro q
    have h1 := hcross q
    have hσ_eq : (Finset.univ.filter (fun i : Fin n =>
        decide (i.val < q) ≠ decide ((σ i).val < q))).card =
        PEqualNP.Outside.L_pcx_410.crossCount σ q := by
      unfold PEqualNP.Outside.L_pcx_410.crossCount
      congr 1
    have hτ_eq : (Finset.univ.filter (fun i : Fin n =>
        decide (i.val < q) ≠ decide ((τ i).val < q))).card =
        PEqualNP.Outside.L_pcx_410.crossCount τ q := by
      unfold PEqualNP.Outside.L_pcx_410.crossCount
      congr 1
    rw [hσ_eq, hτ_eq]
    omega
  refine ⟨σ, τ, mark, anchor, hdisj, hcross', ?_⟩
  intro cost
  refine ⟨hlb, ?_, ?_⟩
  · intro y hy _
    have hb := hbal y hy
    refine ⟨hb.1, fun ⟨a, i⟩ => ?_⟩
    exact hb.2 (0, .inl (.inl (PEqualNP.Outside.L_pcx_410.keyV a i)), false)
  · intro pins
    let encY : X → Y := fun x p =>
      PEqualNP.Outside.L_pcx_410.siteVal
        (PEqualNP.Outside.L_pcx_410.vTriVar k r)
        (PEqualNP.Outside.L_pcx_410.vTriSign k r)
        (PEqualNP.Outside.L_pcx_410.vEdgeEnd k r)
        (@PEqualNP.Outside.L_pcx_410.vCarrySrc k)
        (@PEqualNP.Outside.L_pcx_410.vCarryDst k)
        (PEqualNP.Outside.L_pcx_410.evalTrace k r x)
        (eFin.symm p.2)
    have hok_eq : ∀ x : X, ok0 x ↔
        (PEqualNP.Outside.L_pcx_410.chanIter k r false x r < 2 ^ (k - (k + 1) / 2) ∧
         PEqualNP.Outside.L_pcx_410.chanIter k r true x r < 2 ^ (k - (k + 1) / 2)) :=
      fun _ => Iff.rfl
    have henc_anchor : ∀ x : X, encY x (false, anchor) = false := fun x => by
      dsimp only [encY, anchor]
      rw [Equiv.symm_apply_apply]
      rfl
    have henc_mark : ∀ (x : X) (a : Fin 3) (i : Fin k) (s : Bool),
        encY x (false, mark ((a, i), s)) = xor s ((x a).val.testBit i.val) := fun x a i s => by
      change PEqualNP.Outside.L_pcx_410.siteVal _ _ _ _ _ _
        (eFin.symm (eFin (0, .inl (.inl (PEqualNP.Outside.L_pcx_410.keyV a i)), s))) = _
      rw [Equiv.symm_apply_apply]
      simp [PEqualNP.Outside.L_pcx_410.siteVal, PEqualNP.Outside.L_pcx_410.hubInfo,
        PEqualNP.Outside.L_pcx_410.evalTrace]
    symm
    apply Finset.card_nbij encY
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_, henc_anchor x, ?_⟩
      · exact (hchar (encY x)).mpr
          ⟨PEqualNP.Outside.L_pcx_410.evalTrace k r x,
           PEqualNP.Outside.L_pcx_410.evalTrace_valid k r x ((hok_eq x).mp hx.2.1), rfl⟩
      · intro ⟨a, i⟩ s hs
        rw [henc_mark x a i s, hx.2.2 (a, i) s hs]
        exact Bool.xor_self s
    · intro x1 _ x2 _ heq
      funext a
      rw [← PEqualNP.Outside.L_pcx_410.packFin_bits k (x1 a),
          ← PEqualNP.Outside.L_pcx_410.packFin_bits k (x2 a)]
      congr 1
      funext i
      have h1 := congrFun heq (false, mark ((a, i), false))
      rw [henc_mark, henc_mark] at h1
      simpa using h1
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_filter] at hy
      obtain ⟨A, hAv, rfl⟩ := (hchar y).mp hy.2.1
      have href0 : A 0 PEqualNP.Outside.L_pcx_410.refV = false := by
        have ha := hy.2.2.1
        dsimp only [anchor] at ha
        rw [Equiv.symm_apply_apply] at ha
        simpa [PEqualNP.Outside.L_pcx_410.siteVal, PEqualNP.Outside.L_pcx_410.hubInfo] using ha
      obtain ⟨hokx, hAeq⟩ := PEqualNP.Outside.L_pcx_410.valid_imp_evalTrace k r A hAv href0
      let x : X := fun a => PEqualNP.Outside.L_pcx_410.packFin k (fun i =>
        A 0 (PEqualNP.Outside.L_pcx_410.keyV a i))
      have hAeq' : A = PEqualNP.Outside.L_pcx_410.evalTrace k r x := hAeq
      refine ⟨x, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (hok_eq x).mpr hokx, ?_⟩
        intro ⟨a, i⟩ s hs
        have hp : encY x (false, mark ((a, i), s)) = false := by
          have h0 := hy.2.2.2 (a, i) s hs
          rw [hAeq'] at h0
          exact h0
        rw [henc_mark x a i s] at hp
        change (x a).val.testBit i.val = s
        cases hs1 : s <;> cases hb : (x a).val.testBit i.val <;> simp [hs1, hb] at hp ⊢
      · rw [hAeq']
