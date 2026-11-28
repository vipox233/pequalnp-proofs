import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32591_aux

open Finset

def sg (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

lemma sg0 : sg 0 = 1 := by decide
lemma sg1 : sg 1 = -1 := by decide
lemma z11 : (1 : ZMod 2) + 1 = 0 := by decide

lemma sg_le (z : ZMod 2) : sg z ≤ 1 := by unfold sg; split_ifs <;> norm_num

lemma zz (x : ZMod 2) : x + x = 0 := by revert x; decide

lemma z01 (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

abbrev V (k : ℕ) := Fin k → ZMod 2

lemma vv {k : ℕ} (x : V k) : x + x = 0 := by funext j; exact zz (x j)

lemma sg_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

lemma univZ2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

lemma orth {k : ℕ} (v : V k) :
    ∑ γ : V k, sg (dotProduct γ v) = if v = 0 then (2:ℤ)^k else 0 := by
  have h1 : ∀ γ : V k, sg (dotProduct γ v) = ∏ j, sg (γ j * v j) := fun γ => by
    rw [dotProduct, sg_sum]
  simp only [h1]
  rw [← Fintype.prod_sum (fun j (a : ZMod 2) => sg (a * v j))]
  have h2 : ∀ j, ∑ a : ZMod 2, sg (a * v j) = if v j = 0 then 2 else 0 := by
    intro j
    rw [univZ2, Finset.sum_pair (by decide)]
    rcases z01 (v j) with h | h <;> rw [h] <;> decide
  simp only [h2]
  rw [Finset.prod_ite_zero]
  by_cases hv : v = 0
  · subst hv; simp
  · have : ¬ ∀ i ∈ (Finset.univ : Finset (Fin k)), v i = 0 := by
      intro h; apply hv; funext i; exact h i (Finset.mem_univ _)
    rw [if_neg this, if_neg hv]

lemma orth' {k : ℕ} (v : V k) :
    ∑ x : V k, sg (dotProduct v x) = if v = 0 then (2:ℤ)^k else 0 := by
  rw [← orth v]; simp only [dotProduct_comm v]

lemma cardV (k : ℕ) : ((Finset.univ : Finset (V k)).card : ℤ) = 2^k := by
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]; push_cast; ring

lemma charsum {k : ℕ} (f : V k → ZMod 2) (hf : ∀ x y, f (x + y) = f x + f y) :
    ∑ y : V k, sg (f y) = if ∀ y, f y = 0 then (2:ℤ)^k else 0 := by
  split_ifs with h
  · simp only [h, sg0]
    rw [Finset.sum_const, nsmul_eq_mul, cardV, mul_one]
  · push_neg at h
    obtain ⟨y0, hy0⟩ := h
    have h1 : f y0 = 1 := by
      rcases z01 (f y0) with h' | h'
      · exact absurd h' hy0
      · exact h'
    have e : ∑ y : V k, sg (f (y + y0)) = ∑ y : V k, sg (f y) :=
      Equiv.sum_comp (Equiv.addRight y0) (fun y => sg (f y))
    have e2 : ∑ y : V k, sg (f (y + y0)) = - ∑ y : V k, sg (f y) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hf, h1, sg_add, sg1]; ring
    linarith

/-! parity split -/

section Split
variable {k : ℕ}

def pe (x : V k) : V k := fun j => if j.val % 2 = 0 then x j else 0
def po (x : V k) : V k := fun j => if j.val % 2 = 0 then 0 else x j

lemma pe_add (x y : V k) : pe (x + y) = pe x + pe y := by
  funext j; simp only [pe, Pi.add_apply]; split_ifs <;> simp

lemma po_add (x y : V k) : po (x + y) = po x + po y := by
  funext j; simp only [po, Pi.add_apply]; split_ifs <;> simp

lemma pe_po (x : V k) : pe x + po x = x := by
  funext j; simp only [pe, po, Pi.add_apply]; split_ifs <;> simp

lemma pe_mix (x y : V k) : pe (pe x + po y) = pe x := by
  funext j; simp only [pe, po, Pi.add_apply]; split_ifs <;> simp

lemma po_mix (x y : V k) : po (pe x + po y) = po y := by
  funext j; simp only [pe, po, Pi.add_apply]; split_ifs <;> simp

def swp : V k × V k ≃ V k × V k :=
  Function.Involutive.toPerm (fun p => (pe p.1 + po p.2, pe p.2 + po p.1)) (by
    intro p
    refine Prod.ext ?_ ?_
    · show pe (pe p.1 + po p.2) + po (pe p.2 + po p.1) = p.1
      rw [pe_mix, po_mix, pe_po]
    · show pe (pe p.2 + po p.1) + po (pe p.1 + po p.2) = p.2
      rw [pe_mix, po_mix, pe_po])

lemma swapsum (G : V k → ℤ) :
    ∑ x : V k, ∑ y : V k, G (pe x + po y) = 2^k * ∑ w, G w := by
  rw [← Fintype.sum_prod_type' (f := fun x y => G (pe x + po y))]
  have e := Equiv.sum_comp (swp (k := k)) (fun q => G q.1)
  have e' : ∑ p : V k × V k, G (pe p.1 + po p.2) = ∑ q : V k × V k, G q.1 := e
  rw [e', Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul, cardV]
  rw [Finset.mul_sum]

lemma key (Q ℓ : V k → ZMod 2) (c : ZMod 2)
    (hQ1 : ∀ x x' y, Q (pe (x + x') + po y) = Q (pe x + po y) + Q (pe x' + po y))
    (hQ2 : ∀ x y y', Q (pe x + po (y + y')) = Q (pe x + po y) + Q (pe x + po y'))
    (hℓ : ∀ x y, ℓ (x + y) = ℓ x + ℓ y) :
    ∑ w, sg (Q w + ℓ w + c) ≤ ∑ w, sg (Q w) := by
  classical
  have hpos : (0:ℤ) < 2^k := by positivity
  have inner : ∀ x : V k, ∑ y : V k, sg (Q (pe x + po y) + ℓ (pe x + po y) + c) =
      sg (ℓ (pe x) + c) *
        (if ∀ y, Q (pe x + po y) + ℓ (po y) = 0 then (2:ℤ)^k else 0) := by
    intro x
    rw [← charsum (fun y => Q (pe x + po y) + ℓ (po y)) (by
      intro y y'
      show Q (pe x + po (y + y')) + ℓ (po (y + y')) =
        (Q (pe x + po y) + ℓ (po y)) + (Q (pe x + po y') + ℓ (po y'))
      rw [hQ2, po_add, hℓ]; ring), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hℓ, ← sg_add]; congr 1; ring
  have inner0 : ∀ x : V k, ∑ y : V k, sg (Q (pe x + po y)) =
      (if ∀ y, Q (pe x + po y) = 0 then (2:ℤ)^k else 0) :=
    fun x => charsum (fun y => Q (pe x + po y)) (fun y y' => hQ2 x y y')
  have L : (2:ℤ)^k * ∑ w, sg (Q w + ℓ w + c) = ∑ x : V k, sg (ℓ (pe x) + c) *
      (if ∀ y, Q (pe x + po y) + ℓ (po y) = 0 then (2:ℤ)^k else 0) := by
    rw [← swapsum (fun w => sg (Q w + ℓ w + c))]
    exact Finset.sum_congr rfl (fun x _ => inner x)
  have R : (2:ℤ)^k * ∑ w, sg (Q w) =
      ∑ x : V k, (if ∀ y, Q (pe x + po y) = 0 then (2:ℤ)^k else 0) := by
    rw [← swapsum (fun w => sg (Q w))]
    exact Finset.sum_congr rfl (fun x _ => inner0 x)
  have B1 : ∑ x : V k, sg (ℓ (pe x) + c) *
      (if ∀ y, Q (pe x + po y) + ℓ (po y) = 0 then (2:ℤ)^k else 0)
      ≤ ∑ x : V k, (if ∀ y, Q (pe x + po y) + ℓ (po y) = 0 then (2:ℤ)^k else 0) := by
    apply Finset.sum_le_sum; intro x _
    split_ifs
    · have := sg_le (ℓ (pe x) + c); nlinarith
    · simp
  have B2 : ∑ x : V k, (if ∀ y, Q (pe x + po y) + ℓ (po y) = 0 then (2:ℤ)^k else 0) ≤
      ∑ x : V k, (if ∀ y, Q (pe x + po y) = 0 then (2:ℤ)^k else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hpos.le
    norm_cast
    rcases (Finset.univ.filter (fun x : V k => ∀ y, Q (pe x + po y) + ℓ (po y) = 0)).eq_empty_or_nonempty
      with hE | ⟨x0, hx0⟩
    · rw [hE]; simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0
      apply Finset.card_le_card_of_injOn (fun x => x + x0)
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
        intro y
        rw [hQ1]
        have two : (2 : ZMod 2) = 0 := rfl
        linear_combination hx y + hx0 y - ℓ (po y) * two
      · intro x _ x' _ h
        exact add_right_cancel h
  exact le_of_mul_le_mul_left (by linarith [L, R, B1, B2]) hpos

end Split

end PEqualNP.Outside.L_meta_32591_aux

namespace PEqualNP.Outside.L_meta_32591_aux

open Finset

/-! index shifts -/

section Mix
variable {n : ℕ} (hn : 0 < n)

def ix (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩
def rot (s : ℕ) (w : V n) (i : Fin n) : ZMod 2 := w (ix hn (i.val + n - s % n))
def mm (x : V n) (j : Fin n) : ZMod 2 := x j + x (ix hn (j.val+2)) + x (ix hn (j.val+n-2))
def out (name c raw : V n) (i : Fin n) : ZMod 2 :=
  let old := rot hn 3 raw + name
  let y := fun j : Fin n => old j + old (ix hn (j.val+2)) + old (ix hn (j.val+n-2))
  y i + (1+y (ix hn (i.val+1)))*y (ix hn (i.val+2)) + rot hn 4 raw i + c i

def Y (w : V n) : V n := mm hn (rot hn 3 w)
def Phi (w : V n) : V n := fun i => Y hn w (ix hn (i.val+1)) * Y hn w (ix hn (i.val+2))

lemma mm_add (x y : V n) : mm hn (x + y) = mm hn x + mm hn y := by
  funext j; simp only [mm, Pi.add_apply]; ring

lemma rot_add (s : ℕ) (x y : V n) : rot hn s (x + y) = rot hn s x + rot hn s y := rfl

lemma Y_add (x y : V n) : Y hn (x + y) = Y hn x + Y hn y := by
  simp only [Y, rot_add, mm_add]

lemma ix_par (h2 : 2 ∣ n) (j : ℕ) : (ix hn j).val % 2 = j % 2 := Nat.mod_mod_of_dvd j h2

lemma Y_pe (h2 : 2 ∣ n) (h4 : 4 ≤ n) (x : V n) (j : Fin n) (hj : j.val % 2 = 0) :
    Y hn (pe x) j = 0 := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  have key : ∀ i : Fin n, i.val % 2 = 0 → rot hn 3 (pe x) i = 0 := by
    intro i hi
    have : (ix hn (i.val + n - 3 % n)).val % 2 ≠ 0 := by
      rw [ix_par hn h2, h3]; omega
    simp only [rot, pe, this, if_false]
  simp only [Y, mm]
  rw [key j hj, key _ (by rw [ix_par hn h2]; omega), key _ (by rw [ix_par hn h2]; omega)]
  simp

lemma Y_po (h2 : 2 ∣ n) (h4 : 4 ≤ n) (x : V n) (j : Fin n) (hj : j.val % 2 = 1) :
    Y hn (po x) j = 0 := by
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  have key : ∀ i : Fin n, i.val % 2 = 1 → rot hn 3 (po x) i = 0 := by
    intro i hi
    have : (ix hn (i.val + n - 3 % n)).val % 2 = 0 := by
      rw [ix_par hn h2, h3]; omega
    simp only [rot, po, this, if_true]
  simp only [Y, mm]
  rw [key j hj, key _ (by rw [ix_par hn h2]; omega), key _ (by rw [ix_par hn h2]; omega)]
  simp

lemma split_prod (h2 : 2 ∣ n) (h4 : 4 ≤ n) (x y : V n) (i : Fin n) :
    Y hn (pe x + po y) (ix hn (i.val+1)) * Y hn (pe x + po y) (ix hn (i.val+2)) =
    Y hn (pe x) (ix hn (i.val+1)) * Y hn (po y) (ix hn (i.val+2)) +
      Y hn (po y) (ix hn (i.val+1)) * Y hn (pe x) (ix hn (i.val+2)) := by
  rw [Y_add]; simp only [Pi.add_apply]
  have hp := ix_par hn h2 (i.val+1)
  have hq := ix_par hn h2 (i.val+2)
  rcases Nat.mod_two_eq_zero_or_one (i.val+1) with h | h
  · have a0 : Y hn (pe x) (ix hn (i.val+1)) = 0 := Y_pe hn h2 h4 x _ (by omega)
    have b0 : Y hn (po y) (ix hn (i.val+2)) = 0 := Y_po hn h2 h4 y _ (by omega)
    rw [a0, b0]; ring
  · have a0 : Y hn (pe x) (ix hn (i.val+2)) = 0 := Y_pe hn h2 h4 x _ (by omega)
    have b0 : Y hn (po y) (ix hn (i.val+1)) = 0 := Y_po hn h2 h4 y _ (by omega)
    rw [a0, b0]; ring

lemma hQ1 (h2 : 2 ∣ n) (h4 : 4 ≤ n) (u : V n) (x x' y : V n) :
    dotProduct u (Phi hn (pe (x + x') + po y)) =
      dotProduct u (Phi hn (pe x + po y)) + dotProduct u (Phi hn (pe x' + po y)) := by
  simp only [dotProduct, Phi]
  simp only [split_prod hn h2 h4]
  simp only [pe_add, Y_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma hQ2 (h2 : 2 ∣ n) (h4 : 4 ≤ n) (u : V n) (x y y' : V n) :
    dotProduct u (Phi hn (pe x + po (y + y'))) =
      dotProduct u (Phi hn (pe x + po y)) + dotProduct u (Phi hn (pe x + po y')) := by
  simp only [dotProduct, Phi]
  simp only [split_prod hn h2 h4]
  simp only [po_add, Y_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

def Lp (name : V n) (A : V n →ₗ[ZMod 2] V n) (w : V n) : V n := fun i =>
  Y hn w i + Y hn w (ix hn (i.val+2)) + Y hn w (ix hn (i.val+1)) * mm hn name (ix hn (i.val+2)) +
    mm hn name (ix hn (i.val+1)) * Y hn w (ix hn (i.val+2)) + rot hn 4 w i - A w i

def dp (name c b : V n) : V n := fun i =>
  mm hn name i + mm hn name (ix hn (i.val+2)) +
    mm hn name (ix hn (i.val+1)) * mm hn name (ix hn (i.val+2)) + c i - b i

lemma out_mm (name c w : V n) (i : Fin n) : out hn name c w i =
    mm hn (rot hn 3 w + name) i + (1 + mm hn (rot hn 3 w + name) (ix hn (i.val+1))) *
      mm hn (rot hn 3 w + name) (ix hn (i.val+2)) + rot hn 4 w i + c i := rfl

lemma P_eq (name c b : V n) (A : V n →ₗ[ZMod 2] V n) (w : V n) :
    out hn name c w - (A w + b) = Phi hn w + Lp hn name A w + dp hn name c b := by
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, out_mm, mm_add, Phi, Lp, dp, Y]
  ring

lemma Lp_add (name : V n) (A : V n →ₗ[ZMod 2] V n) (x y : V n) :
    Lp hn name A (x + y) = Lp hn name A x + Lp hn name A y := by
  funext i
  simp only [Lp, Y_add, rot_add, map_add, Pi.add_apply]
  ring

lemma card_eq (p : V n → Prop) :
    (Nat.card {w : V n // p w} : ℤ) = ∑ w : V n, @ite ℤ (p w) (Classical.propDecidable _) 1 0 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

theorem upper (h2 : 2 ∣ n) (h4 : 4 ≤ n) (name c b : V n) (A : V n →ₗ[ZMod 2] V n) :
    (Nat.card {w : V n // out hn name c w = A w + b} : ℤ) ≤
      ∑ w : V n, @ite ℤ (Phi hn w = 0) (Classical.propDecidable _) 1 0 := by
  classical
  rw [card_eq]
  have hpos : (0:ℤ) < 2^n := by positivity
  apply le_of_mul_le_mul_left _ hpos
  have e1 : ∀ w, (2:ℤ)^n * @ite ℤ (out hn name c w = A w + b) (Classical.propDecidable _) 1 0 =
      ∑ u : V n, sg (dotProduct u (out hn name c w - (A w + b))) := by
    intro w; rw [orth]; simp only [sub_eq_zero]; split_ifs <;> simp
  have e2 : ∀ w, (2:ℤ)^n * @ite ℤ (Phi hn w = 0) (Classical.propDecidable _) 1 0 =
      ∑ u : V n, sg (dotProduct u (Phi hn w)) := by
    intro w; rw [orth]; split_ifs <;> simp
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl (fun w _ => e1 w),
    Finset.sum_congr rfl (fun w _ => e2 w), Finset.sum_comm,
    Finset.sum_comm (f := fun w u => sg (dotProduct u (Phi hn w)))]
  apply Finset.sum_le_sum; intro u _
  simp only [P_eq, dotProduct_add]
  exact key (fun w => dotProduct u (Phi hn w)) (fun w => dotProduct u (Lp hn name A w))
    (dotProduct u (dp hn name c b)) (hQ1 hn h2 h4 u) (hQ2 hn h2 h4 u)
    (fun x y => by simp only [Lp_add, dotProduct_add])

end Mix

end PEqualNP.Outside.L_meta_32591_aux

namespace PEqualNP.Outside.L_meta_32591_aux

open Finset

lemma mod_back {k : ℕ} (a j : ℕ) (hk : 0 < k) (hj : j < k) :
    ((j + a) % k + k - a % k) % k = j := by
  have ha : a % k < k := Nat.mod_lt _ hk
  rw [Nat.add_mod j a k, Nat.mod_eq_of_lt hj]
  generalize a % k = c at ha ⊢
  by_cases h : j + c < k
  · rw [Nat.mod_eq_of_lt h, show j + c + k - c = j + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  · have e : (j + c) % k = j + c - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e, show j + c - k + k - c = j by omega, Nat.mod_eq_of_lt hj]

lemma mod_fwd {k : ℕ} (a i : ℕ) (hk : 0 < k) (hi : i < k) :
    ((i + k - a % k) % k + a) % k = i := by
  have ha : a % k < k := Nat.mod_lt _ hk
  rw [Nat.add_mod _ a k, Nat.mod_mod]
  generalize a % k = c at ha ⊢
  by_cases h : c ≤ i
  · rw [show i + k - c = (i - c) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : i - c < k), show i - c + c = i by omega, Nat.mod_eq_of_lt hi]
  · rw [Nat.mod_eq_of_lt (by omega : i + k - c < k), show i + k - c + c = i + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

section Rot
variable {n : ℕ} (hn : 0 < n)

def shiftE (a : ℕ) : Fin n ≃ Fin n where
  toFun j := ix hn (j.val + a)
  invFun i := ix hn (i.val + n - a % n)
  left_inv j := Fin.ext (by simp only [ix]; exact mod_back a j.val hn j.isLt)
  right_inv i := Fin.ext (by simp only [ix]; exact mod_fwd a i.val hn i.isLt)

def rotE (s : ℕ) (v : V n) : V n ≃ V n :=
  (Equiv.arrowCongr (shiftE hn s) (Equiv.refl (ZMod 2))).trans (Equiv.addRight v)

lemma rotE_apply (s : ℕ) (v w : V n) : rotE hn s v w = rot hn s w + v := rfl

lemma sum_rot (s : ℕ) (v : V n) (G : V n → ℤ) : ∑ w, G (rot hn s w + v) = ∑ x, G x := by
  have := Equiv.sum_comp (rotE hn s v) G
  simpa only [rotE_apply] using this

noncomputable def Fi (y : V n) : ℤ :=
  @ite ℤ (∀ i : Fin n, y (ix hn (i.val+1)) * y (ix hn (i.val+2)) = 0) (Classical.propDecidable _) 1 0

lemma phi_sum : ∑ w : V n, @ite ℤ (Phi hn w = 0) (Classical.propDecidable _) 1 0 =
    ∑ x, Fi hn (mm hn x) := by
  rw [← sum_rot hn 3 0 (fun x => Fi hn (mm hn x))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [add_zero, Fi]
  by_cases h : Phi hn w = 0
  · rw [if_pos h, if_pos]; intro i; exact congrFun h i
  · rw [if_neg h, if_neg]; intro h'; exact h (funext h')

def Astar : V n →ₗ[ZMod 2] V n where
  toFun w := fun i => Y hn w i + Y hn w (ix hn (i.val+2)) + rot hn 4 w i
  map_add' x y := by funext i; simp only [Y_add, rot_add, Pi.add_apply]; ring
  map_smul' a x := by
    funext i; simp only [Y, mm, rot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def bstar (name c : V n) : V n := fun i => mm hn name i + mm hn name (ix hn (i.val+2)) + c i

lemma lower (name c : V n) :
    (Nat.card {w : V n // out hn name c w = Astar hn w + bstar hn name c} : ℤ) =
      ∑ x, Fi hn (mm hn x) := by
  rw [card_eq, ← sum_rot hn 3 name (fun x => Fi hn (mm hn x))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have e : ∀ i, out hn name c w i = (Astar hn w + bstar hn name c) i +
      mm hn (rot hn 3 w + name) (ix hn (i.val+1)) * mm hn (rot hn 3 w + name) (ix hn (i.val+2)) := by
    intro i
    simp only [out_mm, mm_add, Astar, bstar, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Y]
    ring
  unfold Fi
  by_cases h : ∀ i : Fin n, mm hn (rot hn 3 w + name) (ix hn (i.val+1)) *
      mm hn (rot hn 3 w + name) (ix hn (i.val+2)) = 0
  · rw [if_pos h, if_pos]; funext i; rw [e i, h i, add_zero]
  · rw [if_neg h, if_neg]; intro h'; apply h; intro i
    have := e i
    rw [congrFun h' i] at this
    linear_combination -this

lemma ix_two (m : ℕ) : ix hn (m + 2) = ix hn ((ix hn (m+1)).val + 1) := by
  apply Fin.ext
  show (m+2) % n = ((m+1) % n + 1) % n
  rw [Nat.add_mod ((m+1) % n), Nat.mod_mod, ← Nat.add_mod]

lemma Fi_shift (y : V n) : (∀ i : Fin n, y (ix hn (i.val+1)) * y (ix hn (i.val+2)) = 0) ↔
    (∀ j : Fin n, y j * y (ix hn (j.val+1)) = 0) := by
  constructor
  · intro h j
    have := h ((shiftE hn 1).symm j)
    have e1 : ix hn (((shiftE hn 1).symm j).val + 1) = j := (shiftE hn 1).apply_symm_apply j
    rw [ix_two, e1] at this
    exact this
  · intro h i
    rw [ix_two]; exact h _

lemma mm_sym (h3 : 2 < n) (γ x : V n) :
    dotProduct γ (mm hn x) = dotProduct (mm hn γ) x := by
  have e1 : ∀ j : Fin n, ix hn (j.val + 2) = shiftE hn 2 j := fun _ => rfl
  have e2 : ∀ j : Fin n, ix hn (j.val + n - 2) = (shiftE hn 2).symm j := fun j => by
    show ix hn (j.val + n - 2) = ix hn (j.val + n - 2 % n)
    rw [Nat.mod_eq_of_lt h3]
  simp only [dotProduct, mm, e1, e2, mul_add, add_mul, Finset.sum_add_distrib]
  have s1 : ∑ j, γ j * x (shiftE hn 2 j) = ∑ i, γ ((shiftE hn 2).symm i) * x i := by
    rw [← Equiv.sum_comp (shiftE hn 2).symm]; simp
  have s2 : ∑ j, γ j * x ((shiftE hn 2).symm j) = ∑ i, γ (shiftE hn 2 i) * x i := by
    rw [← Equiv.sum_comp (shiftE hn 2)]; simp
  rw [s1, s2]; ring

end Rot

theorem fourier {k : ℕ} (M : V k → V k) (hlin : ∀ x y, M (x + y) = M x + M y)
    (hsym : ∀ x y, dotProduct x (M y) = dotProduct (M x) y) (F : V k → ℤ) (b : V k) :
    ∑ x, F (M x) * sg (dotProduct b x) =
      ∑ γ ∈ Finset.univ.filter (fun γ => M γ = b), ∑ y, F y * sg (dotProduct γ y) := by
  have two : (2 : ZMod 2) = 0 := rfl
  have hpos : (0:ℤ) < 2^k := by positivity
  apply mul_left_cancel₀ hpos.ne'
  have L1 : ∀ x, (2:ℤ)^k * (F (M x) * sg (dotProduct b x)) =
      ∑ y, ∑ γ, F y * sg (dotProduct b x) * sg (dotProduct γ (y + M x)) := by
    intro x
    simp only [← Finset.mul_sum, orth]
    have : ∀ y, (y + M x = 0 ↔ y = M x) := fun y => by
      constructor
      · intro h
        have := congrArg (· + M x) h
        simpa [add_assoc, vv] using this
      · rintro rfl; exact vv _
    simp only [this, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq']; simp only [Finset.mem_univ, if_true]; ring
  have R1 : ∀ γ, (2:ℤ)^k * (if M γ = b then ∑ y, F y * sg (dotProduct γ y) else 0) =
      ∑ y, ∑ x, F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x) := by
    intro γ
    simp only [← Finset.mul_sum, orth']
    have : (b + M γ = 0 ↔ M γ = b) := by
      constructor
      · intro h
        funext j
        have := congrFun h j
        simp only [Pi.add_apply, Pi.zero_apply] at this
        linear_combination this - b j * two
      · intro h; rw [h]; exact vv _
    simp only [this]
    split_ifs
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun y _ => by ring)
    · simp
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun x _ => L1 x)]
  rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_congr rfl (fun γ _ => R1 γ)]
  have pt : ∀ x y γ, F y * sg (dotProduct b x) * sg (dotProduct γ (y + M x)) =
      F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x) := by
    intro x y γ
    rw [dotProduct_add, add_dotProduct, hsym, sg_add, sg_add]; ring
  simp only [pt]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (V k))) (t := (Finset.univ : Finset (V k)))
    (f := fun γ y => ∑ x, F y * sg (dotProduct γ y) * sg (dotProduct (b + M γ) x))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_comm]

end PEqualNP.Outside.L_meta_32591_aux

namespace PEqualNP.Outside.L_meta_32591_aux

open Finset

/-! kernel of the mixer at widths divisible by six -/

def pat (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (r : ℕ) : ZMod 2 :=
  if r % 6 = 0 then a.1 else if r % 6 = 1 then a.2.1 else if r % 6 = 2 then a.2.2.1
  else if r % 6 = 3 then a.2.2.2 else if r % 6 = 4 then a.1 + a.2.2.1 else a.2.1 + a.2.2.2

lemma pat_mod (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (r s : ℕ) (h : r % 6 = s % 6) :
    pat a r = pat a s := by simp only [pat, h]

lemma pat_rec (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (r : ℕ) :
    pat a r + pat a (r+2) + pat a (r+4) = 0 := by
  rw [pat_mod a r (r % 6) (Nat.mod_mod r 6).symm, pat_mod a (r+2) (r % 6 + 2) (by omega),
    pat_mod a (r+4) (r % 6 + 4) (by omega)]
  obtain ⟨a0, a1, a2, a3⟩ := a
  have : r % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize r % 6 = m at this ⊢
  interval_cases m <;> simp [pat] <;> revert a0 a1 a2 a3 <;> decide

def kap (n : ℕ) (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : V n := fun j => pat a j.val

section Ker
variable {n : ℕ} (hn : 0 < n)

lemma kap_ker (h6 : 6 ∣ n) (h6' : 6 ≤ n) (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    mm hn (kap n a) = 0 := by
  funext j
  simp only [mm, kap, ix, Pi.zero_apply]
  rw [pat_mod a ((j.val + 2) % n) (j.val + 2) (Nat.mod_mod_of_dvd _ h6),
    pat_mod a ((j.val + n - 2) % n) (j.val + 4) (by rw [Nat.mod_mod_of_dvd _ h6]; omega)]
  exact pat_rec a j.val

lemma ker_eq (h6' : 6 ≤ n) (γ : V n) (hγ : mm hn γ = 0) :
    γ = kap n (γ (ix hn 0), γ (ix hn 1), γ (ix hn 2), γ (ix hn 3)) := by
  set a := (γ (ix hn 0), γ (ix hn 1), γ (ix hn 2), γ (ix hn 3)) with ha
  have main : ∀ j (hj : j < n), γ ⟨j, hj⟩ = pat a j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      by_cases h : j < 4
      · have e : (⟨j, hj⟩ : Fin n) = ix hn j := Fin.ext (by simp [ix, Nat.mod_eq_of_lt hj])
        rw [e]
        interval_cases j <;> simp [pat, ha]
      · have hz := congrFun hγ ⟨j - 2, by omega⟩
        simp only [mm, Pi.zero_apply, Fin.val_mk] at hz
        have a1 : ix hn (j - 2 + 2) = ⟨j, hj⟩ := Fin.ext (by
          simp only [ix]; rw [show j - 2 + 2 = j by omega, Nat.mod_eq_of_lt hj])
        have a2 : ix hn (j - 2 + n - 2) = ⟨j - 4, by omega⟩ := Fin.ext (by
          simp only [ix]
          rw [show j - 2 + n - 2 = (j - 4) + n by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)])
        rw [a1, a2, ih (j - 2) (by omega) (by omega), ih (j - 4) (by omega) (by omega)] at hz
        have hr := pat_rec a (j - 4)
        rw [show j - 4 + 2 = j - 2 by omega, show j - 4 + 4 = j by omega] at hr
        linear_combination hz - hr
  funext j
  exact main j.val j.isLt

lemma ker_sum (h6 : 6 ∣ n) (h6' : 6 ≤ n) (H : V n → ℤ) :
    ∑ γ ∈ univ.filter (fun γ => mm hn γ = 0), H γ =
      ∑ a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2, H (kap n a) := by
  symm
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : 2 % n = 2 := Nat.mod_eq_of_lt (by omega)
  have h3 : 3 % n = 3 := Nat.mod_eq_of_lt (by omega)
  apply Finset.sum_nbij' (fun a => kap n a)
    (fun γ => (γ (ix hn 0), γ (ix hn 1), γ (ix hn 2), γ (ix hn 3)))
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact kap_ker hn h6 h6' a
  · intro γ _; exact Finset.mem_univ _
  · intro a _
    obtain ⟨a0, a1, a2, a3⟩ := a
    simp [kap, ix, pat, h1, h2, h3]
  · intro γ hγ
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    exact (ker_eq hn h6' γ hγ).symm
  · intro a _; rfl

end Ker

/-! cyclic transfer -/

def runD (φ : ℕ → Bool → Bool → ℤ) (st : Bool) : ℕ → Bool → ℤ
  | 0 => fun v => if v = st then 1 else 0
  | i+1 => fun v => runD φ st i false * φ i false v + runD φ st i true * φ i true v

lemma sum_snoc {M : Type} [AddCommMonoid M] (j : ℕ) (F : (Fin (j+1) → Bool) → M) :
    ∑ y, F y = ∑ y : Fin j → Bool, ∑ w : Bool, F (Fin.snoc y w) := by
  rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

def pathP (φ : ℕ → Bool → Bool → ℤ) (j : ℕ) (y : Fin (j+1) → Bool) : ℤ :=
  ∏ i : Fin j, φ i (y i.castSucc) (y i.succ)

lemma pathP_snoc (φ : ℕ → Bool → Bool → ℤ) (j : ℕ) (y : Fin (j+1) → Bool) (w : Bool) :
    pathP φ (j+1) (Fin.snoc y w) = pathP φ j y * φ j (y (Fin.last j)) w := by
  unfold pathP
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc]
  · simp

lemma snoc0 {j : ℕ} (y : Fin (j+1) → Bool) (w : Bool) :
    (Fin.snoc y w : Fin (j+2) → Bool) 0 = y 0 := by
  have : (0 : Fin (j+2)) = Fin.castSucc 0 := rfl
  rw [this, Fin.snoc_castSucc]

lemma runD_path (φ : ℕ → Bool → Bool → ℤ) (st : Bool) : ∀ j v, runD φ st j v =
    ∑ y : Fin (j+1) → Bool, if y 0 = st ∧ y (Fin.last j) = v then pathP φ j y else 0 := by
  intro j
  induction j with
  | zero =>
    intro v
    rw [sum_snoc]
    simp only [runD, pathP, Finset.univ_unique, Finset.sum_singleton, Fintype.sum_bool,
      Finset.univ_eq_empty, Finset.prod_empty]
    cases st <;> cases v <;> simp [Fin.snoc]
  | succ j ih =>
    intro v
    rw [sum_snoc]
    simp only [runD, ih]
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Fintype.sum_bool]
    simp only [pathP_snoc, Fin.snoc_last, snoc0]
    cases hl : y (Fin.last j) <;> cases v <;> by_cases h0 : y 0 = st <;> simp [h0, hl]

theorem chain (k : ℕ) (hk : 0 < k) (φ : ℕ → Bool → Bool → ℤ) :
    runD φ false k false + runD φ true k true =
      ∑ y : Fin k → Bool, ∏ i : Fin k, φ i (y i) (y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) := by
  rw [runD_path, runD_path, ← Finset.sum_add_distrib]
  have e : ∀ y : Fin (k+1) → Bool,
      ((if y 0 = false ∧ y (Fin.last k) = false then pathP φ k y else 0) +
        (if y 0 = true ∧ y (Fin.last k) = true then pathP φ k y else 0)) =
      if y 0 = y (Fin.last k) then pathP φ k y else 0 := by
    intro y; cases h0 : y 0 <;> cases hl : y (Fin.last k) <;> simp
  rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_filter]
  apply Finset.sum_nbij' (fun y => fun i : Fin k => y i.castSucc)
    (fun z => fun i : Fin (k+1) => z ⟨i.val % k, Nat.mod_lt _ hk⟩)
  · intros; simp
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero, Fin.val_last,
      Nat.zero_mod, Nat.mod_self]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    funext i
    rcases Nat.lt_or_ge i.val k with h | h
    · beta_reduce; congr 1; ext; simp [Nat.mod_eq_of_lt h]
    · have : i = Fin.last k := Fin.ext (by simp; omega)
      subst this
      simp only [Fin.val_last, Nat.mod_self]
      rw [← hy]; rfl
  · intro z _
    funext i
    simp [Nat.mod_eq_of_lt i.isLt]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    unfold pathP
    refine Finset.prod_congr rfl (fun i _ => ?_)
    congr 1
    rcases Nat.lt_or_ge (i.val + 1) k with h | h
    · beta_reduce; congr 1; ext; simp [Nat.mod_eq_of_lt h]
    · have hi : i.succ = Fin.last k := Fin.ext (by simp; omega)
      rw [hi, ← hy]
      have : (i.val + 1) % k = 0 := by rw [show i.val + 1 = k by omega, Nat.mod_self]
      beta_reduce; congr 1; ext; simp [this]

def zb (z : ZMod 2) : Bool := decide (z = 1)
def bz (b : Bool) : ZMod 2 := if b then 1 else 0
lemma zb_bz (b : Bool) : zb (bz b) = b := by cases b <;> decide
lemma bz_zb (z : ZMod 2) : bz (zb z) = z := by revert z; decide
def zbE : ZMod 2 ≃ Bool := ⟨zb, bz, bz_zb, zb_bz⟩

def phi (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (i : ℕ) (p q : Bool) : ℤ :=
  if p && q then 0 else if p then sg (pat a i) else 1

lemma phi_eval (s p q : ZMod 2) :
    (if zb p && zb q then (0:ℤ) else if zb p then sg s else 1) =
      if p * q = 0 then sg (s * p) else 0 := by
  revert s p q; decide

lemma trans_sum {n : ℕ} (hn : 0 < n) (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :
    ∑ y : V n, (if ∀ j : Fin n, y j * y (ix hn (j.val+1)) = 0 then (1:ℤ) else 0) *
      sg (dotProduct (kap n a) y) = runD (phi a) false n false + runD (phi a) true n true := by
  rw [chain n hn]
  let e : V n ≃ (Fin n → Bool) := Equiv.arrowCongr (Equiv.refl _) zbE
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  show _ = ∏ i : Fin n, phi a i (zb (y i)) (zb (y (ix hn (i.val+1))))
  simp only [phi]
  simp only [phi_eval]
  rw [dotProduct, sg_sum]
  by_cases hall : ∀ j : Fin n, y j * y (ix hn (j.val+1)) = 0
  · rw [if_pos hall, one_mul]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [if_pos (hall i)]; rfl
  · rw [if_neg hall, zero_mul]
    push_neg at hall
    obtain ⟨i, hi⟩ := hall
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_neg hi])).symm

/-! transfer matrices -/

def vec (φ : ℕ → Bool → Bool → ℤ) (st : Bool) (j : ℕ) : Fin 2 → ℤ :=
  ![runD φ st j false, runD φ st j true]

def Tm (φ : ℕ → Bool → Bool → ℤ) (i : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![φ i false false, φ i false true; φ i true false, φ i true true]

lemma vec_succ (φ : ℕ → Bool → Bool → ℤ) (st : Bool) (j : ℕ) :
    vec φ st (j+1) = Matrix.vecMul (vec φ st j) (Tm φ j) := by
  ext i; fin_cases i <;> simp [vec, Tm, runD, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

lemma vec_six (φ : ℕ → Bool → Bool → ℤ) (st : Bool) (j : ℕ) :
    vec φ st (j+6) = Matrix.vecMul (vec φ st j)
      (Tm φ j * Tm φ (j+1) * Tm φ (j+2) * Tm φ (j+3) * Tm φ (j+4) * Tm φ (j+5)) := by
  rw [show j + 6 = (j+5)+1 by omega, vec_succ, show j + 5 = (j+4)+1 by omega, vec_succ,
    show j + 4 = (j+3)+1 by omega, vec_succ, show j + 3 = (j+2)+1 by omega, vec_succ,
    show j + 2 = (j+1)+1 by omega, vec_succ, vec_succ]
  simp only [Matrix.vecMul_vecMul]

def Bm (φ : ℕ → Bool → Bool → ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  Tm φ 0 * Tm φ 1 * Tm φ 2 * Tm φ 3 * Tm φ 4 * Tm φ 5

lemma Tm_per (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (i r : ℕ) (h : i % 6 = r % 6) :
    Tm (phi a) i = Tm (phi a) r := by
  simp only [Tm, phi, pat_mod a i r h]

lemma vec_pow (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (st : Bool) :
    ∀ m, vec (phi a) st (6*m) = Matrix.vecMul (vec (phi a) st 0) (Bm (phi a) ^ m)
  | 0 => by simp
  | (m+1) => by
    rw [show 6*(m+1) = 6*m+6 by ring, vec_six, vec_pow a st m, Matrix.vecMul_vecMul, pow_succ]
    rw [Tm_per a (6*m) 0 (by omega), Tm_per a (6*m+1) 1 (by omega), Tm_per a (6*m+2) 2 (by omega),
      Tm_per a (6*m+3) 3 (by omega), Tm_per a (6*m+4) 4 (by omega), Tm_per a (6*m+5) 5 (by omega)]
    rfl

lemma trace_eq (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (t : ℕ) :
    runD (phi a) false (6*t) false + runD (phi a) true (6*t) true = (Bm (phi a) ^ t).trace := by
  have h0 := congrFun (vec_pow a false t) 0
  have h1 := congrFun (vec_pow a true t) 1
  simp [vec, runD, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.trace_fin_two, h0, h1]

def T2 (s : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; s, 0]

lemma Tm_phi (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) (r : ℕ) :
    Tm (phi a) r = T2 (sg (pat a r)) := by
  simp [Tm, phi, T2]

lemma trace6 (s0 s1 s2 s3 s4 s5 : ℤ) :
    (T2 s0 * T2 s1 * T2 s2 * T2 s3 * T2 s4 * T2 s5).trace =
      1 + (s0+s1+s2+s3+s4+s5) + (s0*s2 + s2*s4 + s0*s4 + s1*s3 + s3*s5 + s1*s5 +
        s0*s3 + s1*s4 + s2*s5) + s0*s2*s4 + s1*s3*s5 := by
  simp only [T2, Matrix.mul_fin_two, Matrix.trace_fin_two_of]; ring

lemma det6 (s0 s1 s2 s3 s4 s5 : ℤ) :
    (T2 s0 * T2 s1 * T2 s2 * T2 s3 * T2 s4 * T2 s5).det = s0*s1*s2*s3*s4*s5 := by
  simp only [Matrix.det_mul, T2, Matrix.det_fin_two_of]; ring

lemma sg_sq (a : ZMod 2) : sg a * sg a = 1 := by revert a; decide

lemma Bm_eq (a0 a1 a2 a3 : ZMod 2) : Bm (phi (a0, a1, a2, a3)) =
    T2 (sg a0) * T2 (sg a1) * T2 (sg a2) * T2 (sg a3) * T2 (sg a0 * sg a2) *
      T2 (sg a1 * sg a3) := by
  simp only [Bm, Tm_phi]
  have p0 : pat (a0, a1, a2, a3) 0 = a0 := by simp [pat]
  have p1 : pat (a0, a1, a2, a3) 1 = a1 := by simp [pat]
  have p2 : pat (a0, a1, a2, a3) 2 = a2 := by simp [pat]
  have p3 : pat (a0, a1, a2, a3) 3 = a3 := by simp [pat]
  have p4 : pat (a0, a1, a2, a3) 4 = a0 + a2 := by simp [pat]
  have p5 : pat (a0, a1, a2, a3) 5 = a1 + a3 := by simp [pat]
  rw [p0, p1, p2, p3, p4, p5, sg_add, sg_add]

lemma det_Bm (a : ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) : (Bm (phi a)).det = 1 := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  rw [Bm_eq, det6]
  calc sg a0 * sg a1 * sg a2 * sg a3 * (sg a0 * sg a2) * (sg a1 * sg a3)
      = (sg a0 * sg a0) * (sg a1 * sg a1) * (sg a2 * sg a2) * (sg a3 * sg a3) := by ring
    _ = 1 := by rw [sg_sq, sg_sq, sg_sq, sg_sq]; norm_num

/-! power traces of determinant one -/

def sq (τ : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => τ
  | (m+2) => τ * sq τ (m+1) - sq τ m

lemma ch2 (X : Matrix (Fin 2) (Fin 2) ℤ) :
    X * X = X.trace • X - X.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.one_apply] <;> ring

lemma trace_pow (X : Matrix (Fin 2) (Fin 2) ℤ) (hX : X.det = 1) :
    ∀ m, (X^m).trace = sq X.trace m
  | 0 => by simp [sq]
  | 1 => by simp [sq]
  | (m+2) => by
    have e : X^(m+2) = X.trace • X^(m+1) - X^m := by
      rw [pow_succ, pow_succ, mul_assoc, ch2, hX, mul_sub, Matrix.mul_smul, one_smul, mul_one,
        ← pow_succ]
    rw [e, Matrix.trace_sub, Matrix.trace_smul, trace_pow X hX (m+1), trace_pow X hX m]
    simp [sq]

lemma sq2 : ∀ m, sq 2 m = 2
  | 0 => rfl
  | 1 => rfl
  | (m+2) => by rw [sq, sq2 (m+1), sq2 m]; norm_num

lemma sqm2 : ∀ m, sq (-2) m = 2 * (-1)^m
  | 0 => by simp [sq]
  | 1 => by simp [sq]
  | (m+2) => by rw [sq, sqm2 (m+1), sqm2 m]; ring

lemma trC (x : ℤ) (m : ℕ) : ((!![x,-1;1,0] : Matrix (Fin 2) (Fin 2) ℤ)^m).trace = sq x m := by
  rw [trace_pow _ (by rw [Matrix.det_fin_two_of]; ring), Matrix.trace_fin_two_of, add_zero]

lemma T_kernel {n : ℕ} (hn : 0 < n) (h3 : 2 < n) : ∑ x, Fi hn (mm hn x) =
    ∑ γ ∈ univ.filter (fun γ => mm hn γ = 0), ∑ y, Fi hn y * sg (dotProduct γ y) := by
  have := fourier (mm hn) (mm_add hn) (mm_sym hn h3) (Fi hn) 0
  simp only [zero_dotProduct, sg0, mul_one] at this
  exact this

theorem formula_eq (t : ℕ) (ht : 0 < t) (hn : 0 < 6*t) :
    ∑ x : V (6*t), Fi hn (mm hn x) = sq 18 t + 6 * sq 6 t + 6 + 12 * (-1)^t := by
  have h6 : 6 ∣ 6*t := Dvd.intro t rfl
  have h6' : 6 ≤ 6*t := by omega
  rw [T_kernel hn (by omega), ker_sum hn h6 h6']
  have e : ∀ a, ∑ y, Fi hn y * sg (dotProduct (kap (6*t) a) y) = sq (Bm (phi a)).trace t := by
    intro a
    rw [← trace_pow _ (det_Bm a), ← trace_eq a t, ← trans_sum hn a]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    congr 1
    unfold Fi
    by_cases h : ∀ i : Fin (6*t), y (ix hn (i.val+1)) * y (ix hn (i.val+2)) = 0
    · rw [if_pos h, if_pos ((Fi_shift hn y).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((Fi_shift hn y).mpr h'))]
  simp only [e, Fintype.sum_prod_type, Bm_eq, trace6, univZ2]
  rw [Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide)]
  simp only [Finset.sum_pair (show (0 : ZMod 2) ≠ 1 by decide), sg0, sg1]
  norm_num
  simp only [sq2, sqm2]
  ring

end PEqualNP.Outside.L_meta_32591_aux

namespace PEqualNP.Outside.L_meta_32591_aux

theorem main (t : ℕ) (ht : 0 < t) (hn : 0 < 6*t) (name c : V (6*t)) (k : ℕ) :
    (∃ (A : V (6*t) →ₗ[ZMod 2] V (6*t)) (b : V (6*t)),
      k ≤ Nat.card {w : V (6*t) // out hn name c w = A w + b}) ↔
    (k : ℤ) ≤ ((!![(18:ℤ),-1;1,0] : Matrix (Fin 2) (Fin 2) ℤ)^t).trace +
      6*((!![(6:ℤ),-1;1,0] : Matrix (Fin 2) (Fin 2) ℤ)^t).trace + 6 + 12*(-1:ℤ)^t := by
  have h2 : 2 ∣ 6*t := Dvd.intro (3*t) (by ring)
  have h4 : 4 ≤ 6*t := by omega
  rw [trC 18, trC 6, ← formula_eq t ht hn]
  constructor
  · rintro ⟨A, b, hk⟩
    have hu := upper hn h2 h4 name c b A
    rw [phi_sum] at hu
    have hk' : (k : ℤ) ≤ (Nat.card {w : V (6*t) // out hn name c w = A w + b} : ℤ) := by
      exact_mod_cast hk
    linarith
  · intro hk
    refine ⟨Astar hn, bstar hn name c, ?_⟩
    have hl := lower hn name c
    have : (k:ℤ) ≤
        (Nat.card {w : V (6*t) // out hn name c w = Astar hn w + bstar hn name c} : ℤ) := by
      rw [hl]; exact hk
    exact_mod_cast this

end PEqualNP.Outside.L_meta_32591_aux

theorem PEqualNP.Outside.L_meta_32591 : ∀ (t : ℕ) (ht : 0 < t),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let tr := fun x : ℤ => ((!![x,-1;1,0] : Matrix (Fin 2) (Fin 2) ℤ)^t).trace
  ∀ (name c : W) (k : ℕ),
    (∃ (A : W →ₗ[F] W) (b : W), k ≤ Nat.card {w : W // out name c w = A w + b}) ↔
      (k : ℤ) ≤ tr 18 + 6*tr 6 + 6 + 12*(-1:ℤ)^t := by
  intro t ht F n W ix rot out tr name c k
  have h := PEqualNP.Outside.L_meta_32591_aux.main t ht (Nat.mul_pos (Nat.zero_lt_succ 5) ht)
    name c k
  convert h
  rfl
