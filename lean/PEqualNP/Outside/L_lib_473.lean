import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_473

abbrev V := Fin 3 → ZMod 2

def vs : List V := [![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]

def eps (z : ZMod 2) : ℤ := if z = 0 then 1 else -1
def dotc (u v : V) : ZMod 2 := u 0 * v 0 + u 1 * v 1 + u 2 * v 2
def mv (A : Fin 3 → Fin 3 → ZMod 2) (y : V) : V := fun i => A i 0 * y 0 + A i 1 * y 1 + A i 2 * y 2
def isz (u : V) : Bool := decide (u 0 = 0) && decide (u 1 = 0) && decide (u 2 = 0)
def veq (u v : V) : Bool := decide (u 0 = v 0) && decide (u 1 = v 1) && decide (u 2 = v 2)
def Kc (A : Fin 3 → Fin 3 → ZMod 2) (l l' : V) : ℤ :=
  (vs.map fun y => eps ((if isz y then 1 else 0) + dotc l' y) *
    (if isz (l + mv A y) then 6 else -2)).sum
def rowimg (A : Fin 3 → Fin 3 → ZMod 2) (x : V) : V :=
  fun j => x 0 * A 0 j + x 1 * A 1 j + x 2 * A 2 j
def rc (A : Fin 3 → Fin 3 → ZMod 2) : ℕ :=
  (vs.filter fun u => vs.any fun x => veq (rowimg A x) u).length
def chk (A : Fin 3 → Fin 3 → ZMod 2) (p c : ℕ) : Bool :=
  (vs.all fun l => vs.all fun l' => decide ((Kc A l l').natAbs ≤ p)) &&
  decide ((vs.map fun l => (vs.map fun l' => if (Kc A l l').natAbs = p then 1 else 0).sum).sum = c)
def good (A : Fin 3 → Fin 3 → ZMod 2) : Bool :=
  (decide (rc A = 1) && chk A 36 1) || (decide (rc A = 2) && chk A 28 1) ||
  (decide (rc A = 4) && chk A 20 3) || (decide (rc A = 8) && chk A 20 1)

def pk (r : ℕ) : ℕ := if r = 1 then 36 else if r = 2 then 28 else 20
def ck (r : ℕ) : ℕ := if r = 4 then 3 else 1
def cnt (r : ℕ) : ℕ := if r = 4 then 384 else 128

def dot (u v : V) : ZMod 2 := ∑ i, u i * v i
def dl (p x : V) : ZMod 2 := if x = p then 1 else 0
def cub (x : V) : ZMod 2 := x 0 * x 1 * x 2
def bil (A : Fin 3 → Fin 3 → ZMod 2) (x y : V) : ZMod 2 := ∑ i, ∑ j, x i * A i j * y j
def LQ (g : V → ZMod 2) : Prop := ∃ (b : ZMod 2) (l : V)
    (a : Fin 3 → Fin 3 → ZMod 2), ∀ x, g x = b + dot l x + ∑ i, ∑ j, a i j * x i * x j
def imgc (A : Fin 3 → Fin 3 → ZMod 2) : ℕ :=
  (Finset.univ.image (fun x : V => fun j => ∑ i, x i * A i j)).card
def allowedP (A : Fin 3 → Fin 3 → ZMod 2) (q : V → V → ZMod 2) : Prop :=
  ∃ g h : V → ZMod 2, LQ g ∧ LQ h ∧ ∀ x y, q x y = g x + h y + bil A x y
def scoreP (q : V → V → ZMod 2) : ℕ :=
  (∑ x : V, ∑ y : V, if cub x + cub y = q x y then (1 : ℤ) else -1).natAbs
def Φ (A : Fin 3 → Fin 3 → ZMod 2) (t : V × ZMod 2 × V × V × V) : V → V → ZMod 2 :=
  fun x y => (dl t.1 x + dot t.2.2.2.1 x + t.2.1) + (dl t.2.2.1 y + dot t.2.2.2.2 y) +
    (cub x + cub y + bil A x y)

theorem comp512 : ∀ a b c d e f g h i : ZMod 2,
    good ![![a,b,c],![d,e,f],![g,h,i]] = true := by decide +kernel

theorem comp_all (A : Fin 3 → Fin 3 → ZMod 2) : good A = true := by
  have hA : A = ![![A 0 0, A 0 1, A 0 2], ![A 1 0, A 1 1, A 1 2], ![A 2 0, A 2 1, A 2 2]] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hA]; exact comp512 _ _ _ _ _ _ _ _ _

theorem good_chk (A : Fin 3 → Fin 3 → ZMod 2) (h : good A = true) :
    chk A (pk (rc A)) (ck (rc A)) = true := by
  simp only [good, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩ <;> rw [h1] <;> exact h2

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem mem_vs (x : V) : x ∈ vs := by
  have hx : x = ![x 0, x 1, x 2] := by ext i; fin_cases i <;> rfl
  rw [hx]
  rcases z2 (x 0) with h0 | h0 <;> rcases z2 (x 1) with h1 | h1 <;>
    rcases z2 (x 2) with h2 | h2 <;> rw [h0, h1, h2] <;> decide

theorem nodup_vs : vs.Nodup := by decide

theorem univ_eq : (Finset.univ : Finset V) = vs.toFinset := by
  ext x; simp only [Finset.mem_univ, List.mem_toFinset, true_iff]; exact mem_vs x

theorem sum_vs {M : Type*} [AddCommMonoid M] (f : V → M) : ∑ x, f x = (vs.map f).sum := by
  rw [univ_eq, List.sum_toFinset _ nodup_vs]

theorem chk_bound {A : Fin 3 → Fin 3 → ZMod 2} {p c : ℕ} (h : chk A p c = true) (l l' : V) :
    (Kc A l l').natAbs ≤ p := by
  simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1 l (mem_vs l) l' (mem_vs l')

theorem chk_count {A : Fin 3 → Fin 3 → ZMod 2} {p c : ℕ} (h : chk A p c = true) :
    (∑ l : V, ∑ l' : V, if (Kc A l l').natAbs = p then 1 else 0) = c := by
  simp only [chk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simp only [sum_vs]
  exact h.2

theorem veq_iff (u v : V) : veq u v = true ↔ u = v := by
  simp only [veq, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    ext i; fin_cases i
    exacts [h0, h1, h2]
  · rintro rfl; exact ⟨⟨rfl, rfl⟩, rfl⟩

theorem rowimg_eq (A : Fin 3 → Fin 3 → ZMod 2) (x : V) :
    rowimg A x = fun j => ∑ i, x i * A i j := by
  funext j; simp [rowimg, Fin.sum_univ_three]

theorem rc_eq (A : Fin 3 → Fin 3 → ZMod 2) : imgc A = rc A := by
  have h1 : Finset.univ.image (fun x : V => fun j => ∑ i, x i * A i j) =
      (vs.filter fun u => vs.any fun x => veq (rowimg A x) u).toFinset := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_filter,
      List.any_eq_true, veq_iff]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨mem_vs _, x, mem_vs x, rowimg_eq A x⟩
    · rintro ⟨_, x, _, hx⟩; exact ⟨x, by rw [← hx, rowimg_eq]⟩
  unfold imgc
  rw [h1, List.toFinset_card_of_nodup (nodup_vs.filter _)]
  rfl

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  revert a b; decide

theorem natAbs_eps (c : ZMod 2) : (eps c).natAbs = 1 := by
  unfold eps; split_ifs <;> rfl

theorem ceq : ∀ c e : ZMod 2, (c = e + c ↔ e = 0) := by decide

theorem c2 : ∀ c g r : ZMod 2, c + g = r → g = r + c := by decide

theorem cc : ∀ c r : ZMod 2, c + (r + c) = r := by decide

theorem dl_shift (p x : V) : dl p (x + p) = dl 0 x := by
  by_cases h : x = 0
  · simp [dl, h]
  · simp [dl, h]

theorem dl0 (y : V) : dl 0 y = if isz y = true then 1 else 0 := by
  have := (by decide +kernel : ∀ y ∈ vs, dl 0 y = if isz y = true then 1 else 0)
  exact this y (mem_vs y)

theorem dot_dotc (u v : V) : dot u v = dotc u v := by
  simp [dot, dotc, Fin.sum_univ_three]

theorem inner_aux : ∀ w ∈ vs, (vs.map fun x => eps (dl 0 x + dot w x)).sum =
    if isz w = true then 6 else -2 := by decide +kernel

theorem inner (w : V) : ∑ x, eps (dl 0 x + dot w x) = if isz w = true then 6 else -2 := by
  rw [sum_vs]; exact inner_aux w (mem_vs w)

theorem K0_eq (A : Fin 3 → Fin 3 → ZMod 2) (L L' : V) :
    ∑ x : V, ∑ y : V, eps (dl 0 x + dot L x + (dl 0 y + dot L' y) + bil A x y) = Kc A L L' := by
  rw [Finset.sum_comm, Kc, ← sum_vs]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← dl0, ← dot_dotc, ← inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← eps_add]
  congr 1
  simp only [dot, bil, mv, Fin.sum_univ_three, Pi.add_apply]
  ring

theorem score_Φ (A : Fin 3 → Fin 3 → ZMod 2) (p : V) (b : ZMod 2) (p' l l' : V) :
    scoreP (Φ A (p, b, p', l, l')) = (Kc A (l + mv A p') (l' + rowimg A p)).natAbs := by
  unfold scoreP
  have h1 : ∀ x y, (if cub x + cub y = Φ A (p, b, p', l, l') x y then (1:ℤ) else -1) =
      eps ((dl p x + dot l x + b) + (dl p' y + dot l' y) + bil A x y) := by
    intro x y
    have e : Φ A (p, b, p', l, l') x y =
        ((dl p x + dot l x + b) + (dl p' y + dot l' y) + bil A x y) + (cub x + cub y) := by
      simp only [Φ]; ring
    rw [e]; simp only [eps, ceq]
  simp only [h1]
  have h2 : ∀ F : V → V → ℤ, ∑ x, ∑ y, F x y = ∑ x, ∑ y, F (x + p) (y + p') := fun F =>
    (Fintype.sum_equiv (Equiv.addRight p) (fun x => ∑ y, F (x + p) (y + p'))
      (fun x => ∑ y, F x y) (fun x => Fintype.sum_equiv (Equiv.addRight p')
        (fun y => F (x + p) (y + p')) (fun y => F (x + p) y) (fun y => rfl))).symm
  rw [h2]
  have h3 : ∀ x y : V, eps ((dl p (x + p) + dot l (x + p) + b) + (dl p' (y + p') + dot l' (y + p'))
      + bil A (x + p) (y + p')) = eps (dl 0 x + dot (l + mv A p') x +
        (dl 0 y + dot (l' + rowimg A p) y) + bil A x y) *
        eps (b + (dot l p + dot l' p' + bil A p p')) := by
    intro x y
    rw [← eps_add, dl_shift, dl_shift]
    congr 1
    simp only [dot, bil, mv, rowimg, Fin.sum_univ_three, Pi.add_apply]
    ring
  simp only [h3, ← Finset.sum_mul, K0_eq]
  rw [Int.natAbs_mul, natAbs_eps, mul_one]

theorem v0 {α : Type*} (a b c : α) : ![a, b, c] 0 = a := rfl
theorem v1 {α : Type*} (a b c : α) : ![a, b, c] 1 = b := rfl
theorem v2 {α : Type*} (a b c : α) : ![a, b, c] 2 = c := rfl

theorem dl_prod (p x : V) : dl p x = (1 + x 0 + p 0) * (1 + x 1 + p 1) * (1 + x 2 + p 2) := by
  have := (by decide +kernel : ∀ p ∈ vs, ∀ x ∈ vs,
    dl p x = (1 + x 0 + p 0) * (1 + x 1 + p 1) * (1 + x 2 + p 2))
  exact this p (mem_vs p) x (mem_vs x)

theorem core1 : ∀ a00 a01 a02 a10 a11 a12 a20 a21 a22 x0 x1 x2 : ZMod 2,
    x0 * x1 * x2 + (a00 * x0 * x0 + a01 * x0 * x1 + a02 * x0 * x2 + a10 * x1 * x0 + a11 * x1 * x1
      + a12 * x1 * x2 + a20 * x2 * x0 + a21 * x2 * x1 + a22 * x2 * x2) =
    (1 + x0 + (1 + (a12 + a21))) * (1 + x1 + (1 + (a02 + a20))) * (1 + x2 + (1 + (a01 + a10)))
      + ((a00 + (a02 + a20) * (a01 + a10)) * x0 + (a11 + (a12 + a21) * (a01 + a10)) * x1
      + (a22 + (a12 + a21) * (a02 + a20)) * x2) + (a12 + a21) * (a02 + a20) * (a01 + a10) := by
  decide +kernel

theorem core2 : ∀ p0 p1 p2 x0 x1 x2 : ZMod 2,
    (1 + x0 + p0) * (1 + x1 + p1) * (1 + x2 + p2) + x0 * x1 * x2 =
    (1 + p0) * (1 + p1) * (1 + p2) + ((1 + p1) * (1 + p2) * x0 + (1 + p0) * (1 + p2) * x1
      + (1 + p0) * (1 + p1) * x2) + ((1 + p2) * x0 * x1 + (1 + p1) * x0 * x2
      + (1 + p0) * x1 * x2) := by
  decide +kernel

theorem lq_fwd (g : V → ZMod 2) (h : LQ g) : ∃ (p l : V) (b : ZMod 2),
    ∀ x, cub x + g x = dl p x + dot l x + b := by
  obtain ⟨b, l, a, hg⟩ := h
  refine ⟨![1 + (a 1 2 + a 2 1), 1 + (a 0 2 + a 2 0), 1 + (a 0 1 + a 1 0)],
    l + ![a 0 0 + (a 0 2 + a 2 0) * (a 0 1 + a 1 0), a 1 1 + (a 1 2 + a 2 1) * (a 0 1 + a 1 0),
      a 2 2 + (a 1 2 + a 2 1) * (a 0 2 + a 2 0)],
    b + (a 1 2 + a 2 1) * (a 0 2 + a 2 0) * (a 0 1 + a 1 0), fun x => ?_⟩
  rw [hg x, dl_prod]
  simp only [cub, dot, Fin.sum_univ_three, Pi.add_apply, v0, v1, v2]
  linear_combination core1 (a 0 0) (a 0 1) (a 0 2) (a 1 0) (a 1 1) (a 1 2) (a 2 0) (a 2 1)
    (a 2 2) (x 0) (x 1) (x 2)

theorem lq_bwd (g : V → ZMod 2) (p l : V) (b : ZMod 2)
    (h : ∀ x, g x = dl p x + dot l x + b + cub x) : LQ g := by
  refine ⟨b + (1 + p 0) * (1 + p 1) * (1 + p 2),
    l + ![(1 + p 1) * (1 + p 2), (1 + p 0) * (1 + p 2), (1 + p 0) * (1 + p 1)],
    ![![0, 1 + p 2, 1 + p 1], ![0, 0, 1 + p 0], ![0, 0, 0]], fun x => ?_⟩
  rw [h x, dl_prod]
  simp only [cub, dot, Fin.sum_univ_three, Pi.add_apply, v0, v1, v2]
  linear_combination core2 (p 0) (p 1) (p 2) (x 0) (x 1) (x 2)

theorem allowed_iff (A : Fin 3 → Fin 3 → ZMod 2) (q : V → V → ZMod 2) :
    allowedP A q ↔ ∃ t, Φ A t = q := by
  constructor
  · rintro ⟨g, h, hg, hh, hq⟩
    obtain ⟨p, l, b, hg'⟩ := lq_fwd g hg
    obtain ⟨p', l', b', hh'⟩ := lq_fwd h hh
    refine ⟨(p, b + b', p', l, l'), ?_⟩
    funext x y
    rw [hq x y, c2 _ _ _ (hg' x), c2 _ _ _ (hh' y)]
    simp only [Φ]; ring
  · rintro ⟨⟨p, b, p', l, l'⟩, rfl⟩
    refine ⟨fun x => dl p x + dot l x + b + cub x, fun y => dl p' y + dot l' y + 0 + cub y,
      lq_bwd _ p l b (fun x => rfl), lq_bwd _ p' l' 0 (fun y => rfl), fun x y => ?_⟩
    simp only [Φ]; ring

theorem U2_aux : ∀ p ∈ vs, ∀ l ∈ vs, ∀ P ∈ vs, ∀ L ∈ vs, ∀ e f : ZMod 2,
    (vs.all fun x => decide (dl p x + dot l x + e = dl P x + dot L x + f)) = true →
      p = P ∧ l = L ∧ e = f := by decide +kernel

theorem U2 (p l P L : V) (e f : ZMod 2) (h : ∀ x, dl p x + dot l x + e = dl P x + dot L x + f) :
    p = P ∧ l = L ∧ e = f := by
  refine U2_aux p (mem_vs p) l (mem_vs l) P (mem_vs P) L (mem_vs L) e f ?_
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact fun x _ => h x

theorem Φ_inj (A : Fin 3 → Fin 3 → ZMod 2) : Function.Injective (Φ A) := by
  rintro ⟨p, b, p', l, l'⟩ ⟨P, B, P', L, L'⟩ h
  have k : ∀ x y, (dl p x + dot l x + b) + (dl p' y + dot l' y) =
      (dl P x + dot L x + B) + (dl P' y + dot L' y) := fun x y => by
    have := congrFun (congrFun h x) y
    simp only [Φ] at this
    exact add_right_cancel this
  obtain ⟨rfl, rfl, -⟩ := U2 p l P L (b + (dl p' 0 + dot l' 0)) (B + (dl P' 0 + dot L' 0))
    (fun x => by linear_combination k x 0)
  obtain ⟨rfl, rfl, h2⟩ := U2 p' l' P' L' (dl p 0 + dot l 0 + b) (dl p 0 + dot l 0 + B)
    (fun y => by linear_combination k 0 y)
  rw [add_left_cancel h2]

theorem main (A : Fin 3 → Fin 3 → ZMod 2) :
    (∀ q, allowedP A q → scoreP q ≤ pk (imgc A)) ∧
      Set.ncard {q | allowedP A q ∧ scoreP q = pk (imgc A)} = cnt (imgc A) := by
  rw [rc_eq]
  have hc := good_chk A (comp_all A)
  refine ⟨fun q hq => ?_, ?_⟩
  · obtain ⟨⟨p, b, p', l, l'⟩, rfl⟩ := (allowed_iff A q).1 hq
    rw [score_Φ]; exact chk_bound hc _ _
  · have hS : {q | allowedP A q ∧ scoreP q = pk (rc A)} = Φ A '' ↑(Finset.univ.filter
        fun t : V × ZMod 2 × V × V × V =>
          (Kc A (t.2.2.2.1 + mv A t.2.2.1) (t.2.2.2.2 + rowimg A t.1)).natAbs = pk (rc A)) := by
      ext q; constructor
      · rintro ⟨hq, hs⟩
        obtain ⟨⟨p, b, p', l, l'⟩, rfl⟩ := (allowed_iff A q).1 hq
        refine ⟨(p, b, p', l, l'), Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩),
          rfl⟩
        rw [score_Φ] at hs; exact hs
      · rintro ⟨⟨p, b, p', l, l'⟩, ht, rfl⟩
        have ht' := (Finset.mem_filter.1 (Finset.mem_coe.1 ht)).2
        refine ⟨(allowed_iff A _).2 ⟨_, rfl⟩, ?_⟩
        rw [score_Φ]; exact ht'
    rw [hS, Set.ncard_image_of_injective _ (Φ_inj A), Set.ncard_coe_finset, Finset.card_filter]
    simp only [Fintype.sum_prod_type]
    have key : ∀ p p' : V, (∑ l : V, ∑ l' : V,
        if (Kc A (l + mv A p') (l' + rowimg A p)).natAbs = pk (rc A) then 1 else 0) =
          ck (rc A) := by
      intro p p'
      rw [← chk_count hc]
      exact Fintype.sum_equiv (Equiv.addRight (mv A p')) _ _
        (fun l => Fintype.sum_equiv (Equiv.addRight (rowimg A p)) _ _ (fun l' => rfl))
    simp only [key, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hV : Fintype.card V = 8 := by simp
    rw [hV, ZMod.card]
    unfold ck cnt
    split_ifs <;> norm_num

end PEqualNP.Outside.L_lib_473

open PEqualNP.Outside.L_lib_473 in
theorem PEqualNP.Outside.L_lib_473 :
    let V := Fin 3 → ZMod 2
    let dot := fun (u v : V) => ∑ i, u i * v i
    let isLocalQuad := fun (g : V → ZMod 2) => ∃ (b : ZMod 2) (l : V)
        (a : Fin 3 → Fin 3 → ZMod 2), ∀ x, g x = b + dot l x +
          ∑ i, ∑ j, a i j * x i * x j
    let cubic := fun (x : V) => x 0 * x 1 * x 2
    ∀ A : Fin 3 → Fin 3 → ZMod 2,
      let imageSize := (Finset.univ.image (fun x : V => fun j =>
        ∑ i, x i * A i j)).card
      let allowed := fun (q : V → V → ZMod 2) =>
        ∃ g h : V → ZMod 2, isLocalQuad g ∧ isLocalQuad h ∧
          ∀ x y, q x y = g x + h y + ∑ i, ∑ j, x i * A i j * y j
      let score := fun (q : V → V → ZMod 2) =>
        (∑ x : V, ∑ y : V,
          if cubic x + cubic y = q x y then (1 : ℤ) else -1).natAbs
      let peak := if imageSize = 1 then 36 else if imageSize = 2 then 28 else 20
      let count := if imageSize = 4 then 384 else 128
      (∀ q, allowed q → score q ≤ peak) ∧
        Set.ncard {q : V → V → ZMod 2 | allowed q ∧ score q = peak} = count
 := by
  intro V dot isLocalQuad cubic A
  exact PEqualNP.Outside.L_lib_473.main A
