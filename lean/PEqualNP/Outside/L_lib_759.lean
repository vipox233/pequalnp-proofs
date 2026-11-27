import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_759_aux

abbrev V (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}

theorem zc (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

theorem two (x : V n) : x + x = 0 := by
  funext i; simp only [Pi.add_apply, Pi.zero_apply]; generalize x i = a; revert a; decide

theorem solve {a b c : V n} (h : a + b = c) : b = a + c := by
  rw [← h, ← add_assoc, two, zero_add]

theorem solve' {a b c : V n} (h : a + b = c) : a = c + b := by
  rw [← h, add_assoc, two, add_zero]

theorem eq_of_add {a b : V n} (h : a + b = 0) : a = b := by
  have := solve' h; rw [zero_add] at this; exact this

def onP (p q y : V n) : Prop := y = p ∨ y = q ∨ y = p + q
def Valid (p q : V n) : Prop := p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q
def Disj (p q r s : V n) : Prop := ∀ y, onP p q y → ¬ onP r s y

theorem disj_symm {p q r s : V n} (h : Disj p q r s) : Disj r s p q := fun y h1 h2 => h y h2 h1

theorem sum_ne {p q : V n} (hv : Valid p q) : p + q ≠ 0 := fun h => hv.2.2 (eq_of_add h)

theorem comb_zero {p q : V n} (hv : Valid p q) {c0 c1 : ZMod 2} (h : c0 • p + c1 • q = 0) :
    c0 = 0 ∧ c1 = 0 := by
  rcases zc c0 with rfl | rfl <;> rcases zc c1 with rfl | rfl <;> simp at h ⊢ <;>
    first | exact hv.1 h | exact hv.2.1 h | exact hv.2.2 (eq_of_add h)

theorem comb_pt {p q : V n} (c0 c1 : ZMod 2) (h : c0 • p + c1 • q ≠ 0) :
    onP p q (c0 • p + c1 • q) := by
  unfold onP
  rcases zc c0 with rfl | rfl <;> rcases zc c1 with rfl | rfl <;> simp at h ⊢

theorem indep {p q r s : V n} (hP : Valid p q) (hQ : Valid r s) (hd : Disj p q r s)
    (c : Fin 4 → ZMod 2) (h : c 0 • p + c 1 • q + (c 2 • r + c 3 • s) = 0) : c = 0 := by
  have e := eq_of_add h
  by_cases hu : c 0 • p + c 1 • q = 0
  · have ht : c 2 • r + c 3 • s = 0 := by rw [← e, hu]
    obtain ⟨a0, a1⟩ := comb_zero hP hu
    obtain ⟨a2, a3⟩ := comb_zero hQ ht
    funext i; fin_cases i <;> simp [a0, a1, a2, a3]
  · exfalso
    have ht : c 2 • r + c 3 • s ≠ 0 := by rw [← e]; exact hu
    exact hd _ (comb_pt _ _ hu) (by rw [e]; exact comb_pt _ _ ht)

theorem mk_mask {p q r s : V n}
    (hi : ∀ c : Fin 4 → ZMod 2, c 0 • p + c 1 • q + (c 2 • r + c 3 • s) = 0 → c = 0)
    (m0 m1 m2 m3 : ZMod 2) : ∃ mask : V n →ₗ[ZMod 2] ZMod 2,
      mask p = m0 ∧ mask q = m1 ∧ mask r = m2 ∧ mask s = m3 := by
  let φ : (Fin 4 → ZMod 2) →ₗ[ZMod 2] V n :=
    (LinearMap.proj 0 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight p +
    (LinearMap.proj 1 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight q +
    ((LinearMap.proj 2 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight r +
    (LinearMap.proj 3 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2).smulRight s)
  have hφ : ∀ c, φ c = c 0 • p + c 1 • q + (c 2 • r + c 3 • s) := fun c => rfl
  have hk : LinearMap.ker φ = ⊥ :=
    LinearMap.ker_eq_bot'.2 (fun c hc => hi c (by rw [← hφ]; exact hc))
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ hk
  have key : ∀ c, ψ (φ c) = c := fun c => by
    rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  let ev : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    m0 • (LinearMap.proj 0 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    m1 • (LinearMap.proj 1 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    m2 • (LinearMap.proj 2 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2) +
    m3 • (LinearMap.proj 3 : (Fin 4 → ZMod 2) →ₗ[ZMod 2] ZMod 2)
  have hev : ∀ c, ev c = m0 * c 0 + m1 * c 1 + m2 * c 2 + m3 * c 3 := fun c => rfl
  refine ⟨ev ∘ₗ ψ, ?_, ?_, ?_, ?_⟩
  · have : p = φ (Pi.single 0 1) := by rw [hφ]; simp
    rw [LinearMap.comp_apply, this, key, hev]; simp
  · have : q = φ (Pi.single 1 1) := by rw [hφ]; simp
    rw [LinearMap.comp_apply, this, key, hev]; simp
  · have : r = φ (Pi.single 2 1) := by rw [hφ]; simp
    rw [LinearMap.comp_apply, this, key, hev]; simp
  · have : s = φ (Pi.single 3 1) := by rw [hφ]; simp
    rw [LinearMap.comp_apply, this, key, hev]; simp

theorem fr2 {p q : V n} (hv : Valid p q) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({p, q} : Set (V n))) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![p, q] :=
    LinearIndependent.pair_iff.2 (fun s t h => comb_zero hv h)
  have := finrank_span_eq_card hli
  rw [Fintype.card_fin] at this
  have hr : Set.range ![p, q] = ({p, q} : Set (V n)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rwa [hr] at this

theorem build {p q r s : V n} (hP : Valid p q) (hQ : Valid r s) (hd : Disj p q r s)
    (A : V n → Finset (ZMod 2))
    (hodd : ∃ m0 m1 : ZMod 2, 1 + m0 ∈ A p ∧ 1 + m1 ∈ A q ∧ 1 + (m0 + m1) ∈ A (p + q))
    (hev : ∃ m2 m3 : ZMod 2, m2 ∈ A r ∧ m3 ∈ A s ∧ m2 + m3 ∈ A (r + s)) :
    ∃ (U T : Submodule (ZMod 2) (V n)) (mask : V n →ₗ[ZMod 2] ZMod 2),
      Disjoint U T ∧ Module.finrank (ZMod 2) U = 2 ∧ Module.finrank (ZMod 2) T = 2 ∧
      (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ A x) ∧ (∀ x ∈ T, x ≠ 0 → mask x ∈ A x) := by
  obtain ⟨m0, m1, h0, h1, h01⟩ := hodd
  obtain ⟨m2, m3, h2, h3, h23⟩ := hev
  have hi := indep hP hQ hd
  obtain ⟨mask, e0, e1, e2, e3⟩ := mk_mask hi m0 m1 m2 m3
  refine ⟨Submodule.span (ZMod 2) {p, q}, Submodule.span (ZMod 2) {r, s}, mask, ?_,
    fr2 hP, fr2 hQ, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hx'
    have := hi ![a, b, c, d] (by
      show a • p + b • q + (c • r + d • s) = 0
      rw [hcd, two])
    have ha : a = 0 := congrFun this 0
    have hb : b = 0 := congrFun this 1
    rw [ha, hb]; simp
  · intro x hx hx0
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rcases zc a with rfl | rfl <;> rcases zc b with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero, map_add, e0, e1] at hx0 ⊢ <;>
      first | exact absurd rfl hx0 | exact h0 | exact h1 | exact h01
  · intro x hx hx0
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rcases zc a with rfl | rfl <;> rcases zc b with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero, map_add, e2, e3] at hx0 ⊢ <;>
      first | exact absurd rfl hx0 | exact h2 | exact h3 | exact h23

theorem notin (hn : 4 ≤ n) (a b d : V n) :
    ∃ v, v ∉ Submodule.span (ZMod 2) ({a, b, d} : Set (V n)) := by
  by_contra h
  push_neg at h
  have htop : Submodule.span (ZMod 2) ({a, b, d} : Set (V n)) = ⊤ :=
    eq_top_iff.2 (fun v _ => h v)
  have h1 := finrank_span_finset_le_card (R := ZMod 2) ({a, b, d} : Finset (V n))
  have hc : ((({a, b, d} : Finset (V n))) : Set (V n)) = {a, b, d} := by ext; simp
  simp only [Set.finrank] at h1
  rw [hc] at h1
  rw [htop, finrank_top, Module.finrank_fin_fun] at h1
  have := Finset.card_le_three (a := a) (b := b) (c := d)
  omega

theorem m1 (a b d : V n) : a ∈ Submodule.span (ZMod 2) ({a, b, d} : Set (V n)) :=
  Submodule.subset_span (by simp)
theorem m2 (a b d : V n) : b ∈ Submodule.span (ZMod 2) ({a, b, d} : Set (V n)) :=
  Submodule.subset_span (by simp)
theorem m3 (a b d : V n) : d ∈ Submodule.span (ZMod 2) ({a, b, d} : Set (V n)) :=
  Submodule.subset_span (by simp)

theorem onP_mem {p q y : V n} (S : Submodule (ZMod 2) (V n)) (hp : p ∈ S) (hq : q ∈ S)
    (h : onP p q y) : y ∈ S := by
  rcases h with rfl | rfl | rfl
  · exact hp
  · exact hq
  · exact S.add_mem hp hq

theorem chain (hn : 4 ≤ n) {x : V n} (hx : x ≠ 0) :
    ∃ q r s, Valid x q ∧ Valid r s ∧ Disj x q r s := by
  obtain ⟨q, hq⟩ := notin hn x x x
  obtain ⟨r, hr⟩ := notin hn x q q
  obtain ⟨s, hs⟩ := notin hn x q r
  refine ⟨q, r, s, ⟨hx, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro rfl; exact hq (Submodule.zero_mem _)
  · rintro rfl; exact hq (m1 _ _ _)
  · rintro rfl; exact hr (Submodule.zero_mem _)
  · rintro rfl; exact hs (Submodule.zero_mem _)
  · rintro rfl; exact hs (m3 _ _ _)
  · intro y hy hy'
    have y1 : y ∈ Submodule.span (ZMod 2) ({x, q, q} : Set (V n)) :=
      onP_mem _ (m1 _ _ _) (m2 _ _ _) hy
    have y2 : y ∈ Submodule.span (ZMod 2) ({x, q, r} : Set (V n)) :=
      onP_mem _ (m1 _ _ _) (m2 _ _ _) hy
    rcases hy' with rfl | rfl | h
    · exact hr y1
    · exact hs y2
    · have : s = r + y := solve h.symm
      exact hs (this ▸ Submodule.add_mem _ (m3 _ _ _) y2)

theorem g2 (hn : 4 ≤ n) {c q s : V n} (h1 : Valid c q) (h2 : Valid c s) :
    ∃ v w, Valid v w ∧ Disj v w c q ∧ Disj v w c s := by
  by_cases hs : s ∈ Submodule.span (ZMod 2) ({c, q, q} : Set (V n))
  · obtain ⟨v, hv⟩ := notin hn c q q
    obtain ⟨w, hw⟩ := notin hn c q v
    have hmono : Submodule.span (ZMod 2) ({c, q, q} : Set (V n)) ≤
        Submodule.span (ZMod 2) ({c, q, v} : Set (V n)) := by
      apply Submodule.span_mono
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      tauto
    have key : ∀ y, (onP c q y ∨ onP c s y) → ¬ onP v w y := by
      intro y hy hy'
      have yS : y ∈ Submodule.span (ZMod 2) ({c, q, q} : Set (V n)) := by
        rcases hy with hy | hy
        · exact onP_mem _ (m1 _ _ _) (m2 _ _ _) hy
        · exact onP_mem _ (m1 _ _ _) hs hy
      rcases hy' with rfl | rfl | h
      · exact hv yS
      · exact hw (hmono yS)
      · have : w = v + y := solve h.symm
        exact hw (this ▸ Submodule.add_mem _ (m3 _ _ _) (hmono yS))
    refine ⟨v, w, ⟨?_, ?_, ?_⟩, fun y h h' => key y (Or.inl h') h,
      fun y h h' => key y (Or.inr h') h⟩
    · rintro rfl; exact hv (Submodule.zero_mem _)
    · rintro rfl; exact hw (Submodule.zero_mem _)
    · rintro rfl; exact hw (m3 _ _ _)
  · obtain ⟨v, hv⟩ := notin hn c q s
    have sq : ∀ t, s = q + t → t = c → False := by
      intro t h ht; subst ht
      exact hs (h ▸ Submodule.add_mem _ (m2 _ _ _) (m1 _ _ _))
    have inS : ∀ y, (onP c q y ∨ onP c s y) → y ∈ Submodule.span (ZMod 2) ({c, q, s} : Set (V n)) := by
      intro y hy
      rcases hy with hy | hy
      · exact onP_mem _ (m1 _ _ _) (m2 _ _ _) hy
      · exact onP_mem _ (m1 _ _ _) (m3 _ _ _) hy
    have hqs : q + s ∈ Submodule.span (ZMod 2) ({c, q, s} : Set (V n)) :=
      Submodule.add_mem _ (m2 _ _ _) (m3 _ _ _)
    have key : ∀ y, (onP c q y ∨ onP c s y) → ¬ onP v (q + s) y := by
      intro y hy hy'
      rcases hy' with rfl | rfl | h
      · exact hv (inS _ hy)
      · rcases hy with (h | h | h) | (h | h | h)
        · exact sq c (solve h) rfl
        · have : s = q + q := solve h
          rw [two] at this; exact h2.2.1 this
        · have : s = q + (c + q) := solve h
          rw [add_comm c q, ← add_assoc, two, zero_add] at this
          exact h2.2.2 this.symm
        · exact sq c (solve h) rfl
        · have : q = s + s := solve' h
          rw [two] at this; exact h1.2.1 this
        · have : q = c + s + s := solve' h
          rw [add_assoc, two, add_zero] at this; exact h1.2.2 this.symm
      · have : v = y + (q + s) := solve' h.symm
        exact hv (this ▸ Submodule.add_mem _ (inS _ hy) hqs)
    refine ⟨v, q + s, ⟨?_, ?_, ?_⟩, fun y h h' => key y (Or.inl h') h,
      fun y h h' => key y (Or.inr h') h⟩
    · rintro rfl; exact hv (Submodule.zero_mem _)
    · intro h; have := eq_of_add h; subst this
      exact hs (m2 _ _ _)
    · rintro rfl; exact hv hqs

theorem regen (a : V n → ZMod 2) {p q z : V n} (hv : Valid p q) (hz : onP p q z) :
    ∃ q', Valid z q' ∧ a z + a q' + a (z + q') = a p + a q + a (p + q) := by
  rcases hz with rfl | rfl | rfl
  · exact ⟨q, hv, rfl⟩
  · refine ⟨p, ⟨hv.2.1, hv.1, fun h => hv.2.2 h.symm⟩, ?_⟩
    rw [add_comm z p]; ring
  · refine ⟨p, ⟨sum_ne hv, hv.1, ?_⟩, ?_⟩
    · intro h
      have : q = p + p := solve h
      rw [two] at this; exact hv.2.1 this
    · have : p + q + p = q := by rw [add_comm p q, add_assoc, two, add_zero]
      rw [this]; ring

theorem two_pts (S : Submodule (ZMod 2) (V n)) (h : Module.finrank (ZMod 2) S = 2) :
    ∃ x y, x ∈ S ∧ y ∈ S ∧ x ≠ 0 ∧ y ≠ 0 ∧ x + y ≠ 0 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) S h
  refine ⟨b 0, b 1, (b 0).2, (b 1).2, ?_, ?_, ?_⟩
  · intro h0; exact b.ne_zero 0 (Subtype.ext h0)
  · intro h0; exact b.ne_zero 1 (Subtype.ext h0)
  · intro h0
    have := b.injective (Subtype.ext (eq_of_add h0))
    exact absurd this (by decide)

theorem zA : ∀ a b c d o : ZMod 2, 1 + a = c + o → 1 + b = d + o →
    1 + (a + b) = c + d + o → o = 1 := by decide

theorem zB : ∀ e f g h o : ZMod 2, e = g + o → f = h + o → e + f = g + h + o → o = 0 := by decide

theorem main (hn : 4 ≤ n) (A : V n → Finset (ZMod 2)) (hne : ∀ x : V n, x ≠ 0 → (A x).Nonempty) :
    (∃ (U T : Submodule (ZMod 2) (V n)) (mask : V n →ₗ[ZMod 2] ZMod 2),
      Disjoint U T ∧ Module.finrank (ZMod 2) U = 2 ∧ Module.finrank (ZMod 2) T = 2 ∧
      (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ A x) ∧ (∀ x ∈ T, x ≠ 0 → mask x ∈ A x)) ↔
    ¬ (∃ (linear : V n →ₗ[ZMod 2] ZMod 2) (offset : ZMod 2), ∀ x : V n, x ≠ 0 →
        ∀ b ∈ A x, b = linear x + offset) := by
  constructor
  · rintro ⟨U, T, mask, -, hU, hT, hmU, hmT⟩ ⟨lin, off, haff⟩
    obtain ⟨x, y, hx, hy, hx0, hy0, hxy⟩ := two_pts U hU
    obtain ⟨x', y', hx', hy', hx0', hy0', hxy'⟩ := two_pts T hT
    have e1 := haff x hx0 _ (hmU x hx hx0)
    have e2 := haff y hy0 _ (hmU y hy hy0)
    have e3 := haff (x + y) hxy _ (hmU (x + y) (U.add_mem hx hy) hxy)
    have f1 := haff x' hx0' _ (hmT x' hx' hx0')
    have f2 := haff y' hy0' _ (hmT y' hy' hy0')
    have f3 := haff (x' + y') hxy' _ (hmT (x' + y') (T.add_mem hx' hy') hxy')
    rw [map_add, map_add] at e3 f3
    have := (zA _ _ _ _ _ e1 e2 e3).symm.trans (zB _ _ _ _ _ f1 f2 f3)
    exact absurd this (by decide)
  · intro hna
    by_contra H
    apply hna
    have H' : ∀ p q r s : V n, Valid p q → Valid r s → Disj p q r s →
        (∃ m0 m1 : ZMod 2, 1 + m0 ∈ A p ∧ 1 + m1 ∈ A q ∧ 1 + (m0 + m1) ∈ A (p + q)) →
        (∃ m2 m3 : ZMod 2, m2 ∈ A r ∧ m3 ∈ A s ∧ m2 + m3 ∈ A (r + s)) → False :=
      fun p q r s hP hQ hd ho he => H (build hP hQ hd A ho he)
    have z1 : ∀ a : ZMod 2, 1 + (1 + a) = a := by decide
    by_cases hA : ∃ x : V n, x ≠ 0 ∧ (0 : ZMod 2) ∈ A x ∧ (1 : ZMod 2) ∈ A x
    · exfalso
      obtain ⟨x, hx0, hx0A, hx1A⟩ := hA
      have hall : ∀ b : ZMod 2, b ∈ A x := by
        intro b; rcases zc b with rfl | rfl
        · exact hx0A
        · exact hx1A
      obtain ⟨q, r, s, hP, hQ, hd⟩ := chain hn hx0
      obtain ⟨ar, har⟩ := hne r hQ.1
      obtain ⟨as, has⟩ := hne s hQ.2.1
      obtain ⟨ars, hars⟩ := hne (r + s) (sum_ne hQ)
      obtain ⟨aq, haq⟩ := hne q hP.2.1
      obtain ⟨axq, haxq⟩ := hne (x + q) (sum_ne hP)
      have z2 : ∀ a b : ZMod 2, 1 + ((a + b) + (1 + b)) = a := by decide
      have z3 : ∀ a b c : ZMod 2, a + b + c = 0 → a + b = c := by decide
      have z4 : ∀ a b c : ZMod 2, a + b + c = 1 → 1 + ((1 + a) + (1 + b)) = c := by decide
      have z5 : ∀ a b : ZMod 2, (a + b) + b = a := by decide
      rcases zc (ar + as + ars) with h | h
      · exact H' x q r s hP hQ hd ⟨axq + aq, 1 + aq, hall _, by rw [z1]; exact haq,
          by rw [z2]; exact haxq⟩ ⟨ar, as, har, has, by rw [z3 _ _ _ h]; exact hars⟩
      · exact H' r s x q hQ hP (disj_symm hd) ⟨1 + ar, 1 + as, by rw [z1]; exact har,
          by rw [z1]; exact has, by rw [z4 _ _ _ h]; exact hars⟩
          ⟨axq + aq, aq, hall _, haq, by rw [z5]; exact haxq⟩
    · push_neg at hA
      let a : V n → ZMod 2 := fun x => if (0 : ZMod 2) ∈ A x then 0 else 1
      have ha : ∀ x : V n, x ≠ 0 → ∀ b ∈ A x, b = a x := by
        intro x hx b hb
        simp only [a]
        split_ifs with h0
        · rcases zc b with rfl | rfl
          · rfl
          · exact absurd hb (hA x hx h0)
        · rcases zc b with rfl | rfl
          · exact absurd hb h0
          · rfl
      have ha' : ∀ x : V n, x ≠ 0 → a x ∈ A x := by
        intro x hx
        obtain ⟨b, hb⟩ := hne x hx
        rwa [← ha x hx b hb]
      have z3 : ∀ a b c : ZMod 2, a + b + c = 0 → a + b = c := by decide
      have z4 : ∀ a b c : ZMod 2, a + b + c = 1 → 1 + ((1 + a) + (1 + b)) = c := by decide
      have Hs : ∀ p q r s : V n, Valid p q → Valid r s → Disj p q r s →
          a p + a q + a (p + q) = a r + a s + a (r + s) := by
        intro p q r s hP hQ hd
        rcases zc (a p + a q + a (p + q)) with h1 | h1 <;>
          rcases zc (a r + a s + a (r + s)) with h2 | h2
        · rw [h1, h2]
        · exact (H' r s p q hQ hP (disj_symm hd)
            ⟨1 + a r, 1 + a s, by rw [z1]; exact ha' r hQ.1, by rw [z1]; exact ha' s hQ.2.1,
              by rw [z4 _ _ _ h2]; exact ha' _ (sum_ne hQ)⟩
            ⟨a p, a q, ha' p hP.1, ha' q hP.2.1, by rw [z3 _ _ _ h1]; exact ha' _ (sum_ne hP)⟩).elim
        · exact (H' p q r s hP hQ hd
            ⟨1 + a p, 1 + a q, by rw [z1]; exact ha' p hP.1, by rw [z1]; exact ha' q hP.2.1,
              by rw [z4 _ _ _ h1]; exact ha' _ (sum_ne hP)⟩
            ⟨a r, a s, ha' r hQ.1, ha' s hQ.2.1, by rw [z3 _ _ _ h2]; exact ha' _ (sum_ne hQ)⟩).elim
        · rw [h1, h2]
      let x0 : V n := Pi.single ⟨0, by omega⟩ 1
      have hx0 : x0 ≠ 0 := by
        intro h
        have := congrFun h ⟨0, by omega⟩
        simp [x0] at this
      obtain ⟨q0, -, -, hP0, -, -⟩ := chain hn hx0
      have hall : ∀ p q : V n, Valid p q →
          a p + a q + a (p + q) = a x0 + a q0 + a (x0 + q0) := by
        intro p q hv
        by_cases hd : Disj p q x0 q0
        · exact Hs _ _ _ _ hv hP0 hd
        · unfold Disj at hd
          push_neg at hd
          obtain ⟨z, hz1, hz2⟩ := hd
          obtain ⟨q1, hv1, hs1⟩ := regen a hv hz1
          obtain ⟨q2, hv2, hs2⟩ := regen a hP0 hz2
          obtain ⟨v, w, hvw, hd1, hd2⟩ := g2 hn hv1 hv2
          rw [← hs1, ← hs2, Hs _ _ _ _ hv1 hvw (disj_symm hd1), Hs _ _ _ _ hvw hv2 hd2]
      let c := a x0 + a q0 + a (x0 + q0)
      let b : V n → ZMod 2 := fun x => if x = 0 then 0 else a x + c
      have z6 : ∀ t : ZMod 2, t + t = 0 := by decide
      have z7 : ∀ p q r c : ZMod 2, p + q + r = c → r + c = p + c + (q + c) := by decide
      have hb : ∀ x y : V n, b (x + y) = b x + b y := by
        intro x y
        by_cases hx : x = 0
        · subst hx; simp [b]
        by_cases hy : y = 0
        · subst hy; simp [b]
        by_cases hxy : x = y
        · subst hxy; rw [two, z6]; simp [b]
        have hv : Valid x y := ⟨hx, hy, hxy⟩
        simp only [b, if_neg hx, if_neg hy, if_neg (sum_ne hv)]
        exact z7 _ _ _ _ (hall x y hv)
      let lin : V n →ₗ[ZMod 2] ZMod 2 := AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' b hb)
      refine ⟨lin, c, ?_⟩
      intro x hx b' hb'
      rw [ha x hx b' hb']
      show a x = b x + c
      simp only [b, if_neg hx]
      rw [add_assoc, z6, add_zero]

end PEqualNP.Outside.L_lib_759_aux

theorem PEqualNP.Outside.L_lib_759 : (∀ (n : Nat), 4 ≤ n →
  let F := ZMod 2
  let V := Fin n → F
  ∀ (available : V → Finset F), (∀ x : V, x ≠ 0 → (available x).Nonempty) →
    Iff (∃ (U T : Submodule F V) (mask : V →ₗ[F] F),
      Disjoint U T ∧ Module.finrank F U = 2 ∧ Module.finrank F T = 2 ∧
      (∀ x ∈ U, x ≠ 0 → 1 + mask x ∈ available x) ∧
      (∀ x ∈ T, x ≠ 0 → mask x ∈ available x))
    (¬(∃ (linear : V →ₗ[F] F) (offset : F), ∀ x : V, x ≠ 0 →
        ∀ b ∈ available x, b = linear x + offset))) := by
  intro n hn F V available hne
  exact L_lib_759_aux.main hn available hne

