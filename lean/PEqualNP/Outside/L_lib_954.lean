import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_954

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

lemma z2_add_self (a : F) : a + a = 0 := by revert a; decide
lemma z2_mul_self (a : F) : a * a = a := by revert a; decide
lemma z2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by revert a; decide
lemma z2_ne_iff_add_eq_one (a b : F) : a ≠ b ↔ a + b = 1 := by revert a b; decide
lemma z2_eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by revert a b h; decide
lemma z2_add_cancel_right (a b c : F) : a + c = b + c ↔ a = b := by revert a b c; decide

lemma vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  funext i; exact z2_add_self (v i)

lemma vec_eq_of_add_eq_zero {n : ℕ} {a b : Vec n} (h : a + b = 0) : a = b :=
  funext fun i => z2_eq_of_add_eq_zero (congrFun h i)

lemma dot_eq_zero_forall {n : ℕ} {v : Vec n} (h : ∀ x : Vec n, dotProduct v x = 0) : v = 0 := by
  funext i
  have hi := h (Pi.single i 1)
  simpa [dotProduct, Pi.single_apply] using hi

lemma exists_orth_ne_zero {k : ℕ} (S : Submodule F (Vec k)) (hS : S ≠ ⊤) :
    ∃ c : Vec k, c ≠ 0 ∧ ∀ w ∈ S, dotProduct c w = 0 := by
  obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
  have hTne : T ≠ ⊥ := by
    intro hT
    apply hS
    rw [hT] at hST
    exact eq_top_iff.2 (by simpa using hST.codisjoint.top_le)
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
  let B := Module.finBasis F T
  have ht_ne : B.repr ⟨t, htT⟩ ≠ 0 := by
    intro h
    apply ht0
    have := congrArg (fun z => (B.repr.symm z : Vec k)) h
    simpa using this
  obtain ⟨j0, hj0⟩ : ∃ j0, B.repr ⟨t, htT⟩ j0 ≠ 0 := by
    by_contra h
    push Not at h
    exact ht_ne (Finsupp.ext h)
  let projT : Vec k →ₗ[F] T := Submodule.projectionOnto T S hST.symm
  let φ : Vec k →ₗ[F] F := (B.coord j0).comp projT
  let c : Vec k := fun j => φ (Pi.single j 1)
  have hφ_eq : ∀ w : Vec k, dotProduct c w = φ w := by
    intro w
    have hw : w = ∑ j : Fin k, w j • Pi.single j (1 : F) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hw]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, dotProduct, c, mul_comm]
  refine ⟨c, ?_, ?_⟩
  · intro hc
    have h1 : φ t = 0 := by rw [← hφ_eq, hc]; simp
    have h2 : projT t = ⟨t, htT⟩ := Submodule.projectionOnto_apply_left hST.symm ⟨t, htT⟩
    have h3 : φ t = B.repr ⟨t, htT⟩ j0 := by simp [φ, h2, Module.Basis.coord_apply]
    exact hj0 (h3.symm.trans h1)
  · intro w hw
    rw [hφ_eq]
    have h2 : projT w = 0 := Submodule.projectionOnto_apply_right hST.symm ⟨w, hw⟩
    simp [φ, h2]

def evalMap {n k : ℕ} (u : Fin k → Vec n) : Vec n →ₗ[F] Vec k where
  toFun x j := dotProduct (u j) x
  map_add' x y := by funext j; simp [dotProduct_add]
  map_smul' r x := by funext j; simp [dotProduct_smul, smul_eq_mul]

lemma evalMap_surjective {n k : ℕ} {u : Fin k → Vec n} (hu : LinearIndependent F u) :
    Function.Surjective (evalMap u) := by
  by_contra hns
  have hne : LinearMap.range (evalMap u) ≠ ⊤ := by
    intro htop
    apply hns
    intro y
    have hy : y ∈ LinearMap.range (evalMap u) := by rw [htop]; trivial
    exact hy
  obtain ⟨c, hc0, hcorth⟩ := exists_orth_ne_zero (LinearMap.range (evalMap u)) hne
  have hsum : ∑ j : Fin k, c j • u j = 0 := by
    apply dot_eq_zero_forall
    intro x
    have hx := hcorth (evalMap u x) ⟨x, rfl⟩
    have hrew : dotProduct (∑ j : Fin k, c j • u j) x = dotProduct c (evalMap u x) := by
      simp only [evalMap, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    rw [hrew, hx]
  exact hc0 (funext (Fintype.linearIndependent_iff.1 hu c hsum))

lemma linearIndependent_pair {n : ℕ} {a b : Vec n} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    LinearIndependent F (![a, b] : Fin 2 → Vec n) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 : g 0 • a + g 1 • b = 0 := by simpa [Fin.sum_univ_two] using hg
  rcases z2_eq_zero_or_one (g 0) with h00 | h01 <;> rcases z2_eq_zero_or_one (g 1) with h10 | h11
  · fin_cases i <;> assumption
  · exfalso; rw [h00, h11] at h0; simp at h0; exact hb h0
  · exfalso; rw [h01, h10] at h0; simp at h0; exact ha h0
  · exfalso
    rw [h01, h11, one_smul, one_smul] at h0
    exact hab (vec_eq_of_add_eq_zero h0)

lemma fiber_card_eq {n k : ℕ} (L : Vec n →ₗ[F] Vec k) (hL : Function.Surjective L) (y : Vec k) :
    (Finset.univ.filter (fun x : Vec n => L x = y)).card =
      (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by
  obtain ⟨x0, rfl⟩ := hL y
  refine Finset.card_bij (fun x _ => x + x0) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [map_add, hx, vec_add_self]
  · intro x1 _ x2 _ h
    have := congrArg (· + x0) h
    simpa [add_assoc, vec_add_self] using this
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨z + x0, ?_, by simp [add_assoc, vec_add_self]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add, hz, zero_add]

lemma ker_card_mul {n k : ℕ} (L : Vec n →ₗ[F] Vec k) (hL : Function.Surjective L) :
    2 ^ k * (Finset.univ.filter (fun x : Vec n => L x = 0)).card = 2 ^ n := by
  have hpart : (Finset.univ : Finset (Vec n)).card =
      ∑ y : Vec k, (Finset.univ.filter (fun x : Vec n => L x = y)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext x; simp
    · intro y1 _ y2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      exact hne (hx1.symm.trans hx2)
  have h1 : (Finset.univ : Finset (Vec n)).card = 2 ^ n := by
    simp [Fintype.card_pi, ZMod.card]
  have h2 : (Finset.univ : Finset (Vec k)).card = 2 ^ k := by
    simp [Fintype.card_pi, ZMod.card]
  rw [h1] at hpart
  have hsum : ∑ y : Vec k, (Finset.univ.filter (fun x : Vec n => L x = y)).card =
      2 ^ k * (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by
    calc ∑ y : Vec k, (Finset.univ.filter (fun x : Vec n => L x = y)).card
        = ∑ _y : Vec k, (Finset.univ.filter (fun x : Vec n => L x = 0)).card :=
          Finset.sum_congr rfl fun y _ => fiber_card_eq L hL y
      _ = (Finset.univ : Finset (Vec k)).card * (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by
          simp
      _ = 2 ^ k * (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by rw [h2]
  exact hsum.symm.trans hpart.symm

lemma card_preimage_eq {n k : ℕ} (L : Vec n →ₗ[F] Vec k) (hL : Function.Surjective L)
    (P : Vec k → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : Vec n => P (L x))).card =
      (Finset.univ.filter P).card * (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by
  have hbij : Finset.univ.filter (fun x : Vec n => P (L x)) =
      (Finset.univ.filter P).biUnion (fun y => Finset.univ.filter (fun x : Vec n => L x = y)) := by
    ext x; simp
  rw [hbij, Finset.card_biUnion]
  · calc ∑ y ∈ Finset.univ.filter P, (Finset.univ.filter (fun x : Vec n => L x = y)).card
        = ∑ _y ∈ Finset.univ.filter P, (Finset.univ.filter (fun x : Vec n => L x = 0)).card :=
          Finset.sum_congr rfl fun y _ => fiber_card_eq L hL y
      _ = (Finset.univ.filter P).card * (Finset.univ.filter (fun x : Vec n => L x = 0)).card := by simp
  · intro y1 _ y2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    exact hne (hx1.symm.trans hx2)

lemma f2_quad_card_ge (c0 c1 d : F) :
    1 ≤ (Finset.univ.filter (fun z : Vec 2 => c0 * z 0 + c1 * z 1 + d ≠ z 0 * z 1)).card := by
  revert c0 c1 d; decide

lemma f3_quad_card_eq (d : F) :
    (Finset.univ.filter (fun z : Vec 3 => z 2 + d ≠ z 0 * z 1)).card = 4 := by
  revert d; decide

lemma err_card_ge {n : ℕ} {a b P : Vec n} {d : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    2 ^ n ≤ 4 * (Finset.univ.filter (fun x : Vec n => dotProduct P x + d ≠ dotProduct a x * dotProduct b x)).card := by
  have hli2 := linearIndependent_pair ha hb hab
  by_cases hP : P ∈ Submodule.span F ({a, b} : Set (Vec n))
  · rw [Submodule.mem_span_pair] at hP
    obtain ⟨c0, c1, rfl⟩ := hP
    let L := evalMap (![a, b] : Fin 2 → Vec n)
    have hL := evalMap_surjective hli2
    have heq : Finset.univ.filter (fun x : Vec n => dotProduct (c0 • a + c1 • b) x + d ≠ dotProduct a x * dotProduct b x) =
        Finset.univ.filter (fun x : Vec n => c0 * L x 0 + c1 * L x 1 + d ≠ L x 0 * L x 1) := by
      ext x
      simp [L, evalMap, add_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [heq, card_preimage_eq L hL (fun z : Vec 2 => c0 * z 0 + c1 * z 1 + d ≠ z 0 * z 1)]
    have hker := ker_card_mul L hL
    have hge := f2_quad_card_ge c0 c1 d
    have : 4 * (Finset.univ.filter (fun x : Vec n => L x = 0)).card = 2 ^ n := by simpa using hker
    nlinarith
  · have hli3 : LinearIndependent F (![a, b, P] : Fin 3 → Vec n) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hsum : g 0 • a + g 1 • b + g 2 • P = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hg
      rcases z2_eq_zero_or_one (g 2) with h20 | h21
      · rw [h20, zero_smul, add_zero] at hsum
        have h01 := Fintype.linearIndependent_iff.1 hli2 ![g 0, g 1] (by simpa [Fin.sum_univ_two] using hsum)
        fin_cases i
        · exact h01 0
        · exact h01 1
        · exact h20
      · exfalso
        rw [h21, one_smul] at hsum
        have hPeq : g 0 • a + g 1 • b = P := vec_eq_of_add_eq_zero hsum
        apply hP
        rw [← hPeq, Submodule.mem_span_pair]
        exact ⟨g 0, g 1, rfl⟩
    let L := evalMap (![a, b, P] : Fin 3 → Vec n)
    have hL := evalMap_surjective hli3
    have heq : Finset.univ.filter (fun x : Vec n => dotProduct P x + d ≠ dotProduct a x * dotProduct b x) =
        Finset.univ.filter (fun x : Vec n => L x 2 + d ≠ L x 0 * L x 1) := by
      ext x; simp [L, evalMap]
    rw [heq, card_preimage_eq L hL (fun z : Vec 3 => z 2 + d ≠ z 0 * z 1), f3_quad_card_eq d]
    have hker := ker_card_mul L hL
    have : 8 * (Finset.univ.filter (fun x : Vec n => L x = 0)).card = 2 ^ n := by simpa using hker
    omega

lemma deg4_sum_eq_one (α β : Vec 4) (d1 d2 : F) :
    ∑ s : Vec 4, (s 0 * s 1 + dotProduct α s + d1) * (s 2 * s 3 + dotProduct β s + d2) = 1 := by
  have h1 : ∀ c : Vec 4 → F, (∃ k : Fin 4, ∀ s : Vec 4, c (s + Pi.single k 1) = c s) → ∑ s : Vec 4, c s = 0 := by
    intro c ⟨k, hk⟩
    let f : Vec 4 → Vec 4 := fun s => s + Pi.single k 1
    have hf_inv : ∀ s, f (f s) = s := fun s => by
      simp [f, add_assoc, vec_add_self]
    have hsplit : (Finset.univ : Finset (Vec 4)) =
        Finset.univ.filter (fun s : Vec 4 => s k = 0) ∪ Finset.univ.filter (fun s : Vec 4 => s k = 1) := by
      ext s; simp [z2_eq_zero_or_one]
    have hdisj : Disjoint (Finset.univ.filter (fun s : Vec 4 => s k = 0))
        (Finset.univ.filter (fun s : Vec 4 => s k = 1)) := by
      rw [Finset.disjoint_left]; intro s h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1] at h2; exact absurd h2 (by decide)
    have hpair : ∑ s ∈ Finset.univ.filter (fun s : Vec 4 => s k = 1), c s =
        ∑ s ∈ Finset.univ.filter (fun s : Vec 4 => s k = 0), c (f s) := by
      refine (Finset.sum_bij (fun s _ => f s) ?_ ?_ ?_ ?_).symm
      · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        simp [f, hs]
      · intro s1 _ s2 _ h; rw [← hf_inv s1, ← hf_inv s2, h]
      · intro s hs; refine ⟨f s, ?_, hf_inv s⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        simp [f, hs, z2_add_self]
      · intro s _; rfl
    calc ∑ s : Vec 4, c s
        = ∑ s ∈ Finset.univ.filter (fun s : Vec 4 => s k = 0), c s +
          ∑ s ∈ Finset.univ.filter (fun s : Vec 4 => s k = 1), c s := by
          conv_lhs => rw [hsplit]
          exact Finset.sum_union hdisj
      _ = ∑ s ∈ Finset.univ.filter (fun s : Vec 4 => s k = 0), (c s + c (f s)) := by
          rw [hpair, Finset.sum_add_distrib]
      _ = 0 := Finset.sum_eq_zero fun s _ => by rw [hk s, z2_add_self]
  have hprod : ∑ s : Vec 4, s 0 * s 1 * (s 2 * s 3) = 1 := by
    have hsingle : ∀ s : Vec 4, s 0 * s 1 * (s 2 * s 3) = if s = (fun _ => 1) then 1 else 0 := by
      intro s
      split_ifs with hs
      · subst hs; simp
      · have : ∃ i : Fin 4, s i = 0 := by
          by_contra hall; push Not at hall
          apply hs; funext i
          rcases z2_eq_zero_or_one (s i) with h | h
          · exact absurd h (hall i)
          · exact h
        obtain ⟨i, hi⟩ := this
        fin_cases i <;> simp_all
    simp [hsingle]
  have hexp : ∀ s : Vec 4, (s 0 * s 1 + dotProduct α s + d1) * (s 2 * s 3 + dotProduct β s + d2) =
      s 0 * s 1 * (s 2 * s 3) +
      (s 0 * s 1 * (dotProduct β s + d2) + (dotProduct α s + d1) * (s 2 * s 3) +
        (dotProduct α s + d1) * (dotProduct β s + d2)) := fun s => by ring
  simp_rw [hexp, Finset.sum_add_distrib, hprod]
  suffices hrest : ∑ s : Vec 4, s 0 * s 1 * (dotProduct β s + d2) = 0 ∧
      ∑ s : Vec 4, (dotProduct α s + d1) * (s 2 * s 3) = 0 ∧
      ∑ s : Vec 4, (dotProduct α s + d1) * (dotProduct β s + d2) = 0 by
    rw [hrest.1, hrest.2.1, hrest.2.2]; simp
  refine ⟨?_, ?_, ?_⟩
  · have hlin : ∀ s : Vec 4, s 0 * s 1 * (dotProduct β s + d2) =
        s 0 * s 1 * d2 + ∑ j : Fin 4, β j * (s 0 * s 1 * s j) := by
      intro s
      rw [mul_add, dotProduct, Finset.mul_sum, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hlin, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have ht0 : ∑ s : Vec 4, s 0 * s 1 * d2 = 0 := h1 _ ⟨2, fun s => by simp [Pi.single_apply]⟩
    have ht1 : ∀ j : Fin 4, ∑ s : Vec 4, β j * (s 0 * s 1 * s j) = 0 := by
      intro j
      fin_cases j
      · exact h1 _ ⟨2, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨2, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨3, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨2, fun s => by simp [Pi.single_apply]⟩
    simp [ht0, ht1]
  · have hlin : ∀ s : Vec 4, (dotProduct α s + d1) * (s 2 * s 3) =
        d1 * (s 2 * s 3) + ∑ j : Fin 4, α j * (s j * (s 2 * s 3)) := by
      intro s
      rw [add_mul, dotProduct, Finset.sum_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hlin, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have ht0 : ∑ s : Vec 4, d1 * (s 2 * s 3) = 0 := h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
    have ht1 : ∀ j : Fin 4, ∑ s : Vec 4, α j * (s j * (s 2 * s 3)) = 0 := by
      intro j
      fin_cases j
      · exact h1 _ ⟨1, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
    simp [ht0, ht1]
  · have hlin : ∀ s : Vec 4, (dotProduct α s + d1) * (dotProduct β s + d2) =
        d1 * d2 + ∑ j : Fin 4, (d1 * β j + d2 * α j) * s j +
        ∑ j : Fin 4, ∑ k : Fin 4, (α j * β k) * (s j * s k) := by
      intro s
      have e1 : (dotProduct α s + d1) * (dotProduct β s + d2) =
          d1 * d2 + (d1 * dotProduct β s + d2 * dotProduct α s) + dotProduct α s * dotProduct β s := by ring
      rw [e1]
      congr 1
      · congr 1
        simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp only [dotProduct, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    simp_rw [hlin, Finset.sum_add_distrib]
    have ht0 : ∑ _s : Vec 4, d1 * d2 = 0 := h1 _ ⟨0, fun _ => rfl⟩
    have ht1 : ∑ s : Vec 4, ∑ j : Fin 4, (d1 * β j + d2 * α j) * s j = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro j _
      fin_cases j
      · exact h1 _ ⟨1, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
      · exact h1 _ ⟨0, fun s => by simp [Pi.single_apply]⟩
    have ht2 : ∑ s : Vec 4, ∑ j : Fin 4, ∑ k : Fin 4, (α j * β k) * (s j * s k) = 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro k _
      have hex : ∃ r : Fin 4, r ≠ j ∧ r ≠ k := by
        fin_cases j <;> fin_cases k <;> decide
      obtain ⟨r, hrj, hrk⟩ := hex
      exact h1 _ ⟨r, fun s => by simp [Pi.single_apply, Ne.symm hrj, Ne.symm hrk]⟩
    simp [ht0, ht1, ht2]

lemma planes_not_disjoint {n : ℕ} {a1 b1 a2 b2 P1 P2 : Vec n} {d1 d2 : F}
    (hdisj : ∀ x : Vec n,
      (dotProduct a1 x * dotProduct b1 x + dotProduct P1 x + d1) *
      (dotProduct a2 x * dotProduct b2 x + dotProduct P2 x + d2) = 0) :
    ¬ LinearIndependent F (![a1, b1, a2, b2] : Fin 4 → Vec n) := by
  intro hli
  have hsurj := evalMap_surjective hli
  have hv : ∀ k : Fin 4, ∃ v : Vec n, evalMap ![a1, b1, a2, b2] v = Pi.single k 1 :=
    fun k => hsurj (Pi.single k 1)
  choose v hv using hv
  let x : Vec 4 → Vec n := fun s => ∑ k : Fin 4, s k • v k
  have hx : ∀ s : Vec 4, evalMap ![a1, b1, a2, b2] (x s) = s := by
    intro s
    simp only [x, map_sum, map_smul, hv]
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hda1 : ∀ s, dotProduct a1 (x s) = s 0 := fun s => congrFun (hx s) 0
  have hdb1 : ∀ s, dotProduct b1 (x s) = s 1 := fun s => congrFun (hx s) 1
  have hda2 : ∀ s, dotProduct a2 (x s) = s 2 := fun s => congrFun (hx s) 2
  have hdb2 : ∀ s, dotProduct b2 (x s) = s 3 := fun s => congrFun (hx s) 3
  let α : Vec 4 := fun k => dotProduct P1 (v k)
  let β : Vec 4 := fun k => dotProduct P2 (v k)
  have hdP1 : ∀ s, dotProduct P1 (x s) = dotProduct α s := by
    intro s
    simp only [x, α, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      mul_comm, mul_left_comm]
    rw [Finset.sum_comm]
  have hdP2 : ∀ s, dotProduct P2 (x s) = dotProduct β s := by
    intro s
    simp only [x, β, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
      mul_comm, mul_left_comm]
    rw [Finset.sum_comm]
  have hzero : ∑ s : Vec 4, (s 0 * s 1 + dotProduct α s + d1) * (s 2 * s 3 + dotProduct β s + d2) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    rw [← hda1 s, ← hdb1 s, ← hda2 s, ← hdb2 s, ← hdP1 s, ← hdP2 s]
    exact hdisj (x s)
  rw [deg4_sum_eq_one] at hzero
  exact absurd hzero (by decide)

lemma plane_inter_ne_bot {n : ℕ} {a1 b1 a2 b2 : Vec n}
    (h1 : LinearIndependent F (![a1, b1] : Fin 2 → Vec n))
    (h2 : LinearIndependent F (![a2, b2] : Fin 2 → Vec n))
    (hdep : ¬ LinearIndependent F (![a1, b1, a2, b2] : Fin 4 → Vec n)) :
    (Submodule.span F ({a1, b1} : Set (Vec n)) ⊓ Submodule.span F ({a2, b2} : Set (Vec n))) ≠ ⊥ := by
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨g, hg, j, hj⟩ := hdep
  have hsum : g 0 • a1 + g 1 • b1 = g 2 • a2 + g 3 • b2 := by
    apply vec_eq_of_add_eq_zero
    have h0 : g 0 • a1 + g 1 • b1 + g 2 • a2 + g 3 • b2 = 0 := by
      simpa [Fin.sum_univ_four, add_assoc] using hg
    simpa [add_assoc] using h0
  have hne : g 0 • a1 + g 1 • b1 ≠ 0 := by
    intro hz
    have h01 := Fintype.linearIndependent_iff.1 h1 ![g 0, g 1] (by simpa [Fin.sum_univ_two] using hz)
    have h23 := Fintype.linearIndependent_iff.1 h2 ![g 2, g 3] (by simpa [Fin.sum_univ_two] using hsum.symm.trans hz)
    fin_cases j
    · exact hj (h01 0)
    · exact hj (h01 1)
    · exact hj (h23 0)
    · exact hj (h23 1)
  intro hbot
  have hmem : g 0 • a1 + g 1 • b1 ∈ Submodule.span F ({a1, b1} : Set (Vec n)) ⊓
      Submodule.span F ({a2, b2} : Set (Vec n)) := by
    refine ⟨?_, ?_⟩
    · change _ ∈ Submodule.span F ({a1, b1} : Set (Vec n))
      rw [Submodule.mem_span_pair]; exact ⟨g 0, g 1, rfl⟩
    · change _ ∈ Submodule.span F ({a2, b2} : Set (Vec n))
      rw [hsum, Submodule.mem_span_pair]; exact ⟨g 2, g 3, rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hne hmem

lemma span_pair_finrank {n : ℕ} {a b : Vec n} (h : LinearIndependent F (![a, b] : Fin 2 → Vec n)) :
    Module.finrank F (Submodule.span F ({a, b} : Set (Vec n))) = 2 := by
  have hrg : Set.range (![a, b] : Fin 2 → Vec n) = ({a, b} : Set (Vec n)) := by
    ext x; simp [Fin.exists_fin_two, or_comm]
  rw [← hrg, finrank_span_eq_card h]
  simp

lemma span_pair_basis_quad {n : ℕ} {a b w c : Vec n}
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hsp : Submodule.span F ({a, b} : Set (Vec n)) = Submodule.span F ({w, c} : Set (Vec n))) :
    ∃ r : Vec n, ∀ x : Vec n,
      dotProduct a x * dotProduct b x = dotProduct w x * dotProduct c x + dotProduct r x := by
  have hmem : ∀ v ∈ Submodule.span F ({w, c} : Set (Vec n)), v = 0 ∨ v = w ∨ v = c ∨ v = w + c := by
    intro v hv
    rw [Submodule.mem_span_pair] at hv
    obtain ⟨s, t, rfl⟩ := hv
    rcases z2_eq_zero_or_one s with rfl | rfl <;> rcases z2_eq_zero_or_one t with rfl | rfl <;> simp
  have ha' : a ∈ Submodule.span F ({w, c} : Set (Vec n)) := by
    rw [← hsp]; exact Submodule.subset_span (by simp)
  have hb' : b ∈ Submodule.span F ({w, c} : Set (Vec n)) := by
    rw [← hsp]; exact Submodule.subset_span (by simp)
  rcases hmem a ha' with ha0 | haw | hac | hawc
  · exact absurd ha0 ha
  · rcases hmem b hb' with hb0 | hbw | hbc | hbwc
    · exact absurd hb0 hb
    · exact absurd (haw.trans hbw.symm) hab
    · exact ⟨0, fun x => by simp [haw, hbc]⟩
    · refine ⟨w, fun x => ?_⟩
      rw [haw, hbwc, add_dotProduct, mul_add, z2_mul_self]; ring
  · rcases hmem b hb' with hb0 | hbw | hbc | hbwc
    · exact absurd hb0 hb
    · exact ⟨0, fun x => by simp [hac, hbw, mul_comm]⟩
    · exact absurd (hac.trans hbc.symm) hab
    · refine ⟨c, fun x => ?_⟩
      rw [hac, hbwc, add_dotProduct, mul_add, z2_mul_self]; ring
  · rcases hmem b hb' with hb0 | hbw | hbc | hbwc
    · exact absurd hb0 hb
    · refine ⟨w, fun x => ?_⟩
      rw [hawc, hbw, add_dotProduct, add_mul, z2_mul_self]; ring
    · refine ⟨c, fun x => ?_⟩
      rw [hawc, hbc, add_dotProduct, add_mul, z2_mul_self]
    · exact absurd (hawc.trans hbwc.symm) hab

lemma affine_disj_on_half {n : ℕ} {w P Q : Vec n} {d e : F} (hw : w ≠ 0) (b : F)
    (hP : ∃ x : Vec n, dotProduct w x = b ∧ dotProduct P x + d = 1)
    (hQ : ∃ x : Vec n, dotProduct w x = b ∧ dotProduct Q x + e = 1)
    (hdisj : ∀ x : Vec n, dotProduct w x = b → (dotProduct P x + d) * (dotProduct Q x + e) = 0) :
    P + Q ∈ Submodule.span F ({w} : Set (Vec n)) ∧
      ∀ x : Vec n, dotProduct w x = b → dotProduct P x + d + (dotProduct Q x + e) = 1 := by
  have hPw : P ∉ Submodule.span F ({w} : Set (Vec n)) := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨s, rfl⟩ := hmem
    obtain ⟨x1, hx1w, hx1⟩ := hP
    obtain ⟨x2, hx2w, hx2⟩ := hQ
    have h1 : dotProduct (s • w) x2 + d = 1 := by
      rw [smul_dotProduct, hx2w, ← hx1w, ← smul_dotProduct]; exact hx1
    have := hdisj x2 hx2w
    rw [h1, hx2] at this
    exact absurd this (by decide)
  have hQw : Q ∉ Submodule.span F ({w} : Set (Vec n)) := by
    intro hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨s, rfl⟩ := hmem
    obtain ⟨x1, hx1w, hx1⟩ := hP
    obtain ⟨x2, hx2w, hx2⟩ := hQ
    have h2 : dotProduct (s • w) x1 + e = 1 := by
      rw [smul_dotProduct, hx1w, ← hx2w, ← smul_dotProduct]; exact hx2
    have := hdisj x1 hx1w
    rw [hx1, h2] at this
    exact absurd this (by decide)
  have hPQ : P + Q ∈ Submodule.span F ({w} : Set (Vec n)) := by
    by_contra hnot
    have hli : LinearIndependent F (![w, P, Q] : Fin 3 → Vec n) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h0 : g 0 • w + g 1 • P + g 2 • Q = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hg
      rcases z2_eq_zero_or_one (g 1) with h10 | h11 <;> rcases z2_eq_zero_or_one (g 2) with h20 | h21
      · rw [h10, h20] at h0; simp only [zero_smul, add_zero] at h0
        rcases z2_eq_zero_or_one (g 0) with h00 | h01
        · fin_cases i <;> assumption
        · exfalso; rw [h01, one_smul] at h0; exact hw h0
      · exfalso; rw [h10, h21] at h0; simp only [zero_smul, add_zero, one_smul] at h0
        apply hQw; rw [Submodule.mem_span_singleton]; exact ⟨g 0, vec_eq_of_add_eq_zero h0⟩
      · exfalso; rw [h11, h20] at h0; simp only [zero_smul, add_zero, one_smul] at h0
        apply hPw; rw [Submodule.mem_span_singleton]; exact ⟨g 0, vec_eq_of_add_eq_zero h0⟩
      · exfalso; rw [h11, h21] at h0; simp only [one_smul] at h0
        apply hnot; rw [Submodule.mem_span_singleton]
        refine ⟨g 0, vec_eq_of_add_eq_zero (by simpa [add_assoc] using h0)⟩
    obtain ⟨x, hx⟩ := evalMap_surjective hli ![b, d + 1, e + 1]
    have hxw : dotProduct w x = b := congrFun hx 0
    have hxP : dotProduct P x = d + 1 := congrFun hx 1
    have hxQ : dotProduct Q x = e + 1 := congrFun hx 2
    have hmul := hdisj x hxw
    rw [hxP, hxQ] at hmul
    have h1 : d + 1 + d = 1 := by linear_combination z2_add_self d
    have h2 : e + 1 + e = 1 := by linear_combination z2_add_self e
    rw [h1, h2] at hmul
    exact absurd hmul (by decide)
  refine ⟨hPQ, ?_⟩
  rw [Submodule.mem_span_singleton] at hPQ
  obtain ⟨s, hs⟩ := hPQ
  have hQeq : Q = P + s • w := by
    apply vec_eq_of_add_eq_zero
    funext i
    have hi := congrFun hs i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
    linear_combination hi + z2_add_self (P i) + z2_add_self (Q i)
  obtain ⟨x1, hx1w, hx1⟩ := hP
  have hnot0 : dotProduct P x1 + d + (dotProduct Q x1 + e) = 1 := by
    have hmul := hdisj x1 hx1w
    rw [hx1, one_mul] at hmul
    rw [hx1, hmul, add_zero]
  intro x hxw
  rw [hQeq, add_dotProduct, smul_dotProduct, smul_eq_mul, hxw]
  rw [hQeq, add_dotProduct, smul_dotProduct, smul_eq_mul, hx1w] at hnot0
  have hcancel : ∀ u : F, u + d + (u + s * b + e) = d + s * b + e := fun u => by
    linear_combination z2_add_self u
  rw [hcancel] at hnot0 ⊢
  exact hnot0

lemma no_three_on_half {n : ℕ} {w : Vec n} (hw : w ≠ 0) (b : F)
    {P1 P2 P3 : Vec n} {d1 d2 d3 : F}
    (h1 : ∃ x, dotProduct w x = b ∧ dotProduct P1 x + d1 = 1)
    (h2 : ∃ x, dotProduct w x = b ∧ dotProduct P2 x + d2 = 1)
    (h3 : ∃ x, dotProduct w x = b ∧ dotProduct P3 x + d3 = 1)
    (h12 : ∀ x, dotProduct w x = b → (dotProduct P1 x + d1) * (dotProduct P2 x + d2) = 0)
    (h13 : ∀ x, dotProduct w x = b → (dotProduct P1 x + d1) * (dotProduct P3 x + d3) = 0)
    (h23 : ∀ x, dotProduct w x = b → (dotProduct P2 x + d2) * (dotProduct P3 x + d3) = 0) : False := by
  have c12 := (affine_disj_on_half hw b h1 h2 h12).2
  have c13 := (affine_disj_on_half hw b h1 h3 h13).2
  have c23 := (affine_disj_on_half hw b h2 h3 h23).2
  obtain ⟨x, hxw, _⟩ := h1
  have s1 := c12 x hxw
  have s2 := c13 x hxw
  have s3 := c23 x hxw
  have hsum : (dotProduct P1 x + d1 + (dotProduct P2 x + d2)) +
      (dotProduct P1 x + d1 + (dotProduct P3 x + d3)) +
      (dotProduct P2 x + d2 + (dotProduct P3 x + d3)) = 0 := by
    linear_combination z2_add_self (dotProduct P1 x + d1) +
      z2_add_self (dotProduct P2 x + d2) + z2_add_self (dotProduct P3 x + d3)
  rw [s1, s2, s3] at hsum
  exact absurd hsum (by decide)

lemma zero_on_half_slope {n : ℕ} {w P : Vec n} {d : F} (hw : w ≠ 0) (b : F)
    (hz : ∀ x : Vec n, dotProduct w x = b → dotProduct P x + d = 0) :
    P ∈ Submodule.span F ({w} : Set (Vec n)) := by
  by_contra hnot
  have hli : LinearIndependent F (![w, P] : Fin 2 → Vec n) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : g 0 • w + g 1 • P = 0 := by simpa [Fin.sum_univ_two] using hg
    rcases z2_eq_zero_or_one (g 1) with h10 | h11
    · rw [h10, zero_smul, add_zero] at h0
      rcases z2_eq_zero_or_one (g 0) with h00 | h01
      · fin_cases i <;> assumption
      · exfalso; rw [h01, one_smul] at h0; exact hw h0
    · exfalso; rw [h11, one_smul] at h0
      apply hnot; rw [Submodule.mem_span_singleton]; exact ⟨g 0, vec_eq_of_add_eq_zero h0⟩
  obtain ⟨x, hx⟩ := evalMap_surjective hli ![b, d + 1]
  have hxw : dotProduct w x = b := congrFun hx 0
  have hxP : dotProduct P x = d + 1 := congrFun hx 1
  have h0 := hz x hxw
  rw [hxP] at h0
  have : d + 1 + d = 1 := by linear_combination z2_add_self d
  rw [this] at h0
  exact absurd h0 (by decide)

lemma no_three_common {n : ℕ} {w c1 c2 c3 P1 P2 P3 : Vec n} {d1 d2 d3 : F}
    (hli : LinearIndependent F (![w, c1, c2, c3] : Fin 4 → Vec n))
    (h12 : ∀ x : Vec n, (dotProduct w x * dotProduct c1 x + dotProduct P1 x + d1) *
      (dotProduct w x * dotProduct c2 x + dotProduct P2 x + d2) = 0)
    (h13 : ∀ x : Vec n, (dotProduct w x * dotProduct c1 x + dotProduct P1 x + d1) *
      (dotProduct w x * dotProduct c3 x + dotProduct P3 x + d3) = 0)
    (h23 : ∀ x : Vec n, (dotProduct w x * dotProduct c2 x + dotProduct P2 x + d2) *
      (dotProduct w x * dotProduct c3 x + dotProduct P3 x + d3) = 0) : False := by
  have hw : w ≠ 0 := hli.ne_zero 0
  have hnot_span : ∀ (e1 e2 e3 : F), (e1 ≠ 0 ∨ e2 ≠ 0 ∨ e3 ≠ 0) →
      e1 • c1 + e2 • c2 + e3 • c3 ∉ Submodule.span F ({w} : Set (Vec n)) := by
    intro e1 e2 e3 hne hmem
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hsum : s • w + (e1 • c1 + (e2 • c2 + e3 • c3)) = 0 := by
      have : s • w + (e1 • c1 + e2 • c2 + e3 • c3) = 0 := by
        rw [hs]; exact vec_add_self _
      simpa [add_assoc] using this
    have hall := Fintype.linearIndependent_iff.1 hli ![s, e1, e2, e3]
      (by simpa [Fin.sum_univ_four, add_assoc] using hsum)
    rcases hne with h | h | h
    · exact h (hall 1)
    · exact h (hall 2)
    · exact h (hall 3)
  have hdisj0_12 : ∀ x, dotProduct w x = 0 → (dotProduct P1 x + d1) * (dotProduct P2 x + d2) = 0 := by
    intro x hx; have := h12 x; simpa [hx] using this
  have hdisj0_13 : ∀ x, dotProduct w x = 0 → (dotProduct P1 x + d1) * (dotProduct P3 x + d3) = 0 := by
    intro x hx; have := h13 x; simpa [hx] using this
  have hdisj0_23 : ∀ x, dotProduct w x = 0 → (dotProduct P2 x + d2) * (dotProduct P3 x + d3) = 0 := by
    intro x hx; have := h23 x; simpa [hx] using this
  have hdisj1_12 : ∀ x, dotProduct w x = 1 → (dotProduct (P1 + c1) x + d1) * (dotProduct (P2 + c2) x + d2) = 0 := by
    intro x hx; have := h12 x; simpa [hx, add_dotProduct, add_comm, add_left_comm] using this
  have hdisj1_13 : ∀ x, dotProduct w x = 1 → (dotProduct (P1 + c1) x + d1) * (dotProduct (P3 + c3) x + d3) = 0 := by
    intro x hx; have := h13 x; simpa [hx, add_dotProduct, add_comm, add_left_comm] using this
  have hdisj1_23 : ∀ x, dotProduct w x = 1 → (dotProduct (P2 + c2) x + d2) * (dotProduct (P3 + c3) x + d3) = 0 := by
    intro x hx; have := h23 x; simpa [hx, add_dotProduct, add_comm, add_left_comm] using this
  have hnot_both : ∀ (P c : Vec n) (d : F), c ∉ Submodule.span F ({w} : Set (Vec n)) →
      (∃ x, dotProduct w x = 0 ∧ dotProduct P x + d = 1) ∨
      (∃ x, dotProduct w x = 1 ∧ dotProduct (P + c) x + d = 1) := by
    intro P c d hc
    by_contra h
    push Not at h
    have h0 : ∀ x, dotProduct w x = 0 → dotProduct P x + d = 0 := fun x hx =>
      (z2_eq_zero_or_one _).resolve_right (h.1 x hx)
    have h1 : ∀ x, dotProduct w x = 1 → dotProduct (P + c) x + d = 0 := fun x hx =>
      (z2_eq_zero_or_one _).resolve_right (h.2 x hx)
    have hp0 := zero_on_half_slope hw 0 h0
    have hp1 := zero_on_half_slope hw 1 h1
    have hc' : c ∈ Submodule.span F ({w} : Set (Vec n)) := by
      have hsum := Submodule.add_mem _ hp0 hp1
      convert hsum using 1
      funext i; simp only [Pi.add_apply]; linear_combination -z2_add_self (P i)
    exact hc hc'
  have ha1 := hnot_both P1 c1 d1 (by simpa using hnot_span 1 0 0 (Or.inl one_ne_zero))
  have ha2 := hnot_both P2 c2 d2 (by simpa using hnot_span 0 1 0 (Or.inr (Or.inl one_ne_zero)))
  have ha3 := hnot_both P3 c3 d3 (by simpa using hnot_span 0 0 1 (Or.inr (Or.inr one_ne_zero)))
  have aux_contra : ∀ (cA cB cC PA PB PC : Vec n) (dA dB dC : F),
      (∀ e1 e2 e3 : F, (e1 ≠ 0 ∨ e2 ≠ 0 ∨ e3 ≠ 0) → e1 • cA + e2 • cB + e3 • cC ∉ Submodule.span F ({w} : Set (Vec n))) →
      (∃ x, dotProduct w x = 0 ∧ dotProduct PA x + dA = 1) →
      (∃ x, dotProduct w x = 0 ∧ dotProduct PB x + dB = 1) →
      (∀ x, dotProduct w x = 0 → (dotProduct PA x + dA) * (dotProduct PB x + dB) = 0) →
      (∀ x, dotProduct w x = 0 → (dotProduct PA x + dA) * (dotProduct PC x + dC) = 0) →
      (∀ x, dotProduct w x = 0 → (dotProduct PB x + dB) * (dotProduct PC x + dC) = 0) →
      (∀ x, dotProduct w x = 1 → (dotProduct (PA + cA) x + dA) * (dotProduct (PC + cC) x + dC) = 0) →
      (∀ x, dotProduct w x = 1 → (dotProduct (PB + cB) x + dB) * (dotProduct (PC + cC) x + dC) = 0) →
      False := by
    intro cA cB cC PA PB PC dA dB dC hns hA0 hB0 hd0AB hd0AC hd0BC hd1AC hd1BC
    have hAB := (affine_disj_on_half hw 0 hA0 hB0 hd0AB).1
    have hC0_zero : ∀ x, dotProduct w x = 0 → dotProduct PC x + dC = 0 := by
      intro x hx
      by_contra hne
      have h1 : dotProduct PC x + dC = 1 := (z2_eq_zero_or_one _).resolve_left hne
      exact no_three_on_half hw 0 hA0 hB0 ⟨x, hx, h1⟩ hd0AB hd0AC hd0BC
    have hPC := zero_on_half_slope hw 0 hC0_zero
    have hC1 : ∃ x, dotProduct w x = 1 ∧ dotProduct (PC + cC) x + dC = 1 := by
      rcases hnot_both PC cC dC (by simpa using hns 0 0 1 (Or.inr (Or.inr one_ne_zero))) with ⟨x, hx, h1⟩ | h
      · exfalso; rw [hC0_zero x hx] at h1; exact absurd h1 (by decide)
      · exact h
    by_cases hA1 : ∃ x, dotProduct w x = 1 ∧ dotProduct (PA + cA) x + dA = 1
    · have hAC1 := (affine_disj_on_half hw 1 hA1 hC1 hd1AC).1
      by_cases hB1 : ∃ x, dotProduct w x = 1 ∧ dotProduct (PB + cB) x + dB = 1
      · have hBC1 := (affine_disj_on_half hw 1 hB1 hC1 hd1BC).1
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hAC1) hBC1
        have : cA + cB ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i) + z2_add_self (cC i))
        exact hns 1 1 0 (Or.inl one_ne_zero) (by simpa using this)
      · push Not at hB1
        have hPBcB := zero_on_half_slope hw 1 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hB1 x hx))
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hAC1) (Submodule.add_mem _ hPBcB hPC)
        have : cA + cB + cC ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i))
        exact hns 1 1 1 (Or.inl one_ne_zero) (by simpa using this)
    · push Not at hA1
      have hPAcA := zero_on_half_slope hw 1 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hA1 x hx))
      by_cases hB1 : ∃ x, dotProduct w x = 1 ∧ dotProduct (PB + cB) x + dB = 1
      · have hBC1 := (affine_disj_on_half hw 1 hB1 hC1 hd1BC).1
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hBC1) (Submodule.add_mem _ hPAcA hPC)
        have : cA + cB + cC ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i))
        exact hns 1 1 1 (Or.inl one_ne_zero) (by simpa using this)
      · push Not at hB1
        have hPBcB := zero_on_half_slope hw 1 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hB1 x hx))
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hPAcA) hPBcB
        have : cA + cB ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i))
        exact hns 1 1 0 (Or.inl one_ne_zero) (by simpa using this)
  have aux_contra1 : ∀ (cA cB cC PA PB PC : Vec n) (dA dB dC : F),
      (∀ e1 e2 e3 : F, (e1 ≠ 0 ∨ e2 ≠ 0 ∨ e3 ≠ 0) → e1 • cA + e2 • cB + e3 • cC ∉ Submodule.span F ({w} : Set (Vec n))) →
      (∃ x, dotProduct w x = 1 ∧ dotProduct (PA + cA) x + dA = 1) →
      (∃ x, dotProduct w x = 1 ∧ dotProduct (PB + cB) x + dB = 1) →
      (∀ x, dotProduct w x = 1 → (dotProduct (PA + cA) x + dA) * (dotProduct (PB + cB) x + dB) = 0) →
      (∀ x, dotProduct w x = 1 → (dotProduct (PA + cA) x + dA) * (dotProduct (PC + cC) x + dC) = 0) →
      (∀ x, dotProduct w x = 1 → (dotProduct (PB + cB) x + dB) * (dotProduct (PC + cC) x + dC) = 0) →
      (∀ x, dotProduct w x = 0 → (dotProduct PA x + dA) * (dotProduct PC x + dC) = 0) →
      (∀ x, dotProduct w x = 0 → (dotProduct PB x + dB) * (dotProduct PC x + dC) = 0) →
      False := by
    intro cA cB cC PA PB PC dA dB dC hns hA1 hB1 hd1AB hd1AC hd1BC hd0AC hd0BC
    have hAB := (affine_disj_on_half hw 1 hA1 hB1 hd1AB).1
    have hC1_zero : ∀ x, dotProduct w x = 1 → dotProduct (PC + cC) x + dC = 0 := by
      intro x hx
      by_contra hne
      have h1 : dotProduct (PC + cC) x + dC = 1 := (z2_eq_zero_or_one _).resolve_left hne
      exact no_three_on_half hw 1 hA1 hB1 ⟨x, hx, h1⟩ hd1AB hd1AC hd1BC
    have hPCcC := zero_on_half_slope hw 1 hC1_zero
    have hC0 : ∃ x, dotProduct w x = 0 ∧ dotProduct PC x + dC = 1 := by
      rcases hnot_both PC cC dC (by simpa using hns 0 0 1 (Or.inr (Or.inr one_ne_zero))) with h | ⟨x, hx, h1⟩
      · exact h
      · exfalso; rw [hC1_zero x hx] at h1; exact absurd h1 (by decide)
    by_cases hA0 : ∃ x, dotProduct w x = 0 ∧ dotProduct PA x + dA = 1
    · have hAC0 := (affine_disj_on_half hw 0 hA0 hC0 hd0AC).1
      by_cases hB0 : ∃ x, dotProduct w x = 0 ∧ dotProduct PB x + dB = 1
      · have hBC0 := (affine_disj_on_half hw 0 hB0 hC0 hd0BC).1
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hAC0) hBC0
        have : cA + cB ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i))
        exact hns 1 1 0 (Or.inl one_ne_zero) (by simpa using this)
      · push Not at hB0
        have hPB := zero_on_half_slope hw 0 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hB0 x hx))
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hAC0) (Submodule.add_mem _ hPB hPCcC)
        have : cA + cB + cC ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i))
        exact hns 1 1 1 (Or.inl one_ne_zero) (by simpa using this)
    · push Not at hA0
      have hPA := zero_on_half_slope hw 0 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hA0 x hx))
      by_cases hB0 : ∃ x, dotProduct w x = 0 ∧ dotProduct PB x + dB = 1
      · have hBC0 := (affine_disj_on_half hw 0 hB0 hC0 hd0BC).1
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hBC0) (Submodule.add_mem _ hPA hPCcC)
        have : cA + cB + cC ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i) + z2_add_self (PC i))
        exact hns 1 1 1 (Or.inl one_ne_zero) (by simpa using this)
      · push Not at hB0
        have hPB := zero_on_half_slope hw 0 (fun x hx => (z2_eq_zero_or_one _).resolve_right (hB0 x hx))
        have hsum := Submodule.add_mem _ (Submodule.add_mem _ hAB hPA) hPB
        have : cA + cB ∈ Submodule.span F ({w} : Set (Vec n)) := by
          convert hsum using 1
          funext i; simp only [Pi.add_apply]
          linear_combination -(z2_add_self (PA i) + z2_add_self (PB i))
        exact hns 1 1 0 (Or.inl one_ne_zero) (by simpa using this)
  rcases ha1 with h10 | h11 <;> rcases ha2 with h20 | h21 <;> rcases ha3 with h30 | h31
  · exact no_three_on_half hw 0 h10 h20 h30 hdisj0_12 hdisj0_13 hdisj0_23
  · exact aux_contra c1 c2 c3 P1 P2 P3 d1 d2 d3 hnot_span h10 h20 hdisj0_12 hdisj0_13 hdisj0_23 hdisj1_13 hdisj1_23
  · exact aux_contra c1 c3 c2 P1 P3 P2 d1 d3 d2
      (fun e1 e2 e3 h => by convert hnot_span e1 e3 e2 (by tauto) using 1; abel)
      h10 h30 hdisj0_13 hdisj0_12 (fun x hx => by rw [mul_comm]; exact hdisj0_23 x hx)
      hdisj1_12 (fun x hx => by rw [mul_comm]; exact hdisj1_23 x hx)
  · exact aux_contra1 c2 c3 c1 P2 P3 P1 d2 d3 d1
      (fun e1 e2 e3 h => by convert hnot_span e3 e1 e2 (by tauto) using 1; abel)
      h21 h31 hdisj1_23 (fun x hx => by rw [mul_comm]; exact hdisj1_12 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj1_13 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj0_12 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj0_13 x hx)
  · exact aux_contra c2 c3 c1 P2 P3 P1 d2 d3 d1
      (fun e1 e2 e3 h => by convert hnot_span e3 e1 e2 (by tauto) using 1; abel)
      h20 h30 hdisj0_23 (fun x hx => by rw [mul_comm]; exact hdisj0_12 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj0_13 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj1_12 x hx)
      (fun x hx => by rw [mul_comm]; exact hdisj1_13 x hx)
  · exact aux_contra1 c1 c3 c2 P1 P3 P2 d1 d3 d2
      (fun e1 e2 e3 h => by convert hnot_span e1 e3 e2 (by tauto) using 1; abel)
      h11 h31 hdisj1_13 hdisj1_12 (fun x hx => by rw [mul_comm]; exact hdisj1_23 x hx)
      hdisj0_12 (fun x hx => by rw [mul_comm]; exact hdisj0_23 x hx)
  · exact aux_contra1 c1 c2 c3 P1 P2 P3 d1 d2 d3 hnot_span h11 h21 hdisj1_12 hdisj1_13 hdisj1_23 hdisj0_13 hdisj0_23
  · exact no_three_on_half hw 1 h11 h21 h31 hdisj1_12 hdisj1_13 hdisj1_23

lemma sub_eq_of_inf_finrank {n : ℕ} {A B : Submodule F (Vec n)}
    (hA : Module.finrank F A = 2) (hB : Module.finrank F B = 2)
    (hinf : Module.finrank F ↥(A ⊓ B) = 2) : A = B := by
  have e1 : A ⊓ B = A := Submodule.eq_of_le_of_finrank_eq inf_le_left (hinf.trans hA.symm)
  have e2 : A ⊓ B = B := Submodule.eq_of_le_of_finrank_eq inf_le_right (hinf.trans hB.symm)
  exact e1.symm.trans e2

lemma three_planes_common {n : ℕ} {Q1 Q2 Q3 : Submodule F (Vec n)}
    (h1 : Module.finrank F Q1 = 2) (h2 : Module.finrank F Q2 = 2) (h3 : Module.finrank F Q3 = 2)
    (h12 : Q1 ⊓ Q2 ≠ ⊥) (h13 : Q1 ⊓ Q3 ≠ ⊥) (h23 : Q2 ⊓ Q3 ≠ ⊥)
    (hdim : 4 ≤ Module.finrank F ↥(Q1 ⊔ Q2 ⊔ Q3)) :
    ∃ w c1 c2 c3 : Vec n, LinearIndependent F (![w, c1, c2, c3] : Fin 4 → Vec n) ∧
      Q1 = Submodule.span F ({w, c1} : Set (Vec n)) ∧
      Q2 = Submodule.span F ({w, c2} : Set (Vec n)) ∧
      Q3 = Submodule.span F ({w, c3} : Set (Vec n)) := by
  have h12_ne : Q1 ≠ Q2 := by
    intro heq; subst heq
    have hle : Module.finrank F ↥(Q1 ⊔ Q1 ⊔ Q3) ≤ 3 := by
      rw [sup_idem]
      have hform := Submodule.finrank_sup_add_finrank_inf_eq Q1 Q3
      have hpos : 1 ≤ Module.finrank F ↥(Q1 ⊓ Q3) := Nat.pos_of_ne_zero (by
        intro hz; exact h13 (Submodule.finrank_eq_zero.1 hz))
      omega
    omega
  have h12_dim : Module.finrank F ↥(Q1 ⊓ Q2) = 1 := by
    have hpos : 1 ≤ Module.finrank F ↥(Q1 ⊓ Q2) := Nat.pos_of_ne_zero (by
      intro hz; exact h12 (Submodule.finrank_eq_zero.1 hz))
    have hle : Module.finrank F ↥(Q1 ⊓ Q2) ≤ 2 := le_trans (Submodule.finrank_mono inf_le_left) (le_of_eq h1)
    have hne2 : Module.finrank F ↥(Q1 ⊓ Q2) ≠ 2 := fun h2' => h12_ne (sub_eq_of_inf_finrank h1 h2 h2')
    omega
  have h12_sup : Module.finrank F ↥(Q1 ⊔ Q2) = 3 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq Q1 Q2
    omega
  have h3_not_le : ¬ Q3 ≤ Q1 ⊔ Q2 := by
    intro hle
    have : Q1 ⊔ Q2 ⊔ Q3 = Q1 ⊔ Q2 := sup_eq_left.2 hle
    rw [this, h12_sup] at hdim; omega
  have h3_inf_le : Module.finrank F ↥((Q1 ⊔ Q2) ⊓ Q3) ≤ 1 := by
    have hle : Module.finrank F ↥((Q1 ⊔ Q2) ⊓ Q3) ≤ 2 := le_trans (Submodule.finrank_mono inf_le_right) (le_of_eq h3)
    have hne2 : Module.finrank F ↥((Q1 ⊔ Q2) ⊓ Q3) ≠ 2 := by
      intro h2'
      have e : (Q1 ⊔ Q2) ⊓ Q3 = Q3 := Submodule.eq_of_le_of_finrank_eq inf_le_right (h2'.trans h3.symm)
      exact h3_not_le (e ▸ inf_le_left)
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h13
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h23
  have hu' : u ∈ (Q1 ⊔ Q2) ⊓ Q3 := ⟨Submodule.mem_sup_left hu.1, hu.2⟩
  have hv' : v ∈ (Q1 ⊔ Q2) ⊓ Q3 := ⟨Submodule.mem_sup_right hv.1, hv.2⟩
  have huv : u = v := by
    by_contra hne
    have hli : LinearIndependent F (![u, v] : Fin 2 → Vec n) := linearIndependent_pair hu0 hv0 hne
    have hsp : Submodule.span F ({u, v} : Set (Vec n)) ≤ (Q1 ⊔ Q2) ⊓ Q3 := by
      rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
    have h2' := Submodule.finrank_mono hsp
    rw [span_pair_finrank hli] at h2'
    omega
  subst huv
  have hu1 : u ∈ Q1 := hu.1
  have hu2 : u ∈ Q2 := hv.1
  have hu3 : u ∈ Q3 := hu.2
  have pick : ∀ Q : Submodule F (Vec n), Module.finrank F Q = 2 → u ∈ Q →
      ∃ c ∈ Q, c ≠ 0 ∧ c ≠ u ∧ Q = Submodule.span F ({u, c} : Set (Vec n)) := by
    intro Q hQ huQ
    have hne : Submodule.span F ({u} : Set (Vec n)) ≠ Q := by
      intro heq
      have := finrank_span_singleton (K := F) hu0
      rw [heq, hQ] at this; omega
    have hlt : Submodule.span F ({u} : Set (Vec n)) < Q :=
      lt_of_le_of_ne (Submodule.span_le.2 (Set.singleton_subset_iff.2 huQ)) hne
    obtain ⟨c, hcQ, hc_not⟩ := IsConcreteLE.exists_of_lt hlt
    have hc0 : c ≠ 0 := fun h => hc_not (h ▸ Submodule.zero_mem _)
    have hcu : c ≠ u := fun h => hc_not (h ▸ Submodule.subset_span rfl)
    have hli := linearIndependent_pair hu0 hc0 hcu.symm
    have hsp : Submodule.span F ({u, c} : Set (Vec n)) = Q := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]; rintro x (rfl | rfl) <;> assumption
      · rw [span_pair_finrank hli, hQ]
    exact ⟨c, hcQ, hc0, hcu, hsp.symm⟩
  obtain ⟨c1, _, _, _, hP1⟩ := pick Q1 h1 hu1
  obtain ⟨c2, _, _, _, hP2⟩ := pick Q2 h2 hu2
  obtain ⟨c3, _, _, _, hP3⟩ := pick Q3 h3 hu3
  refine ⟨u, c1, c2, c3, ?_, hP1, hP2, hP3⟩
  have hsup_eq : Q1 ⊔ Q2 ⊔ Q3 = Submodule.span F (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n)) := by
    rw [hP1, hP2, hP3, ← Submodule.span_union, ← Submodule.span_union]
    congr 1; ext x
    constructor
    · rintro ((h | h) | h)
      · rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨1, rfl⟩
      · rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨2, rfl⟩
      · rcases h with rfl | rfl; exact ⟨0, rfl⟩; exact ⟨3, rfl⟩
    · rintro ⟨k, rfl⟩
      fin_cases k <;> simp
  rw [hsup_eq] at hdim
  have hle4 : Module.finrank F ↥(Submodule.span F (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n))) ≤ 4 := by
    have h1 := finrank_span_le_card (R := F) (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n))
    have h2 : (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n)).toFinset.card ≤ 4 := by
      rw [Set.toFinset_range]
      exact le_trans Finset.card_image_le (by simp)
    simpa [Set.toFinset_card] using le_trans h1 h2
  have hcard : Module.finrank F ↥(Submodule.span F (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n))) = 4 :=
    le_antisymm hle4 hdim
  rw [linearIndependent_iff_card_eq_finrank_span]
  change Fintype.card (Fin 4) = Module.finrank F ↥(Submodule.span F (Set.range (![u, c1, c2, c3] : Fin 4 → Vec n)))
  simpa using hcard.symm

set_option maxHeartbeats 800000 in
lemma forward_dir {n m : ℕ} (a b : Fin m → Vec n)
    (hex : ∃ (P : Fin m → Vec n) (d : Fin m → F), ∀ x : Vec n,
      (Finset.univ.filter (fun i : Fin m => dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ 1) :
    let live := (Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    let U := Submodule.span F (↑(live.image a ∪ live.image b) : Set (Vec n))
    live.card ≤ 4 ∧ Module.finrank F U ≤ 3 ∧
      (live.card = 4 → ∀ x y : Vec n, (∑ i ∈ live,
        (dotProduct (a i) x * dotProduct (b i) y + dotProduct (a i) y * dotProduct (b i) x)) = 0) := by
  intro live U
  obtain ⟨P, d, hP⟩ := hex
  let S : Fin m → Finset (Vec n) := fun i =>
    Finset.univ.filter (fun x : Vec n => dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)
  have hdisj : ∀ i ∈ live, ∀ j ∈ live, i ≠ j → Disjoint (S i) (S j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hsub : ({i, j} : Finset (Fin m)) ⊆ Finset.univ.filter (fun k =>
        dotProduct (P k) x + d k ≠ dotProduct (a k) x * dotProduct (b k) x) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · simpa [S] using hxi
      · simpa [S] using hxj
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hij] at hc
    have := hP x; omega
  have hdisj_mul : ∀ i ∈ live, ∀ j ∈ live, i ≠ j → ∀ x : Vec n,
      (dotProduct (a i) x * dotProduct (b i) x + dotProduct (P i) x + d i) *
      (dotProduct (a j) x * dotProduct (b j) x + dotProduct (P j) x + d j) = 0 := by
    intro i hi j hj hij x
    by_contra hne
    have h1 : dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x := by
      intro heq; apply hne
      have : dotProduct (a i) x * dotProduct (b i) x + dotProduct (P i) x + d i = 0 := by
        rw [add_assoc, heq, z2_add_self]
      rw [this, zero_mul]
    have h2 : dotProduct (P j) x + d j ≠ dotProduct (a j) x * dotProduct (b j) x := by
      intro heq; apply hne
      have : dotProduct (a j) x * dotProduct (b j) x + dotProduct (P j) x + d j = 0 := by
        rw [add_assoc, heq, z2_add_self]
      rw [this, mul_zero]
    exact Finset.disjoint_left.1 (hdisj i hi j hj hij) (by simpa [S] using h1) (by simpa [S] using h2)
  have hsum_le : ∑ i ∈ live, (S i).card ≤ 2 ^ n := by
    rw [← Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij)]
    calc (live.biUnion S).card ≤ (Finset.univ : Finset (Vec n)).card := Finset.card_le_univ _
      _ = 2 ^ n := by simp [Fintype.card_pi, ZMod.card]
  have hge_each : ∀ i ∈ live, 2 ^ n ≤ 4 * (S i).card := by
    intro i hi
    simp only [live, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact err_card_ge hi.1 hi.2.1 hi.2.2
  have hcard_le : live.card ≤ 4 := by
    have h1 : live.card * 2 ^ n ≤ 4 * ∑ i ∈ live, (S i).card := by
      calc live.card * 2 ^ n = ∑ _i ∈ live, 2 ^ n := by simp
        _ ≤ ∑ i ∈ live, 4 * (S i).card := Finset.sum_le_sum hge_each
        _ = 4 * ∑ i ∈ live, (S i).card := by rw [Finset.mul_sum]
    have h2 : live.card * 2 ^ n ≤ 4 * 2 ^ n := le_trans h1 (Nat.mul_le_mul_left 4 hsum_le)
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  refine ⟨hcard_le, ?_, ?_⟩
  · by_contra hgt
    push Not at hgt
    let Q : Fin m → Submodule F (Vec n) := fun i => Submodule.span F ({a i, b i} : Set (Vec n))
    have hU_eq : U = live.sup Q := by
      simp only [U]
      apply le_antisymm
      · rw [Submodule.span_le]
        intro v hv
        simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image] at hv
        rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
        · exact Finset.le_sup (f := Q) hi (Submodule.subset_span (by simp))
        · exact Finset.le_sup (f := Q) hi (Submodule.subset_span (by simp))
      · rw [Finset.sup_le_iff]
        intro i hi
        rw [Submodule.span_le]
        rintro v (rfl | rfl)
        · exact Submodule.subset_span (by simp; left; exact ⟨i, hi, rfl⟩)
        · exact Submodule.subset_span (by simp; right; exact ⟨i, hi, rfl⟩)
    have hQ2 : ∀ i ∈ live, Module.finrank F (Q i) = 2 := by
      intro i hi
      simp only [live, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact span_pair_finrank (linearIndependent_pair hi.1 hi.2.1 hi.2.2)
    have hQ_inter : ∀ i ∈ live, ∀ j ∈ live, i ≠ j → Q i ⊓ Q j ≠ ⊥ := by
      intro i hi j hj hij
      have hi' : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i := (Finset.mem_filter.1 hi).2
      have hj' : a j ≠ 0 ∧ b j ≠ 0 ∧ a j ≠ b j := (Finset.mem_filter.1 hj).2
      exact plane_inter_ne_bot (linearIndependent_pair hi'.1 hi'.2.1 hi'.2.2)
        (linearIndependent_pair hj'.1 hj'.2.1 hj'.2.2)
        (planes_not_disjoint (hdisj_mul i hi j hj hij))
    have hex3 : ∃ i1 ∈ live, ∃ i2 ∈ live, ∃ i3 ∈ live, 4 ≤ Module.finrank F ↥(Q i1 ⊔ Q i2 ⊔ Q i3) := by
      have hsub_le : ∀ s : Finset (Fin m), s ⊆ live → s.card ≤ 2 → Module.finrank F ↥(s.sup Q) ≤ 3 := by
        intro s hs hsc
        interval_cases h : s.card
        · rw [Finset.card_eq_zero] at h; subst h; rw [Finset.sup_empty]; simp
        · rw [Finset.card_eq_one] at h; obtain ⟨x, rfl⟩ := h
          rw [Finset.sup_singleton, hQ2 x (hs (by simp))]; omega
        · rw [Finset.card_eq_two] at h; obtain ⟨x, y, hxy, rfl⟩ := h
          rw [Finset.sup_insert, Finset.sup_singleton]
          have hform := Submodule.finrank_sup_add_finrank_inf_eq (Q x) (Q y)
          have hpos : 1 ≤ Module.finrank F ↥(Q x ⊓ Q y) := Nat.pos_of_ne_zero (by
            intro hz; exact hQ_inter x (hs (by simp)) y (hs (by simp)) hxy (Submodule.finrank_eq_zero.1 hz))
          rw [hQ2 x (hs (by simp)), hQ2 y (hs (by simp))] at hform; omega
      have hcard_ge3 : 3 ≤ live.card := by
        by_contra hlt
        have := hsub_le live Finset.Subset.rfl (by omega)
        rw [← hU_eq] at this; omega
      have hcase3 : ∀ s : Finset (Fin m), s ⊆ live → s.card = 3 → 4 ≤ Module.finrank F ↥(s.sup Q) →
          ∃ i1 ∈ live, ∃ i2 ∈ live, ∃ i3 ∈ live, 4 ≤ Module.finrank F ↥(Q i1 ⊔ Q i2 ⊔ Q i3) := by
        intro s hs hsc hdim
        rw [Finset.card_eq_three] at hsc
        obtain ⟨i1, i2, i3, _, _, _, rfl⟩ := hsc
        refine ⟨i1, hs (by simp), i2, hs (by simp), i3, hs (by simp), ?_⟩
        rw [Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton, ← sup_assoc] at hdim
        exact hdim
      rcases Nat.eq_or_lt_of_le hcard_ge3 with h3 | h4
      · exact hcase3 live Finset.Subset.rfl h3.symm (hU_eq ▸ hgt)
      · have hc4 : live.card = 4 := by omega
        obtain ⟨i1, hi1⟩ := Finset.card_pos.1 (by omega : 0 < live.card)
        let s3 := live.erase i1
        have hs3c : s3.card = 3 := by rw [Finset.card_erase_of_mem hi1, hc4]
        by_cases hdim3 : 4 ≤ Module.finrank F ↥(s3.sup Q)
        · exact hcase3 s3 (Finset.erase_subset _ _) hs3c hdim3
        · rw [Finset.card_eq_three] at hs3c
          obtain ⟨i2, i3, i4, h23, h24, h34, hs3eq⟩ := hs3c
          have hlive_eq : live = {i1, i2, i3, i4} := by
            rw [← Finset.insert_erase hi1]; change insert i1 s3 = _; rw [hs3eq]
          have hmem2 : i2 ∈ live := by rw [hlive_eq]; simp
          have hmem3 : i3 ∈ live := by rw [hlive_eq]; simp
          have hmem4 : i4 ∈ live := by rw [hlive_eq]; simp
          have hsup_all : U = Q i1 ⊔ (Q i2 ⊔ Q i3 ⊔ Q i4) := by
            rw [hU_eq, hlive_eq]; simp [Finset.sup_insert, Finset.sup_singleton, sup_assoc]
          by_cases e23 : Q i2 = Q i3
          · refine ⟨i1, hi1, i2, hmem2, i4, hmem4, ?_⟩
            rw [hsup_all, ← e23, sup_idem, ← sup_assoc] at hgt
            omega
          · have h23_dim : Module.finrank F ↥(Q i2 ⊔ Q i3) = 3 := by
              have hform := Submodule.finrank_sup_add_finrank_inf_eq (Q i2) (Q i3)
              have hpos : 1 ≤ Module.finrank F ↥(Q i2 ⊓ Q i3) := Nat.pos_of_ne_zero (by
                intro hz; exact hQ_inter i2 hmem2 i3 hmem3 h23 (Submodule.finrank_eq_zero.1 hz))
              have hne2 : Module.finrank F ↥(Q i2 ⊓ Q i3) ≠ 2 := fun h2' =>
                e23 (sub_eq_of_inf_finrank (hQ2 i2 hmem2) (hQ2 i3 hmem3) h2')
              have hle2 : Module.finrank F ↥(Q i2 ⊓ Q i3) ≤ 2 :=
                le_trans (Submodule.finrank_mono inf_le_left) (le_of_eq (hQ2 i2 hmem2))
              rw [hQ2 i2 hmem2, hQ2 i3 hmem3] at hform; omega
            have hle3 : Q i2 ⊔ Q i3 ≤ s3.sup Q := by
              rw [hs3eq]; simp only [Finset.sup_insert, Finset.sup_singleton]
              exact sup_le le_sup_left (le_trans le_sup_left le_sup_right)
            have h3dim : Module.finrank F ↥(s3.sup Q) = 3 := by
              have hge := Submodule.finrank_mono hle3; omega
            have h3eq : Q i2 ⊔ Q i3 = s3.sup Q :=
              Submodule.eq_of_le_of_finrank_eq hle3 (h23_dim.trans h3dim.symm)
            refine ⟨i1, hi1, i2, hmem2, i3, hmem3, ?_⟩
            have hU1 : U = Q i1 ⊔ s3.sup Q := by
              rw [hU_eq, ← Finset.insert_erase hi1, Finset.sup_insert]
            rw [hU1, ← h3eq, ← sup_assoc] at hgt
            omega
    obtain ⟨i1, hi1, i2, hi2, i3, hi3, hdim⟩ := hex3
    have h12ne : i1 ≠ i2 := by
      rintro rfl
      have hform := Submodule.finrank_sup_add_finrank_inf_eq (Q i1) (Q i3)
      by_cases h13 : i1 = i3
      · subst h13; rw [sup_idem, sup_idem, hQ2 i1 hi1] at hdim; omega
      · have hpos : 1 ≤ Module.finrank F ↥(Q i1 ⊓ Q i3) := Nat.pos_of_ne_zero (by
          intro hz; exact hQ_inter i1 hi1 i3 hi3 h13 (Submodule.finrank_eq_zero.1 hz))
        rw [sup_idem] at hdim; rw [hQ2 i1 hi1, hQ2 i3 hi3] at hform; omega
    have h13ne : i1 ≠ i3 := by
      rintro rfl
      have hform := Submodule.finrank_sup_add_finrank_inf_eq (Q i1) (Q i2)
      have hpos : 1 ≤ Module.finrank F ↥(Q i1 ⊓ Q i2) := Nat.pos_of_ne_zero (by
        intro hz; exact hQ_inter i1 hi1 i2 hi2 h12ne (Submodule.finrank_eq_zero.1 hz))
      have : Q i1 ⊔ Q i2 ⊔ Q i1 = Q i1 ⊔ Q i2 := by rw [sup_comm (Q i1 ⊔ Q i2), ← sup_assoc, sup_idem]
      rw [this] at hdim; rw [hQ2 i1 hi1, hQ2 i2 hi2] at hform; omega
    have h23ne : i2 ≠ i3 := by
      rintro rfl
      have hform := Submodule.finrank_sup_add_finrank_inf_eq (Q i1) (Q i2)
      have hpos : 1 ≤ Module.finrank F ↥(Q i1 ⊓ Q i2) := Nat.pos_of_ne_zero (by
        intro hz; exact hQ_inter i1 hi1 i2 hi2 h12ne (Submodule.finrank_eq_zero.1 hz))
      rw [sup_assoc, sup_idem] at hdim; rw [hQ2 i1 hi1, hQ2 i2 hi2] at hform; omega
    obtain ⟨w, c1, c2, c3, hli, hsp1, hsp2, hsp3⟩ := three_planes_common
      (hQ2 i1 hi1) (hQ2 i2 hi2) (hQ2 i3 hi3)
      (hQ_inter i1 hi1 i2 hi2 h12ne) (hQ_inter i1 hi1 i3 hi3 h13ne) (hQ_inter i2 hi2 i3 hi3 h23ne) hdim
    have hlive1 := (Finset.mem_filter.1 hi1).2
    have hlive2 := (Finset.mem_filter.1 hi2).2
    have hlive3 := (Finset.mem_filter.1 hi3).2
    obtain ⟨r1, hr1⟩ := span_pair_basis_quad hlive1.1 hlive1.2.1 hlive1.2.2 hsp1
    obtain ⟨r2, hr2⟩ := span_pair_basis_quad hlive2.1 hlive2.2.1 hlive2.2.2 hsp2
    obtain ⟨r3, hr3⟩ := span_pair_basis_quad hlive3.1 hlive3.2.1 hlive3.2.2 hsp3
    refine no_three_common hli (P1 := r1 + P i1) (P2 := r2 + P i2) (P3 := r3 + P i3)
      (d1 := d i1) (d2 := d i2) (d3 := d i3) ?_ ?_ ?_
    · intro x; have := hdisj_mul i1 hi1 i2 hi2 h12ne x
      simpa [hr1 x, hr2 x, add_dotProduct, add_assoc] using this
    · intro x; have := hdisj_mul i1 hi1 i3 hi3 h13ne x
      simpa [hr1 x, hr3 x, add_dotProduct, add_assoc] using this
    · intro x; have := hdisj_mul i2 hi2 i3 hi3 h23ne x
      simpa [hr2 x, hr3 x, add_dotProduct, add_assoc] using this
  · intro hc4 x y
    have hsum_eq : ∑ i ∈ live, (S i).card = 2 ^ n := by
      have h1 : 4 * 2 ^ n ≤ 4 * ∑ i ∈ live, (S i).card := by
        calc 4 * 2 ^ n = ∑ _i ∈ live, 2 ^ n := by simp [hc4]
          _ ≤ ∑ i ∈ live, 4 * (S i).card := Finset.sum_le_sum hge_each
          _ = 4 * ∑ i ∈ live, (S i).card := by rw [Finset.mul_sum]
      omega
    have hunion : live.biUnion S = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_biUnion (fun i hi j hj hij => hdisj i hi j hj hij), hsum_eq]
      simp [Fintype.card_pi, ZMod.card]
    let E : Fin m → Vec n → F := fun i z => dotProduct (a i) z * dotProduct (b i) z + dotProduct (P i) z + d i
    have hE_sum : ∀ z : Vec n, ∑ i ∈ live, E i z = 1 := by
      intro z
      have hz : z ∈ live.biUnion S := by rw [hunion]; exact Finset.mem_univ z
      rw [Finset.mem_biUnion] at hz
      obtain ⟨i0, hi0, hzi0⟩ := hz
      have hval : ∀ i ∈ live, E i z = if i = i0 then 1 else 0 := by
        intro i hi
        split_ifs with heq
        · subst heq
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzi0
          have := (z2_ne_iff_add_eq_one _ _).1 hzi0
          simpa [E, add_comm, add_left_comm, add_assoc] using this
        · have hnot : z ∉ S i := fun h => Finset.disjoint_left.1 (hdisj i hi i0 hi0 heq) h hzi0
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
          change dotProduct (a i) z * dotProduct (b i) z + dotProduct (P i) z + d i = 0
          rw [add_assoc, hnot, z2_add_self]
      rw [Finset.sum_congr rfl hval]
      simp [hi0]
    have hpolar_eq : ∀ i : Fin m,
        E i 0 + E i x + E i y + E i (x + y) =
          dotProduct (a i) x * dotProduct (b i) y + dotProduct (a i) y * dotProduct (b i) x := by
      intro i
      simp only [E, dotProduct_zero, dotProduct_add, zero_mul, zero_add]
      linear_combination
        z2_add_self (dotProduct (a i) x * dotProduct (b i) x) +
        z2_add_self (dotProduct (a i) y * dotProduct (b i) y) +
        z2_add_self (dotProduct (P i) x) +
        z2_add_self (dotProduct (P i) y) +
        z2_add_self (d i) + z2_add_self (d i)
    calc ∑ i ∈ live, (dotProduct (a i) x * dotProduct (b i) y + dotProduct (a i) y * dotProduct (b i) x)
        = ∑ i ∈ live, (E i 0 + E i x + E i y + E i (x + y)) :=
          Finset.sum_congr rfl fun i _ => (hpolar_eq i).symm
      _ = (∑ i ∈ live, E i 0) + (∑ i ∈ live, E i x) + (∑ i ∈ live, E i y) + (∑ i ∈ live, E i (x + y)) := by
          simp [Finset.sum_add_distrib]
      _ = 1 + 1 + 1 + 1 := by simp [hE_sum]
      _ = 0 := by decide

lemma dim2_point_err (α β p : Vec 2) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    ∃ (P' : Vec 2) (d : F), ∀ z : Vec 2,
      (dotProduct P' z + d ≠ dotProduct α z * dotProduct β z) ↔ z = p := by
  refine ⟨(dotProduct β p + 1) • α + (dotProduct α p + 1) • β,
    (dotProduct α p + 1) * (dotProduct β p + 1), fun z => ?_⟩
  have h : (dotProduct ((dotProduct β p + 1) • α + (dotProduct α p + 1) • β) z +
      (dotProduct α p + 1) * (dotProduct β p + 1) ≠ dotProduct α z * dotProduct β z) ↔
      (dotProduct α z = dotProduct α p ∧ dotProduct β z = dotProduct β p) := by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    generalize dotProduct α z = az
    generalize dotProduct β z = bz
    generalize dotProduct α p = ap
    generalize dotProduct β p = bp
    revert az bz ap bp; decide
  rw [h]
  constructor
  · intro ⟨h1, h2⟩
    have hsub : ∀ v : Vec 2, dotProduct α v = 0 → dotProduct β v = 0 → v = 0 := by
      intro v hv1 hv2
      have h1' : α 0 * v 0 + α 1 * v 1 = 0 := by simpa [dotProduct, Fin.sum_univ_two] using hv1
      have h2' : β 0 * v 0 + β 1 * v 1 = 0 := by simpa [dotProduct, Fin.sum_univ_two] using hv2
      rcases z2_eq_zero_or_one (v 0) with hv0 | hv0 <;> rcases z2_eq_zero_or_one (v 1) with hv1' | hv1'
      · funext k; fin_cases k <;> [exact hv0; exact hv1']
      · exfalso
        rw [hv0, hv1', mul_zero, zero_add, mul_one] at h1' h2'
        have ha0 : α 0 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hα (funext fun k => by fin_cases k <;> [exact h; exact h1'])
        have hb0 : β 0 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hβ (funext fun k => by fin_cases k <;> [exact h; exact h2'])
        exact hαβ (funext fun k => by fin_cases k <;> [exact ha0.trans hb0.symm; exact h1'.trans h2'.symm])
      · exfalso
        rw [hv0, hv1', mul_zero, add_zero, mul_one] at h1' h2'
        have ha1 : α 1 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hα (funext fun k => by fin_cases k <;> [exact h1'; exact h])
        have hb1 : β 1 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hβ (funext fun k => by fin_cases k <;> [exact h2'; exact h])
        exact hαβ (funext fun k => by fin_cases k <;> [exact h1'.trans h2'.symm; exact ha1.trans hb1.symm])
      · exfalso
        rw [hv0, hv1', mul_one, mul_one] at h1' h2'
        have hae : α 0 = α 1 := z2_eq_of_add_eq_zero h1'
        have hbe : β 0 = β 1 := z2_eq_of_add_eq_zero h2'
        have ha0 : α 0 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hα (funext fun k => by fin_cases k <;> [exact h; exact hae.symm.trans h])
        have hb0 : β 0 = 1 := (z2_eq_zero_or_one _).resolve_left fun h =>
          hβ (funext fun k => by fin_cases k <;> [exact h; exact hbe.symm.trans h])
        exact hαβ (funext fun k => by fin_cases k <;> [exact ha0.trans hb0.symm; exact hae.symm.trans (ha0.trans (hb0.symm.trans hbe))])
    apply vec_eq_of_add_eq_zero
    apply hsub (z + p)
    · rw [dotProduct_add, h1, z2_add_self]
    · rw [dotProduct_add, h2, z2_add_self]
  · rintro rfl; exact ⟨rfl, rfl⟩

def cross3 (α β : Vec 3) : Vec 3 :=
  ![α 1 * β 2 + α 2 * β 1, α 2 * β 0 + α 0 * β 2, α 0 * β 1 + α 1 * β 0]

lemma cross3_ne_zero (α β : Vec 3) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    cross3 α β ≠ 0 := by
  revert α β; decide

lemma dim3_edge_err_aux : ∀ (α β v : Vec 3), α ≠ 0 → β ≠ 0 → α ≠ β →
    ∀ z : Vec 3,
      (dotProduct ((dotProduct β v + 1) • α + (dotProduct α v + 1) • β) z +
        (dotProduct α v + 1) * (dotProduct β v + 1) ≠ dotProduct α z * dotProduct β z) ↔
        (z = v ∨ z = v + cross3 α β) := by
  decide

lemma dim3_edge_err (α β v : Vec 3) (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : α ≠ β) :
    ∃ (P' : Vec 3) (d : F), ∀ z : Vec 3,
      (dotProduct P' z + d ≠ dotProduct α z * dotProduct β z) ↔ (z = v ∨ z = v + cross3 α β) :=
  ⟨(dotProduct β v + 1) • α + (dotProduct α v + 1) • β,
    (dotProduct α v + 1) * (dotProduct β v + 1), dim3_edge_err_aux α β v hα hβ hαβ⟩

lemma cross3_polar_coord (α β : Vec 3) :
    (dotProduct α ![0, 1, 0] * dotProduct β ![0, 0, 1] + dotProduct α ![0, 0, 1] * dotProduct β ![0, 1, 0] = cross3 α β 0) ∧
    (dotProduct α ![0, 0, 1] * dotProduct β ![1, 0, 0] + dotProduct α ![1, 0, 0] * dotProduct β ![0, 0, 1] = cross3 α β 1) ∧
    (dotProduct α ![1, 0, 0] * dotProduct β ![0, 1, 0] + dotProduct α ![0, 1, 0] * dotProduct β ![1, 0, 0] = cross3 α β 2) := by
  revert α β; decide

def allVec3 : List (Vec 3) :=
  [![0,0,0], ![0,0,1], ![0,1,0], ![0,1,1], ![1,0,0], ![1,0,1], ![1,1,0], ![1,1,1]]

def edgeDisj (v1 e1 v2 e2 : Vec 3) : Bool :=
  decide (v1 ≠ v2 ∧ v1 ≠ v2 + e2 ∧ v1 + e1 ≠ v2 ∧ v1 + e1 ≠ v2 + e2)

def findPack4 (e1 e2 e3 e4 : Vec 3) : Vec 3 × Vec 3 × Vec 3 × Vec 3 :=
  let v1 : Vec 3 := 0
  let cand := allVec3.findSome? fun v2 =>
    if edgeDisj v1 e1 v2 e2 then
      allVec3.findSome? fun v3 =>
        if edgeDisj v1 e1 v3 e3 && edgeDisj v2 e2 v3 e3 then
          allVec3.findSome? fun v4 =>
            if edgeDisj v1 e1 v4 e4 && edgeDisj v2 e2 v4 e4 && edgeDisj v3 e3 v4 e4 then
              some (v1, v2, v3, v4)
            else none
        else none
    else none
  cand.getD (0, 0, 0, 0)

def pack4Ok (e1 e2 e3 : Vec 3) : Bool :=
  let e4 := e1 + e2 + e3
  let w := findPack4 e1 e2 e3 e4
  edgeDisj w.1 e1 w.2.1 e2 && edgeDisj w.1 e1 w.2.2.1 e3 && edgeDisj w.1 e1 w.2.2.2 e4 &&
  edgeDisj w.2.1 e2 w.2.2.1 e3 && edgeDisj w.2.1 e2 w.2.2.2 e4 && edgeDisj w.2.2.1 e3 w.2.2.2 e4

lemma mem_allVec3 (v : Vec 3) : v ∈ allVec3 := by
  have h : v = ![v 0, v 1, v 2] := by funext k; fin_cases k <;> rfl
  rw [h]
  generalize v 0 = a; generalize v 1 = b; generalize v 2 = c
  revert a b c; decide

lemma pack4_dim3_aux_bool : allVec3.all (fun e1 => allVec3.all (fun e2 => allVec3.all (fun e3 =>
    if e1 != 0 && e2 != 0 && e3 != 0 && e1 + e2 + e3 != 0 then pack4Ok e1 e2 e3 else true))) = true := by
  decide

lemma pack4_dim3_aux (e1 e2 e3 : Vec 3)
    (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (h3 : e3 ≠ 0) (h4 : e1 + e2 + e3 ≠ 0) :
    pack4Ok e1 e2 e3 = true := by
  have hb := List.all_eq_true.1 pack4_dim3_aux_bool e1 (mem_allVec3 e1)
  have hb2 := List.all_eq_true.1 hb e2 (mem_allVec3 e2)
  have hb3 := List.all_eq_true.1 hb2 e3 (mem_allVec3 e3)
  simpa [h1, h2, h3, h4] using hb3

lemma edgeDisj_spec {v1 e1 v2 e2 : Vec 3} (h : edgeDisj v1 e1 v2 e2 = true) (z : Vec 3) :
    ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v2 ∨ z = v2 + e2)) := by
  simp only [edgeDisj, decide_eq_true_eq] at h
  rintro ⟨rfl | rfl, h2 | h2⟩
  · exact h.1 h2
  · exact h.2.1 h2
  · exact h.2.2.1 h2
  · exact h.2.2.2 h2

lemma pack4_dim3 (e1 e2 e3 e4 : Vec 3)
    (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (h3 : e3 ≠ 0) (h4 : e4 ≠ 0)
    (hsum : e1 + e2 + e3 + e4 = 0) :
    ∃ v1 v2 v3 v4 : Vec 3,
      ∀ z : Vec 3,
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v2 ∨ z = v2 + e2)) ∧
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v3 ∨ z = v3 + e3)) ∧
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v4 ∨ z = v4 + e4)) ∧
        ¬ ((z = v2 ∨ z = v2 + e2) ∧ (z = v3 ∨ z = v3 + e3)) ∧
        ¬ ((z = v2 ∨ z = v2 + e2) ∧ (z = v4 ∨ z = v4 + e4)) ∧
        ¬ ((z = v3 ∨ z = v3 + e3) ∧ (z = v4 ∨ z = v4 + e4)) := by
  have he4 : e4 = e1 + e2 + e3 := (vec_eq_of_add_eq_zero hsum).symm
  subst he4
  have hok := pack4_dim3_aux e1 e2 e3 h1 h2 h3 h4
  simp only [pack4Ok, Bool.and_eq_true] at hok
  let w := findPack4 e1 e2 e3 (e1 + e2 + e3)
  exact ⟨w.1, w.2.1, w.2.2.1, w.2.2.2, fun z =>
    ⟨edgeDisj_spec hok.1.1.1.1.1 z, edgeDisj_spec hok.1.1.1.1.2 z, edgeDisj_spec hok.1.1.1.2 z,
     edgeDisj_spec hok.1.1.2 z, edgeDisj_spec hok.1.2 z, edgeDisj_spec hok.2 z⟩⟩

def findPack3 (e1 e2 e3 : Vec 3) : Vec 3 × Vec 3 × Vec 3 :=
  let v1 : Vec 3 := 0
  let cand := allVec3.findSome? fun v2 =>
    if edgeDisj v1 e1 v2 e2 then
      allVec3.findSome? fun v3 =>
        if edgeDisj v1 e1 v3 e3 && edgeDisj v2 e2 v3 e3 then
          some (v1, v2, v3)
        else none
    else none
  cand.getD (0, 0, 0)

lemma pack3_ne_dim3_aux : ∀ (e1 e2 e3 : Vec 3),
    e1 ≠ 0 → e2 ≠ 0 → e3 ≠ 0 → e1 + e2 + e3 ≠ 0 →
    let w := findPack3 e1 e2 e3
    ∀ z : Vec 3,
      ¬ ((z = w.1 ∨ z = w.1 + e1) ∧ (z = w.2.1 ∨ z = w.2.1 + e2)) ∧
      ¬ ((z = w.1 ∨ z = w.1 + e1) ∧ (z = w.2.2 ∨ z = w.2.2 + e3)) ∧
      ¬ ((z = w.2.1 ∨ z = w.2.1 + e2) ∧ (z = w.2.2 ∨ z = w.2.2 + e3)) := by
  decide

lemma pack3_ne_dim3 (e1 e2 e3 : Vec 3)
    (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (h3 : e3 ≠ 0) (hsum : e1 + e2 + e3 ≠ 0) :
    ∃ v1 v2 v3 : Vec 3,
      ∀ z : Vec 3,
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v2 ∨ z = v2 + e2)) ∧
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v3 ∨ z = v3 + e3)) ∧
        ¬ ((z = v2 ∨ z = v2 + e2) ∧ (z = v3 ∨ z = v3 + e3)) :=
  let w := findPack3 e1 e2 e3
  ⟨w.1, w.2.1, w.2.2, pack3_ne_dim3_aux e1 e2 e3 h1 h2 h3 hsum⟩

def findCanon3 (e1 e2 : Vec 3) : Vec 3 × Vec 3 × Vec 3 × Vec 3 × Vec 3 × F :=
  let e3 := e1 + e2
  let v1 : Vec 3 := 0
  let cand := allVec3.findSome? fun v2 =>
    if edgeDisj v1 e1 v2 e2 then
      allVec3.findSome? fun a3 =>
        allVec3.findSome? fun b3 =>
          if a3 ≠ 0 && b3 ≠ 0 && a3 ≠ b3 && decide (cross3 a3 b3 = e3) then
            allVec3.findSome? fun P3 =>
              ([0, 1] : List F).findSome? fun d3 =>
                if allVec3.all (fun z =>
                    !((z == v1 || z == v1 + e1) && decide (dotProduct P3 z + d3 ≠ dotProduct a3 z * dotProduct b3 z)) &&
                    !((z == v2 || z == v2 + e2) && decide (dotProduct P3 z + d3 ≠ dotProduct a3 z * dotProduct b3 z))) then
                  some (v1, v2, a3, b3, P3, d3)
                else none
          else none
    else none
  cand.getD (0, 0, 0, 0, 0, 0)

lemma pack3_eq_dim3_canon : ∀ e1' e2' : Vec 3, e1' ≠ 0 → e2' ≠ 0 → e1' ≠ e2' →
    let c := findCanon3 e1' e2'
    c.2.2.1 ≠ 0 ∧ c.2.2.2.1 ≠ 0 ∧ c.2.2.1 ≠ c.2.2.2.1 ∧ cross3 c.2.2.1 c.2.2.2.1 = e1' + e2' ∧
      ∀ z : Vec 3,
        ¬ ((z = c.1 ∨ z = c.1 + e1') ∧ (z = c.2.1 ∨ z = c.2.1 + e2')) ∧
        ¬ ((z = c.1 ∨ z = c.1 + e1') ∧ (dotProduct c.2.2.2.2.1 z + c.2.2.2.2.2 ≠ dotProduct c.2.2.1 z * dotProduct c.2.2.2.1 z)) ∧
        ¬ ((z = c.2.1 ∨ z = c.2.1 + e2') ∧ (dotProduct c.2.2.2.2.1 z + c.2.2.2.2.2 ≠ dotProduct c.2.2.1 z * dotProduct c.2.2.2.1 z)) := by
  decide

lemma pack3_eq_dim3 (e1 e2 : Vec 3) (α3 β3 : Vec 3)
    (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) (h12 : e1 ≠ e2)
    (hα3 : α3 ≠ 0) (hβ3 : β3 ≠ 0) (hαβ3 : α3 ≠ β3)
    (he3 : cross3 α3 β3 = e1 + e2) :
    ∃ (v1 v2 P3' : Vec 3) (d3 : F),
      ∀ z : Vec 3,
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v2 ∨ z = v2 + e2)) ∧
        ¬ ((z = v1 ∨ z = v1 + e1) ∧ (dotProduct P3' z + d3 ≠ dotProduct α3 z * dotProduct β3 z)) ∧
        ¬ ((z = v2 ∨ z = v2 + e2) ∧ (dotProduct P3' z + d3 ≠ dotProduct α3 z * dotProduct β3 z)) := by
  have hc := pack3_eq_dim3_canon e1 e2 h1 h2 h12
  let c := findCanon3 e1 e2
  have hsp : Submodule.span F ({α3, β3} : Set (Vec 3)) = Submodule.span F ({c.2.2.1, c.2.2.2.1} : Set (Vec 3)) := by
    have horth : ∀ (a b v : Vec 3), a ≠ 0 → b ≠ 0 → a ≠ b →
        (v ∈ Submodule.span F ({a, b} : Set (Vec 3)) ↔ dotProduct (cross3 a b) v = 0) := by
      intro a b v ha hb hab
      rw [Submodule.mem_span_pair]
      revert a b v ha hb hab; decide
    ext v
    rw [horth α3 β3 v hα3 hβ3 hαβ3, horth c.2.2.1 c.2.2.2.1 v hc.1 hc.2.1 hc.2.2.1, he3, hc.2.2.2.1]
  obtain ⟨r, hr⟩ := span_pair_basis_quad hα3 hβ3 hαβ3 hsp
  refine ⟨c.1, c.2.1, c.2.2.2.2.1 + r, c.2.2.2.2.2, fun z => ?_⟩
  have h := hc.2.2.2.2 z
  have heq : (dotProduct (c.2.2.2.2.1 + r) z + c.2.2.2.2.2 ≠ dotProduct α3 z * dotProduct β3 z) ↔
      (dotProduct c.2.2.2.2.1 z + c.2.2.2.2.2 ≠ dotProduct c.2.2.1 z * dotProduct c.2.2.2.1 z) := by
    rw [hr z, add_dotProduct]
    have h1 : dotProduct c.2.2.2.2.1 z + dotProduct r z + c.2.2.2.2.2 =
        (dotProduct c.2.2.2.2.1 z + c.2.2.2.2.2) + dotProduct r z := by ring
    rw [h1, ne_eq, ne_eq, z2_add_cancel_right]
  exact ⟨h.1, fun hp => h.2.1 ⟨hp.1, heq.1 hp.2⟩, fun hp => h.2.2 ⟨hp.1, heq.1 hp.2⟩⟩

def findPack2 (e1 e2 : Vec 3) : Vec 3 × Vec 3 :=
  let v1 : Vec 3 := 0
  let cand := allVec3.findSome? fun v2 => if edgeDisj v1 e1 v2 e2 then some (v1, v2) else none
  cand.getD (0, 0)

lemma pack2_dim3_aux : ∀ (e1 e2 : Vec 3), e1 ≠ 0 → e2 ≠ 0 →
    let w := findPack2 e1 e2
    ∀ z : Vec 3, ¬ ((z = w.1 ∨ z = w.1 + e1) ∧ (z = w.2 ∨ z = w.2 + e2)) := by
  decide

lemma pack2_dim3 (e1 e2 : Vec 3) (h1 : e1 ≠ 0) (h2 : e2 ≠ 0) :
    ∃ v1 v2 : Vec 3, ∀ z : Vec 3, ¬ ((z = v1 ∨ z = v1 + e1) ∧ (z = v2 ∨ z = v2 + e2)) :=
  let w := findPack2 e1 e2
  ⟨w.1, w.2, pack2_dim3_aux e1 e2 h1 h2⟩

lemma solve_on_small {r : ℕ} {m : ℕ} (hr : r ≤ 3) (live : Finset (Fin m))
    (α β : Fin m → Vec r)
    (hlive : ∀ i ∈ live, α i ≠ 0 ∧ β i ≠ 0 ∧ α i ≠ β i)
    (hcard : live.card ≤ 4)
    (hpolar : live.card = 4 → ∀ x y : Vec r,
      ∑ i ∈ live, (dotProduct (α i) x * dotProduct (β i) y + dotProduct (α i) y * dotProduct (β i) x) = 0) :
    ∃ (P' : Fin m → Vec r) (d : Fin m → F), ∀ z : Vec r,
      (live.filter (fun i => dotProduct (P' i) z + d i ≠ dotProduct (α i) z * dotProduct (β i) z)).card ≤ 1 := by
  have hpairwise : ∀ (P' : Fin m → Vec r) (d : Fin m → F),
      (∀ z : Vec r, ∀ i ∈ live, ∀ j ∈ live, i ≠ j →
        ¬ ((dotProduct (P' i) z + d i ≠ dotProduct (α i) z * dotProduct (β i) z) ∧
           (dotProduct (P' j) z + d j ≠ dotProduct (α j) z * dotProduct (β j) z))) →
      ∀ z : Vec r, (live.filter (fun i => dotProduct (P' i) z + d i ≠ dotProduct (α i) z * dotProduct (β i) z)).card ≤ 1 := by
    intro P' d hpw z
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter] at hi hj
    by_contra hij
    exact hpw z i hi.1 j hj.1 hij ⟨hi.2, hj.2⟩
  interval_cases r
  · refine ⟨0, 0, ?_⟩
    have hempty : live = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
      exact (hlive i hi).1 (Subsingleton.elim _ _)
    intro z; simp [hempty]
  · refine ⟨0, 0, ?_⟩
    have hempty : live = ∅ := by
      by_contra hne
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hne
      obtain ⟨ha, hb, hab⟩ := hlive i hi
      have h1 : α i 0 = 1 := (z2_eq_zero_or_one _).resolve_left (fun h => ha (funext fun k => by fin_cases k; exact h))
      have h2 : β i 0 = 1 := (z2_eq_zero_or_one _).resolve_left (fun h => hb (funext fun k => by fin_cases k; exact h))
      exact hab (funext fun k => by fin_cases k; exact h1.trans h2.symm)
    intro z; simp [hempty]
  · let pts : Fin 4 → Vec 2 := ![![0, 0], ![0, 1], ![1, 0], ![1, 1]]
    have hpts_inj : Function.Injective pts := by decide
    let e := live.equivFin
    have hpt : ∀ i : Fin m, ∃ (P' : Vec 2) (d : F),
        ∀ hi : i ∈ live, ∀ z : Vec 2,
          (dotProduct P' z + d ≠ dotProduct (α i) z * dotProduct (β i) z) ↔
            z = pts ⟨(e ⟨i, hi⟩).val, lt_of_lt_of_le (e ⟨i, hi⟩).isLt hcard⟩ := by
      intro i
      by_cases hi : i ∈ live
      · obtain ⟨ha, hb, hab⟩ := hlive i hi
        obtain ⟨P', d, h⟩ := dim2_point_err (α i) (β i) (pts ⟨(e ⟨i, hi⟩).val, lt_of_lt_of_le (e ⟨i, hi⟩).isLt hcard⟩) ha hb hab
        exact ⟨P', d, fun _ => h⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose P' d hPd using hpt
    refine ⟨P', d, hpairwise P' d fun z i hi j hj hij ⟨h1, h2⟩ => ?_⟩
    rw [hPd i hi z] at h1
    rw [hPd j hj z] at h2
    have heq := hpts_inj (h1.symm.trans h2)
    have hval : (e ⟨i, hi⟩).val = (e ⟨j, hj⟩).val := by
      have := congrArg (Fin.val : Fin 4 → ℕ) heq
      exact this
    have : (⟨i, hi⟩ : {x // x ∈ live}) = ⟨j, hj⟩ := e.injective (Fin.ext hval)
    exact hij (congrArg Subtype.val this)
  · interval_cases hc : live.card
    · rw [Finset.card_eq_zero] at hc; subst hc; exact ⟨0, 0, fun z => by simp⟩
    · rw [Finset.card_eq_one] at hc; obtain ⟨i1, rfl⟩ := hc
      exact ⟨0, 0, fun z => le_trans (Finset.card_filter_le _ _) (by simp)⟩
    · rw [Finset.card_eq_two] at hc; obtain ⟨i1, i2, h12, rfl⟩ := hc
      have h1 := hlive i1 (by simp); have h2 := hlive i2 (by simp)
      obtain ⟨v1, v2, hpack⟩ := pack2_dim3 (cross3 (α i1) (β i1)) (cross3 (α i2) (β i2))
        (cross3_ne_zero _ _ h1.1 h1.2.1 h1.2.2) (cross3_ne_zero _ _ h2.1 h2.2.1 h2.2.2)
      obtain ⟨P1, d1, hP1⟩ := dim3_edge_err (α i1) (β i1) v1 h1.1 h1.2.1 h1.2.2
      obtain ⟨P2, d2, hP2⟩ := dim3_edge_err (α i2) (β i2) v2 h2.1 h2.2.1 h2.2.2
      let P' : Fin m → Vec 3 := fun i => if i = i1 then P1 else if i = i2 then P2 else 0
      let d : Fin m → F := fun i => if i = i1 then d1 else if i = i2 then d2 else 0
      refine ⟨P', d, hpairwise P' d fun z i hi j hj hij ⟨hzi, hzj⟩ => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact hij rfl
      · simp only [P', d, ite_true, ite_eq_right_iff, Ne.symm h12] at hzi hzj
        exact hpack z ⟨(hP1 z).1 hzi, (hP2 z).1 (by simpa [Ne.symm h12] using hzj)⟩
      · simp only [P', d, ite_true, ite_eq_right_iff, Ne.symm h12] at hzi hzj
        exact hpack z ⟨(hP1 z).1 hzj, (hP2 z).1 (by simpa [Ne.symm h12] using hzi)⟩
      · exact hij rfl
    · rw [Finset.card_eq_three] at hc; obtain ⟨i1, i2, i3, h12, h13, h23, rfl⟩ := hc
      have h1 := hlive i1 (by simp); have h2 := hlive i2 (by simp); have h3 := hlive i3 (by simp)
      let e1 := cross3 (α i1) (β i1); let e2 := cross3 (α i2) (β i2); let e3 := cross3 (α i3) (β i3)
      have he1 := cross3_ne_zero _ _ h1.1 h1.2.1 h1.2.2
      have he2 := cross3_ne_zero _ _ h2.1 h2.2.1 h2.2.2
      have he3 := cross3_ne_zero _ _ h3.1 h3.2.1 h3.2.2
      by_cases hsum : e1 + e2 + e3 = 0
      · have he12 : e1 ≠ e2 := by
          intro heq; rw [heq, vec_add_self, zero_add] at hsum; exact he3 hsum
        have he3eq : cross3 (α i3) (β i3) = e1 + e2 := (vec_eq_of_add_eq_zero hsum).symm
        obtain ⟨v1, v2, P3, d3, hpack⟩ := pack3_eq_dim3 e1 e2 (α i3) (β i3) he1 he2 he12 h3.1 h3.2.1 h3.2.2 he3eq
        obtain ⟨P1, d1, hP1⟩ := dim3_edge_err (α i1) (β i1) v1 h1.1 h1.2.1 h1.2.2
        obtain ⟨P2, d2, hP2⟩ := dim3_edge_err (α i2) (β i2) v2 h2.1 h2.2.1 h2.2.2
        let P' : Fin m → Vec 3 := fun i => if i = i1 then P1 else if i = i2 then P2 else if i = i3 then P3 else 0
        let d : Fin m → F := fun i => if i = i1 then d1 else if i = i2 then d2 else if i = i3 then d3 else 0
        have hP1v : P' i1 = P1 ∧ d i1 = d1 := ⟨by simp [P'], by simp [d]⟩
        have hP2v : P' i2 = P2 ∧ d i2 = d2 := ⟨by simp [P', Ne.symm h12], by simp [d, Ne.symm h12]⟩
        have hP3v : P' i3 = P3 ∧ d i3 = d3 := ⟨by simp [P', Ne.symm h13, Ne.symm h23], by simp [d, Ne.symm h13, Ne.symm h23]⟩
        refine ⟨P', d, hpairwise P' d fun z i hi j hj hij ⟨hzi, hzj⟩ => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
        · exact hij rfl
        · rw [hP1v.1, hP1v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
          exact (hpack z).1 ⟨(hP1 z).1 hzi, (hP2 z).1 hzj⟩
        · rw [hP1v.1, hP1v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
          exact (hpack z).2.1 ⟨(hP1 z).1 hzi, hzj⟩
        · rw [hP2v.1, hP2v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
          exact (hpack z).1 ⟨(hP1 z).1 hzj, (hP2 z).1 hzi⟩
        · exact hij rfl
        · rw [hP2v.1, hP2v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
          exact (hpack z).2.2 ⟨(hP2 z).1 hzi, hzj⟩
        · rw [hP3v.1, hP3v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
          exact (hpack z).2.1 ⟨(hP1 z).1 hzj, hzi⟩
        · rw [hP3v.1, hP3v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
          exact (hpack z).2.2 ⟨(hP2 z).1 hzj, hzi⟩
        · exact hij rfl
      · obtain ⟨v1, v2, v3, hpack⟩ := pack3_ne_dim3 e1 e2 e3 he1 he2 he3 hsum
        obtain ⟨P1, d1, hP1⟩ := dim3_edge_err (α i1) (β i1) v1 h1.1 h1.2.1 h1.2.2
        obtain ⟨P2, d2, hP2⟩ := dim3_edge_err (α i2) (β i2) v2 h2.1 h2.2.1 h2.2.2
        obtain ⟨P3, d3, hP3⟩ := dim3_edge_err (α i3) (β i3) v3 h3.1 h3.2.1 h3.2.2
        let P' : Fin m → Vec 3 := fun i => if i = i1 then P1 else if i = i2 then P2 else if i = i3 then P3 else 0
        let d : Fin m → F := fun i => if i = i1 then d1 else if i = i2 then d2 else if i = i3 then d3 else 0
        have hP1v : P' i1 = P1 ∧ d i1 = d1 := ⟨by simp [P'], by simp [d]⟩
        have hP2v : P' i2 = P2 ∧ d i2 = d2 := ⟨by simp [P', Ne.symm h12], by simp [d, Ne.symm h12]⟩
        have hP3v : P' i3 = P3 ∧ d i3 = d3 := ⟨by simp [P', Ne.symm h13, Ne.symm h23], by simp [d, Ne.symm h13, Ne.symm h23]⟩
        refine ⟨P', d, hpairwise P' d fun z i hi j hj hij ⟨hzi, hzj⟩ => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
        · exact hij rfl
        · rw [hP1v.1, hP1v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
          exact (hpack z).1 ⟨(hP1 z).1 hzi, (hP2 z).1 hzj⟩
        · rw [hP1v.1, hP1v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
          exact (hpack z).2.1 ⟨(hP1 z).1 hzi, (hP3 z).1 hzj⟩
        · rw [hP2v.1, hP2v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
          exact (hpack z).1 ⟨(hP1 z).1 hzj, (hP2 z).1 hzi⟩
        · exact hij rfl
        · rw [hP2v.1, hP2v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
          exact (hpack z).2.2 ⟨(hP2 z).1 hzi, (hP3 z).1 hzj⟩
        · rw [hP3v.1, hP3v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
          exact (hpack z).2.1 ⟨(hP1 z).1 hzj, (hP3 z).1 hzi⟩
        · rw [hP3v.1, hP3v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
          exact (hpack z).2.2 ⟨(hP2 z).1 hzj, (hP3 z).1 hzi⟩
        · exact hij rfl
    · have hpol := hpolar rfl
      obtain ⟨i1, hi1⟩ := Finset.card_pos.1 (by omega : 0 < live.card)
      have hc3 : (live.erase i1).card = 3 := by rw [Finset.card_erase_of_mem hi1, hc]
      rw [Finset.card_eq_three] at hc3
      obtain ⟨i2, i3, i4, h23, h24, h34, hs3⟩ := hc3
      have h12 : i1 ≠ i2 := fun h => (Finset.notMem_erase i1 live) (by rw [hs3, h]; simp)
      have h13 : i1 ≠ i3 := fun h => (Finset.notMem_erase i1 live) (by rw [hs3, h]; simp)
      have h14 : i1 ≠ i4 := fun h => (Finset.notMem_erase i1 live) (by rw [hs3, h]; simp)
      have hlive_eq : live = {i1, i2, i3, i4} := by rw [← Finset.insert_erase hi1, hs3]
      subst hlive_eq
      have h1 := hlive i1 (by simp); have h2 := hlive i2 (by simp)
      have h3 := hlive i3 (by simp); have h4 := hlive i4 (by simp)
      let e1 := cross3 (α i1) (β i1); let e2 := cross3 (α i2) (β i2)
      let e3 := cross3 (α i3) (β i3); let e4 := cross3 (α i4) (β i4)
      have he1 := cross3_ne_zero _ _ h1.1 h1.2.1 h1.2.2
      have he2 := cross3_ne_zero _ _ h2.1 h2.2.1 h2.2.2
      have he3 := cross3_ne_zero _ _ h3.1 h3.2.1 h3.2.2
      have he4 := cross3_ne_zero _ _ h4.1 h4.2.1 h4.2.2
      have hsum : e1 + e2 + e3 + e4 = 0 := by
        funext k
        fin_cases k
        · have h := hpol ![0, 1, 0] ![0, 0, 1]
          simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, h12, h13, h14, h23, h24, h34,
            or_self, not_false_eq_true, Finset.sum_singleton] at h
          change e1 0 + e2 0 + e3 0 + e4 0 = 0
          simp only [e1, e2, e3, e4, ← (cross3_polar_coord _ _).1]
          linear_combination h
        · have h := hpol ![0, 0, 1] ![1, 0, 0]
          simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, h12, h13, h14, h23, h24, h34,
            or_self, not_false_eq_true, Finset.sum_singleton] at h
          change e1 1 + e2 1 + e3 1 + e4 1 = 0
          simp only [e1, e2, e3, e4, ← (cross3_polar_coord _ _).2.1]
          linear_combination h
        · have h := hpol ![1, 0, 0] ![0, 1, 0]
          simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, h12, h13, h14, h23, h24, h34,
            or_self, not_false_eq_true, Finset.sum_singleton] at h
          change e1 2 + e2 2 + e3 2 + e4 2 = 0
          simp only [e1, e2, e3, e4, ← (cross3_polar_coord _ _).2.2]
          linear_combination h
      obtain ⟨v1, v2, v3, v4, hpack⟩ := pack4_dim3 e1 e2 e3 e4 he1 he2 he3 he4 hsum
      obtain ⟨P1, d1, hP1⟩ := dim3_edge_err (α i1) (β i1) v1 h1.1 h1.2.1 h1.2.2
      obtain ⟨P2, d2, hP2⟩ := dim3_edge_err (α i2) (β i2) v2 h2.1 h2.2.1 h2.2.2
      obtain ⟨P3, d3, hP3⟩ := dim3_edge_err (α i3) (β i3) v3 h3.1 h3.2.1 h3.2.2
      obtain ⟨P4, d4, hP4⟩ := dim3_edge_err (α i4) (β i4) v4 h4.1 h4.2.1 h4.2.2
      let P' : Fin m → Vec 3 := fun i =>
        if i = i1 then P1 else if i = i2 then P2 else if i = i3 then P3 else if i = i4 then P4 else 0
      let d : Fin m → F := fun i =>
        if i = i1 then d1 else if i = i2 then d2 else if i = i3 then d3 else if i = i4 then d4 else 0
      have hP1v : P' i1 = P1 ∧ d i1 = d1 := ⟨by simp [P'], by simp [d]⟩
      have hP2v : P' i2 = P2 ∧ d i2 = d2 := ⟨by simp [P', Ne.symm h12], by simp [d, Ne.symm h12]⟩
      have hP3v : P' i3 = P3 ∧ d i3 = d3 := ⟨by simp [P', Ne.symm h13, Ne.symm h23], by simp [d, Ne.symm h13, Ne.symm h23]⟩
      have hP4v : P' i4 = P4 ∧ d i4 = d4 := ⟨by simp [P', Ne.symm h14, Ne.symm h24, Ne.symm h34], by simp [d, Ne.symm h14, Ne.symm h24, Ne.symm h34]⟩
      refine ⟨P', d, hpairwise P' d fun z i hi j hj hij ⟨hzi, hzj⟩ => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl
      · exact hij rfl
      · rw [hP1v.1, hP1v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
        exact (hpack z).1 ⟨(hP1 z).1 hzi, (hP2 z).1 hzj⟩
      · rw [hP1v.1, hP1v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
        exact (hpack z).2.1 ⟨(hP1 z).1 hzi, (hP3 z).1 hzj⟩
      · rw [hP1v.1, hP1v.2] at hzi; rw [hP4v.1, hP4v.2] at hzj
        exact (hpack z).2.2.1 ⟨(hP1 z).1 hzi, (hP4 z).1 hzj⟩
      · rw [hP2v.1, hP2v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
        exact (hpack z).1 ⟨(hP1 z).1 hzj, (hP2 z).1 hzi⟩
      · exact hij rfl
      · rw [hP2v.1, hP2v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
        exact (hpack z).2.2.2.1 ⟨(hP2 z).1 hzi, (hP3 z).1 hzj⟩
      · rw [hP2v.1, hP2v.2] at hzi; rw [hP4v.1, hP4v.2] at hzj
        exact (hpack z).2.2.2.2.1 ⟨(hP2 z).1 hzi, (hP4 z).1 hzj⟩
      · rw [hP3v.1, hP3v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
        exact (hpack z).2.1 ⟨(hP1 z).1 hzj, (hP3 z).1 hzi⟩
      · rw [hP3v.1, hP3v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
        exact (hpack z).2.2.2.1 ⟨(hP2 z).1 hzj, (hP3 z).1 hzi⟩
      · exact hij rfl
      · rw [hP3v.1, hP3v.2] at hzi; rw [hP4v.1, hP4v.2] at hzj
        exact (hpack z).2.2.2.2.2 ⟨(hP3 z).1 hzi, (hP4 z).1 hzj⟩
      · rw [hP4v.1, hP4v.2] at hzi; rw [hP1v.1, hP1v.2] at hzj
        exact (hpack z).2.2.1 ⟨(hP1 z).1 hzj, (hP4 z).1 hzi⟩
      · rw [hP4v.1, hP4v.2] at hzi; rw [hP2v.1, hP2v.2] at hzj
        exact (hpack z).2.2.2.2.1 ⟨(hP2 z).1 hzj, (hP4 z).1 hzi⟩
      · rw [hP4v.1, hP4v.2] at hzi; rw [hP3v.1, hP3v.2] at hzj
        exact (hpack z).2.2.2.2.2 ⟨(hP3 z).1 hzj, (hP4 z).1 hzi⟩
      · exact hij rfl

lemma backward_dir {n m : ℕ} (a b : Fin m → Vec n)
    (hcard : ((Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)).card ≤ 4)
    (hrank : Module.finrank F (Submodule.span F (↑((((Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)).image a) ∪ (((Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)).image b)) : Set (Vec n))) ≤ 3)
    (hpolar : ((Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)).card = 4 →
      ∀ x y : Vec n, (∑ i ∈ ((Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)),
        (dotProduct (a i) x * dotProduct (b i) y + dotProduct (a i) y * dotProduct (b i) x)) = 0) :
    ∃ (P : Fin m → Vec n) (d : Fin m → F), ∀ x : Vec n,
      (Finset.univ.filter (fun i : Fin m => dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ 1 := by
  let live := (Finset.univ : Finset (Fin m)).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
  let U := Submodule.span F (↑(live.image a ∪ live.image b) : Set (Vec n))
  let B := Module.finBasis F U
  let r := Module.finrank F U
  let u : Fin r → Vec n := fun k => (B k).val
  have hu_li : LinearIndependent F u := by
    have := B.linearIndependent
    exact this.map' U.subtype (Submodule.ker_subtype U)
  let φ := evalMap u
  have hφ_surj : Function.Surjective φ := evalMap_surjective hu_li
  have haU : ∀ i ∈ live, a i ∈ U := fun i hi =>
    Submodule.subset_span (by simp; left; exact ⟨i, hi, rfl⟩)
  have hbU : ∀ i ∈ live, b i ∈ U := fun i hi =>
    Submodule.subset_span (by simp; right; exact ⟨i, hi, rfl⟩)
  let α : Fin m → Vec r := fun i => if hi : i ∈ live then (B.repr ⟨a i, haU i hi⟩ : Vec r) else 0
  let β : Fin m → Vec r := fun i => if hi : i ∈ live then (B.repr ⟨b i, hbU i hi⟩ : Vec r) else 0
  have hrep_dot : ∀ (v : Vec n) (hv : v ∈ U) (x : Vec n),
      dotProduct v x = dotProduct (B.repr ⟨v, hv⟩ : Vec r) (φ x) := by
    intro v hv x
    have hv_eq : v = ∑ k : Fin r, B.repr ⟨v, hv⟩ k • u k := by
      have h := congrArg Subtype.val (B.sum_repr ⟨v, hv⟩).symm
      rw [Submodule.coe_sum] at h
      exact h
    conv_lhs => rw [hv_eq]
    simp only [φ, evalMap, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hα_dot : ∀ i ∈ live, ∀ x : Vec n, dotProduct (a i) x = dotProduct (α i) (φ x) := by
    intro i hi x; simp only [α, dite_eq_left hi]; exact hrep_dot (a i) (haU i hi) x
  have hβ_dot : ∀ i ∈ live, ∀ x : Vec n, dotProduct (b i) x = dotProduct (β i) (φ x) := by
    intro i hi x; simp only [β, dite_eq_left hi]; exact hrep_dot (b i) (hbU i hi) x
  have hlive' : ∀ i ∈ live, α i ≠ 0 ∧ β i ≠ 0 ∧ α i ≠ β i := by
    intro i hi
    have h := (Finset.mem_filter.1 hi).2
    simp only [α, β, dite_eq_left hi]
    refine ⟨?_, ?_, ?_⟩
    · intro hz; apply h.1
      have hfs : B.repr ⟨a i, haU i hi⟩ = 0 := Finsupp.ext fun k => congrFun hz k
      have := congrArg (fun z => (B.repr.symm z : Vec n)) hfs
      simpa using this
    · intro hz; apply h.2.1
      have hfs : B.repr ⟨b i, hbU i hi⟩ = 0 := Finsupp.ext fun k => congrFun hz k
      have := congrArg (fun z => (B.repr.symm z : Vec n)) hfs
      simpa using this
    · intro hz; apply h.2.2
      have hfs : B.repr ⟨a i, haU i hi⟩ = B.repr ⟨b i, hbU i hi⟩ := Finsupp.ext fun k => congrFun hz k
      have := congrArg (fun z => (B.repr.symm z : Vec n)) hfs
      simpa using this
  have hpolar' : live.card = 4 → ∀ x' y' : Vec r,
      ∑ i ∈ live, (dotProduct (α i) x' * dotProduct (β i) y' + dotProduct (α i) y' * dotProduct (β i) x') = 0 := by
    intro hc4 x' y'
    obtain ⟨x, rfl⟩ := hφ_surj x'
    obtain ⟨y, rfl⟩ := hφ_surj y'
    have h := hpolar hc4 x y
    convert h using 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hα_dot i hi x, hβ_dot i hi y, hα_dot i hi y, hβ_dot i hi x]
  obtain ⟨P', d', hPd'⟩ := solve_on_small hrank live α β hlive' hcard hpolar'
  let P : Fin m → Vec n := fun i =>
    if i ∈ live then ∑ k : Fin r, P' i k • u k
    else if a i = 0 ∨ b i = 0 then 0
    else a i
  let d : Fin m → F := fun i => if i ∈ live then d' i else 0
  refine ⟨P, d, fun x => ?_⟩
  have hsub : Finset.univ.filter (fun i : Fin m => dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x) ⊆
      live.filter (fun i => dotProduct (P' i) (φ x) + d' i ≠ dotProduct (α i) (φ x) * dotProduct (β i) (φ x)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases hmem : i ∈ live
    · refine ⟨hmem, ?_⟩
      have hPdot : dotProduct (P i) x = dotProduct (P' i) (φ x) := by
        simp only [P, ite_eq_left hmem, φ, evalMap, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
      simpa [d, ite_eq_left hmem, hPdot, hα_dot i hmem x, hβ_dot i hmem x] using hi
    · exfalso
      have hnot : a i = 0 ∨ b i = 0 ∨ a i = b i := by
        simp only [live, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hmem
        exact hmem
      simp only [P, d, ite_eq_right hmem, add_zero] at hi
      rcases hnot with h0 | h0 | heq
      · simp [h0] at hi
      · simp [h0] at hi
      · by_cases h0 : a i = 0 ∨ b i = 0
        · rcases h0 with h | h <;> simp [h] at hi
        · have hbne : b i ≠ 0 := fun hb => h0 (Or.inr hb)
          simp [heq, hbne, z2_mul_self] at hi
  exact le_trans (Finset.card_le_card hsub) (hPd' (φ x))

end PEqualNP.Outside.L_lib_954

theorem PEqualNP.Outside.L_lib_954 : (∀ (n m : Nat),
  let F := ZMod 2
  let W := Fin n → F
  let I := Fin m
  ∀ a b : I → W,
    let live := (Finset.univ : Finset I).filter (fun i => a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    let U := Submodule.span F (↑(live.image a ∪ live.image b) : Set W)
    (∃ (P : I → W) (d : I → F), ∀ x : W,
      ((Finset.univ : Finset I).filter (fun i =>
        dotProduct (P i) x+d i ≠ dotProduct (a i) x*dotProduct (b i) x)).card ≤ 1) ↔
    live.card ≤ 4 ∧ Module.finrank F U ≤ 3 ∧
      (live.card = 4 → ∀ x y : W, (∑ i ∈ live,
        (dotProduct (a i) x*dotProduct (b i) y + dotProduct (a i) y*dotProduct (b i) x)) = 0)) := by
  intro n m F W I a b live U
  exact ⟨PEqualNP.Outside.L_lib_954.forward_dir a b,
    fun ⟨h1, h2, h3⟩ => PEqualNP.Outside.L_lib_954.backward_dir a b h1 h2 h3⟩
