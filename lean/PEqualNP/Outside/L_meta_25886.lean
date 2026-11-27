import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25886

lemma Matching25886_square_tangent (t d : ℕ) :
    (2 * d + 1) * t ≤ t ^ 2 + d ^ 2 + d := by
  by_cases h : t ≤ d
  · have hp : 0 ≤ ((d : ℤ) - t) * ((d : ℤ) + 1 - t) :=
      mul_nonneg (by omega) (by omega)
    exact_mod_cast (show (2 * (d : ℤ) + 1) * t ≤ (t : ℤ) ^ 2 + (d : ℤ) ^ 2 + d by
      nlinarith)
  · have hp : 0 ≤ ((t : ℤ) - d) * ((t : ℤ) - (d + 1)) :=
      mul_nonneg (by omega) (by omega)
    exact_mod_cast (show (2 * (d : ℤ) + 1) * t ≤ (t : ℤ) ^ 2 + (d : ℤ) ^ 2 + d by
      nlinarith)

lemma Matching25886_balanced_squares {k b : ℕ} (hk : 0 < k)
    (h : Fin k → ℕ) (hsum : ∑ i, h i = b) :
    k * (b / k) ^ 2 + (2 * (b / k) + 1) * (b % k) ≤ ∑ i, (h i) ^ 2 := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin k) _ => Matching25886_square_tangent (h i) (b / k))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum] at ht
  have hb := Nat.mod_add_div b k
  have hb' := congrArg (fun t => (2 * (b / k) + 1) * t) hb
  nlinarith only [ht, hb']

lemma Matching25886_weight_pos {k b : ℕ} (hk : 0 < k) (hb : 0 < b) :
    0 < k * (b / k) ^ 2 + (2 * (b / k) + 1) * (b % k) := by
  by_cases h : b / k = 0
  · have hmod : b % k = b := by
      have := Nat.mod_add_div b k
      simp only [h, mul_zero, add_zero] at this
      exact this
    simp [h, hmod, hb]
  · have hd : 0 < b / k := Nat.pos_of_ne_zero h
    exact lt_of_lt_of_le (Nat.mul_pos hk (pow_pos hd 2)) (Nat.le_add_right _ _)

lemma Matching25886_balanced_squares_le {t k b : ℕ} (htk : t ≤ k)
    (h : Fin t → ℕ) (hsum : ∑ i, h i = b) :
    k * (b / k) ^ 2 + (2 * (b / k) + 1) * (b % k) ≤ ∑ i, (h i) ^ 2 := by
  have ht := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin t) _ => Matching25886_square_tangent (h i) (b / k))
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hsum] at ht
  have htk' := Nat.mul_le_mul_right ((b / k) ^ 2 + b / k) htk
  have hb' := congrArg (fun v => (2 * (b / k) + 1) * v) (Nat.mod_add_div b k)
  nlinarith only [ht, htk', hb']

lemma Matching25886_weight_eq_small {k b : ℕ} (hk : 0 < k) (hb : b ≤ k) :
    k * (b / k) ^ 2 + (2 * (b / k) + 1) * (b % k) = b := by
  rcases lt_or_eq_of_le hb with hb | rfl
  · simp [Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]
  · simp [Nat.div_self hk]

lemma Matching25886_weight_ge_copies {k b : ℕ} (hk : 0 < k) :
    b ≤ k * (b / k) ^ 2 + (2 * (b / k) + 1) * (b % k) := by
  have hd : b / k ≤ (b / k) ^ 2 := Nat.le_self_pow (by omega) _
  have hb := Nat.mod_add_div b k
  have hm : b % k ≤ (2 * (b / k) + 1) * (b % k) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have := Nat.add_le_add (Nat.mul_le_mul_left k hd) hm
  omega

end PEqualNP.Outside.L_meta_25886

namespace PEqualNP.Outside.L_meta_25886

def Matching25886Fits (s q : ℕ) (rowCap colCap : Fin q → ℕ)
    (G : Fin s → Fin s → Bool) (budget : ℕ) : Prop :=
  ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool)
    (R C : Fin q → Finset (Fin s))
    (out : Finset (Fin s) → (Fin q → Bool) → Bool),
    (∀ j, (R j).card ≤ rowCap j ∧ (C j).card ≤ colCap j) ∧
    ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget

lemma Matching25886_preimage_card {α β : Type*} [Fintype α] [DecidableEq α]
    [DecidableEq β] (f : α → β) (hf : Function.Injective f) (S : Finset β) :
    (Finset.univ.filter (fun x => f x ∈ S)).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ h
    exact hf h

lemma Matching25886_pair_singleton {α : Type*} [DecidableEq α] {u v : α} :
    (∃ i, ({u,v} : Finset α) = {i}) ↔ u = v := by
  constructor
  · rintro ⟨i, hi⟩
    have hu : u = i := Finset.mem_singleton.mp (hi ▸ (by simp : u ∈ ({u,v} : Finset α)))
    have hv : v = i := Finset.mem_singleton.mp (hi ▸ (by simp : v ∈ ({u,v} : Finset α)))
    exact hu.trans hv.symm
  · rintro rfl
    exact ⟨u, by simp⟩

noncomputable def Matching25886Decoder {n N q : ℕ} (f : Fin n → Fin N)
    (D : Fin n → Bool) (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (S : Finset (Fin n)) (obs : Fin q → Bool) : Bool :=
  if h : ∃ i, S = {i} then D (Classical.choose h) else out (S.image f) obs

lemma Matching25886Decoder_diag {n N q : ℕ} (f : Fin n → Fin N)
    (D : Fin n → Bool) (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (u : Fin n) (obs : Fin q → Bool) :
    Matching25886Decoder f D out {u,u} obs = D u := by
  classical
  have h : ∃ i, ({u,u} : Finset (Fin n)) = {i} := ⟨u, by simp⟩
  simp only [Matching25886Decoder, dif_pos h]
  have he := Classical.choose_spec h
  have hu : u = Classical.choose h :=
    Finset.mem_singleton.mp (he ▸ (by simp : u ∈ ({u,u} : Finset (Fin n))))
  rw [← hu]

lemma Matching25886Decoder_offdiag {n N q : ℕ} (f : Fin n → Fin N)
    (D : Fin n → Bool) (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (u v : Fin n) (huv : u ≠ v) (obs : Fin q → Bool) :
    Matching25886Decoder f D out {u,v} obs = out {f u,f v} obs := by
  classical
  have h : ¬ ∃ i, ({u,v} : Finset (Fin n)) = {i} :=
    fun h => huv (Matching25886_pair_singleton.mp h)
  simp [Matching25886Decoder, h]

lemma Matching25886_restrict
    {n N q : ℕ} (rowCap colCap : Fin q → ℕ)
    (G : Fin n → Fin n → Bool) (typ : Fin N → Fin n)
    (π : Equiv.Perm (Fin N)) (rf cf : Fin N → Bool)
    (R C : Fin q → Finset (Fin N))
    (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (hcaps : ∀ j, (R j).card ≤ rowCap j ∧ (C j).card ≤ colCap j)
    (f : Fin n → Fin N) (σ : Equiv.Perm (Fin n))
    (hl : ∀ u, typ (f u) = u) (hr : ∀ u, typ (π (f u)) = σ u) :
    Matching25886Fits n q rowCap colCap G
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
        z.1 ≠ z.2 ∧
        out {f z.1,f z.2} (fun j => decide (f z.1 ∈ R j ∨ π (f z.2) ∈ C j)) ≠
          Bool.xor (G (typ (f z.1)) (typ (π (f z.2))))
            (Bool.xor (rf (f z.1)) (cf (π (f z.2)))))).card := by
  classical
  have hf : Function.Injective f := by
    intro u v huv
    simpa only [hl] using congrArg typ huv
  let cf' := fun v => cf (π (f (σ.symm v)))
  let R' := fun j => Finset.univ.filter (fun u => f u ∈ R j)
  let C' := fun j => Finset.univ.filter (fun v => π (f (σ.symm v)) ∈ C j)
  let D := fun u => Bool.xor (G u (σ u)) (Bool.xor (rf (f u)) (cf (π (f u))))
  refine ⟨σ, rf ∘ f, cf', R', C', Matching25886Decoder f D out, ?_, ?_⟩
  · intro j
    constructor
    · exact (Matching25886_preimage_card f hf (R j)).trans (hcaps j).1
    · exact (Matching25886_preimage_card _ (π.injective.comp (hf.comp σ.symm.injective))
        (C j)).trans (hcaps j).2
  · apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hobs : (fun j => decide (z.1 ∈ R' j ∨ σ z.2 ∈ C' j)) =
        (fun j => decide (f z.1 ∈ R j ∨ π (f z.2) ∈ C j)) := by
      funext j
      simp [R', C']
    have hcf : cf' (σ z.2) = cf (π (f z.2)) := by simp [cf']
    have hne : z.1 ≠ z.2 := by
      intro heq
      apply hz
      simp only [heq, Matching25886Decoder_diag, Function.comp_apply]
      simp [D, cf']
    refine ⟨hne, ?_⟩
    rw [Matching25886Decoder_offdiag f D out z.1 z.2 hne, hobs, hcf] at hz
    simpa only [hl, hr, Function.comp_apply] using hz

lemma Matching25886_singleton (q : ℕ) (rowCap colCap : Fin q → ℕ)
    (G : Fin 1 → Fin 1 → Bool) (budget : ℕ) :
    Matching25886Fits 1 q rowCap colCap G budget := by
  refine ⟨Equiv.refl _, fun _ => false, fun _ => false, fun _ => ∅, fun _ => ∅,
    fun _ _ => G 0 0, ?_, ?_⟩
  · simp
  · have h : (Finset.univ : Finset (Fin 1 × Fin 1)).filter (fun z =>
        G 0 0 ≠ Bool.xor (G z.1 ((Equiv.refl (Fin 1)) z.2))
          (Bool.xor false false)) = ∅ := by
      ext z
      simp [Subsingleton.elim z.1 0, Subsingleton.elim z.2 0]
    simpa only [h, Finset.card_empty] using Nat.zero_le budget

end PEqualNP.Outside.L_meta_25886

namespace PEqualNP.Outside.L_meta_25886

lemma Matching25886_count_two {n h : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : Fin h) :
    ((Finset.univ : Finset (Fin n → Fin h)).filter
      (fun f => f i = a ∧ f j = b)).card = h ^ (n - 2) := by
  classical
  let S : Fin n → Finset (Fin h) := Function.update (fun _ => Finset.univ) i {a}
  have hfirst : (Finset.univ : Finset (Fin n → Fin h)).filter (fun f => f i = a) =
      Fintype.piFinset S := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hf k
      by_cases hk : k = i <;> simp [S, hk, hf]
    · intro hf
      simpa [S] using hf i
  have hboth : (Finset.univ : Finset (Fin n → Fin h)).filter
      (fun f => f i = a ∧ f j = b) =
      (Fintype.piFinset S).filter (fun f => f j = b) := by
    rw [← hfirst]
    ext f
    simp
  rw [hboth, Fintype.card_filter_piFinset_eq_of_mem S j (by simp [S, hij.symm])]
  have hcard : (fun k => (S k).card) = Function.update (fun _ => h) i 1 := by
    funext k
    by_cases hk : k = i <;> simp [S, hk]
  rw [hcard, Finset.prod_update_of_mem (by simp [hij])]
  simp [← Finset.erase_eq, Finset.card_erase_of_mem, hij, hij.symm, Nat.sub_sub]

lemma Matching25886_sum_two {n h : ℕ} (i j : Fin n) (hij : i ≠ j)
    (c : Fin h → Fin h → ℕ) :
    (∑ f : Fin n → Fin h, c (f i) (f j)) =
      h ^ (n - 2) * ∑ a : Fin h, ∑ b : Fin h, c a b := by
  classical
  have hf (f : Fin n → Fin h) :
      c (f i) (f j) = ∑ a : Fin h, ∑ b : Fin h,
        if f i = a ∧ f j = b then c a b else 0 := by
    simp [ite_and]
  have hterm (a b : Fin h) :
      (∑ f ∈ (Finset.univ : Finset (Fin n → Fin h)).filter
        (fun f => f i = a ∧ f j = b), c a b) = h ^ (n - 2) * c a b := by
    rw [Finset.sum_const, smul_eq_mul, Matching25886_count_two i j hij a b]
  calc
    _ = ∑ f : Fin n → Fin h, ∑ a : Fin h, ∑ b : Fin h,
        if f i = a ∧ f j = b then c a b else 0 :=
      Finset.sum_congr rfl (fun f _ => hf f)
    _ = ∑ a : Fin h, ∑ b : Fin h, ∑ f : Fin n → Fin h,
        if f i = a ∧ f j = b then c a b else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a : Fin h, ∑ b : Fin h, h ^ (n - 2) * c a b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_filter]
      exact hterm a b
    _ = _ := by simp_rw [Finset.mul_sum]

lemma Matching25886_weighted_average {α : Type*} [Fintype α] [Nonempty α]
    (cost : α → ℕ) (w E : ℕ)
    (hs : w * ∑ x, cost x ≤ Fintype.card α * E) :
    ∃ x, cost x * w ≤ E := by
  by_contra h
  have hx : ∀ x, E + 1 ≤ w * cost x := by
    intro x
    have : ¬ cost x * w ≤ E := fun he => h ⟨x, he⟩
    rw [Nat.mul_comm (cost x) w] at this
    omega
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at ht
  have hp := Fintype.card_pos (α := α)
  nlinarith

lemma Matching25886_sample_bound {n h : ℕ} (hn : 2 ≤ n) (hh : 0 < h)
    (c : Fin n → Fin n → Fin h → Fin h → ℕ) :
    ∃ f : Fin n → Fin h,
      (∑ z : Fin n × Fin n, if z.1 ≠ z.2 then c z.1 z.2 (f z.1) (f z.2) else 0) * h ^ 2 ≤
        ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then ∑ a : Fin h, ∑ b : Fin h,
          c z.1 z.2 a b else 0 := by
  classical
  letI : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
  let cost := fun f : Fin n → Fin h =>
    ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then c z.1 z.2 (f z.1) (f z.2) else 0
  let E := ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then
    ∑ a : Fin h, ∑ b : Fin h, c z.1 z.2 a b else 0
  have heq : ∑ f : Fin n → Fin h, cost f = h ^ (n - 2) * E := by
    unfold cost E
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z.1 = z.2
    · simp [hz]
    · simpa [hz] using Matching25886_sum_two z.1 z.2 hz (c z.1 z.2)
  apply Matching25886_weighted_average cost (h ^ 2) E
  rw [heq, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hn' : 2 + (n - 2) = n := by omega
  rw [← mul_assoc, ← pow_add, hn']

lemma Matching25886_group_average {α : Type*} [Fintype α]
    (cost weight : α → ℕ) (W E : ℕ) (hW : 0 < W)
    (hw : W ≤ ∑ x, weight x) (hs : ∑ x, cost x * weight x ≤ E) :
    ∃ x, 0 < weight x ∧ cost x ≤ E / W := by
  by_contra h
  have hx : ∀ x, (E / W + 1) * weight x ≤ cost x * weight x := by
    intro x
    by_cases hz : weight x = 0
    · simp [hz]
    · have hp : 0 < weight x := Nat.pos_of_ne_zero hz
      have : ¬ cost x ≤ E / W := fun he => h ⟨x, hp, he⟩
      exact Nat.mul_le_mul_right _ (by omega)
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hx x)
  rw [← Finset.mul_sum] at ht
  have hw' := Nat.mul_le_mul_left (E / W + 1) hw
  have hdiv : E < (E / W + 1) * W := by
    have := Nat.mod_lt E hW
    have := Nat.div_add_mod E W
    nlinarith
  omega

end PEqualNP.Outside.L_meta_25886

namespace PEqualNP.Outside.L_meta_25886

def Matching25886PM {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if σ i = j then 1 else 0

lemma Matching25886_supported_perm {n b : ℕ} (hb : 0 < b)
    (M : Fin n → Fin n → ℕ)
    (hr : ∀ i, ∑ j, M i j = b) (hc : ∀ j, ∑ i, M i j = b) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, 0 < M i (σ i) := by
  classical
  let S := fun i => (Finset.univ : Finset (Fin n)).filter (fun j => 0 < M i j)
  have hall : ∀ A : Finset (Fin n), A.card ≤ (A.biUnion S).card := by
    intro A
    have h1 : ∑ i ∈ A, ∑ j ∈ S i, M i j = A.card * b := by
      have ht : ∀ i, ∑ j ∈ S i, M i j = b := by
        intro i
        rw [← hr i]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hj
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
        omega
      simp [ht]
    have h2 : ∑ i : Fin n, ∑ j ∈ A.biUnion S, M i j = (A.biUnion S).card * b := by
      rw [Finset.sum_comm]
      simp [hc]
    have hle : A.card * b ≤ (A.biUnion S).card * b := by
      rw [← h1, ← h2]
      calc
        _ ≤ ∑ i ∈ A, ∑ j ∈ A.biUnion S, M i j := by
          apply Finset.sum_le_sum
          intro i hi
          exact Finset.sum_le_sum_of_subset (Finset.subset_biUnion_of_mem S hi)
        _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    exact Nat.le_of_mul_le_mul_right hle hb
  obtain ⟨g, hg, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' S).mp hall
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), ?_⟩
  intro i
  exact (Finset.mem_filter.mp (hmem i)).2

lemma Matching25886_decompose {n : ℕ} (hn : 0 < n) :
    ∀ (b : ℕ) (M : Fin n → Fin n → ℕ),
      (∀ i, ∑ j, M i j = b) → (∀ j, ∑ i, M i j = b) →
      ∃ (t : ℕ) (σ : Fin t → Equiv.Perm (Fin n)) (h : Fin t → ℕ),
        (∀ a, 0 < h a) ∧
        (∀ i j, (∑ a, if σ a i = j then h a else 0) = M i j) ∧
        LinearIndependent ℚ (fun a => Matching25886PM (σ a)) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro b
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro M hr hc
    by_cases hb : b = 0
    · refine ⟨0, Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, ?_, ?_⟩
      · intro i j
        have hm : M i j ≤ ∑ j, M i j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
        simp only [hr, hb] at hm
        simp [Nat.eq_zero_of_le_zero hm]
      · exact linearIndependent_empty_type
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    obtain ⟨p, hp⟩ := Matching25886_supported_perm hbpos M hr hc
    obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ
      (fun i => M i (p i)) Finset.univ_nonempty
    let d := M i₀ (p i₀)
    have hd : 0 < d := hp i₀
    have hdi : ∀ i, d ≤ M i (p i) := fun i => hmin i (Finset.mem_univ i)
    have hdb : d ≤ b := by
      have hs : M i₀ (p i₀) ≤ ∑ j, M i₀ j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp)
      simpa [hr, d] using hs
    let M' := fun i j => M i j - if p i = j then d else 0
    have heq : ∀ i j, M' i j + (if p i = j then d else 0) = M i j := by
      intro i j
      by_cases hij : p i = j
      · simp only [M', hij, if_true]
        apply Nat.sub_add_cancel
        simpa [hij] using hdi i
      · simp [M', hij]
    have hr' : ∀ i, ∑ j, M' i j = b - d := by
      intro i
      have hs := congrArg (fun f : Fin n → ℕ => ∑ j, f j) (funext (heq i))
      have hpi : (∑ j : Fin n, if p i = j then d else 0) = d := by simp
      simp only [Finset.sum_add_distrib, hpi, hr] at hs
      omega
    have hc' : ∀ j, ∑ i, M' i j = b - d := by
      intro j
      have hs := congrArg (fun f : Fin n → ℕ => ∑ i, f i) (funext (fun i => heq i j))
      have hpj : ∑ i : Fin n, (if p i = j then d else 0) = d := by
        simp_rw [p.apply_eq_iff_eq_symm_apply]
        simp
      simp only [Finset.sum_add_distrib, hpj, hc] at hs
      omega
    obtain ⟨t, σ, h, hh, hM, hLI⟩ := ih (b - d) (by omega) M' hr' hc'
    have hzero : M' i₀ (p i₀) = 0 := by simp [M', d]
    have hpivot : ∀ a, σ a i₀ ≠ p i₀ := by
      intro a ha
      have hs : (if σ a i₀ = p i₀ then h a else 0) ≤
          ∑ a, if σ a i₀ = p i₀ then h a else 0 :=
        Finset.single_le_sum (f := fun a : Fin t => if σ a i₀ = p i₀ then h a else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      rw [hM, hzero, if_pos ha] at hs
      exact (Nat.not_le_of_gt (hh a)) hs
    have hspan : Matching25886PM p ∉
        Submodule.span ℚ (Set.range (fun a => Matching25886PM (σ a))) := by
      intro hmem
      have hz : ∀ v ∈ Submodule.span ℚ (Set.range (fun a => Matching25886PM (σ a))),
          v i₀ (p i₀) = 0 := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          rcases hv with ⟨a, rfl⟩
          simp [Matching25886PM, hpivot a]
        | zero => rfl
        | add x y hx hy hx0 hy0 => simp [hx0, hy0]
        | smul c x hx hx0 => simp [hx0]
      have := hz _ hmem
      simpa [Matching25886PM] using this
    refine ⟨t + 1, Fin.cons p σ, Fin.cons d h, ?_, ?_, ?_⟩
    · intro a
      refine Fin.cases hd hh a
    · intro i j
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hM]
      exact (Nat.add_comm _ _).trans (heq i j)
    · have he : (fun a : Fin (t + 1) =>
          Matching25886PM ((Fin.cons p σ : Fin (t + 1) → Equiv.Perm (Fin n)) a)) =
          Fin.cons (Matching25886PM p) (fun a => Matching25886PM (σ a)) := by
        funext a
        refine Fin.cases rfl (fun _ => rfl) a
      rw [he]
      exact hLI.finCons hspan

lemma Matching25886_independent_bound {n t : ℕ} (hn : 0 < n)
    (σ : Fin t → Equiv.Perm (Fin n))
    (hLI : LinearIndependent ℚ (fun a => Matching25886PM (σ a))) :
    t ≤ (n - 1) ^ 2 + 1 := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    let enc := fun a : Fin t => fun z : (Fin m × Fin m) ⊕ Unit =>
      match z with
      | Sum.inl (i,j) => Matching25886PM (σ a) i.castSucc j.castSucc
      | Sum.inr _ => 1
    have hEnc : LinearIndependent ℚ enc := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hs : (∑ a, c a) = 0 := by
        have he := congrFun hc (Sum.inr ())
        simpa [enc] using he
      let A : Fin (m + 1) → Fin (m + 1) → ℚ :=
        fun i j => ∑ a, c a * Matching25886PM (σ a) i j
      have htop : ∀ i j : Fin m, A i.castSucc j.castSucc = 0 := by
        intro i j
        have he := congrFun hc (Sum.inl (i,j))
        simpa [enc, A] using he
      have hrow : ∀ i, ∑ j, A i j = 0 := by
        intro i
        dsimp [A]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        simpa [Matching25886PM] using hs
      have hcol : ∀ j, ∑ i, A i j = 0 := by
        intro j
        dsimp [A]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum]
        have hp : ∀ a, (∑ i : Fin (m + 1), Matching25886PM (σ a) i j) = 1 := by
          intro a
          simp only [Matching25886PM]
          simp_rw [(σ a).apply_eq_iff_eq_symm_apply]
          simp
        simpa only [hp, mul_one] using hs
      have hright : ∀ i : Fin m, A i.castSucc (Fin.last m) = 0 := by
        intro i
        have he := hrow i.castSucc
        rw [Fin.sum_univ_castSucc] at he
        simpa [htop] using he
      have hbottom : ∀ j : Fin m, A (Fin.last m) j.castSucc = 0 := by
        intro j
        have he := hcol j.castSucc
        rw [Fin.sum_univ_castSucc] at he
        simpa [htop] using he
      have hcorner : A (Fin.last m) (Fin.last m) = 0 := by
        have he := hrow (Fin.last m)
        rw [Fin.sum_univ_castSucc] at he
        simpa [hbottom] using he
      have hzero : ∀ i j, A i j = 0 := by
        intro i
        refine Fin.lastCases ?_ ?_ i
        · intro j
          exact Fin.lastCases hcorner hbottom j
        · intro i j
          exact Fin.lastCases (hright i) (htop i) j
      apply Fintype.linearIndependent_iff.mp hLI c
      ext i j
      simpa [A] using hzero i j
    have ht := hEnc.fintype_card_le_finrank
    simpa [Module.finrank_pi, Fintype.card_sum, Fintype.card_prod, pow_two] using ht

end PEqualNP.Outside.L_meta_25886

namespace PEqualNP.Outside.L_meta_25886

lemma Matching25886_allocate {α : Type*} [Fintype α] {n t : ℕ}
    (l r : α → Fin n) (σ : Fin t → Equiv.Perm (Fin n)) (h : Fin t → ℕ)
    (hM : ∀ i j, (∑ a, if σ a i = j then h a else 0) =
      (Finset.univ.filter (fun x => l x = i ∧ r x = j)).card) :
    ∃ e : (Σ a : Fin t, Fin n × Fin (h a)) ≃ α,
      ∀ a i k, l (e ⟨a, i, k⟩) = i ∧ r (e ⟨a, i, k⟩) = σ a i := by
  classical
  let D := Σ a : Fin t, Fin n × Fin (h a)
  let f := fun x : D => (x.2.1, σ x.1 x.2.1)
  let g := fun x : α => (l x, r x)
  have hc : ∀ z, Fintype.card {x : D // f x = z} = Fintype.card {x : α // g x = z} := by
    rintro ⟨i,j⟩
    have hleft : Fintype.card {x : D // f x = (i,j)} =
        ∑ a, if σ a i = j then h a else 0 := by
      simp [D, f, Fintype.card_subtype, Finset.card_filter,
        Fintype.sum_sigma, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    rw [hleft, hM]
    simp [Fintype.card_subtype, g]
  let E := fun z => Fintype.equivOfCardEq (hc z)
  refine ⟨Equiv.ofFiberEquiv E, ?_⟩
  intro a i k
  have he := Equiv.ofFiberEquiv_map E (⟨a, i, k⟩ : D)
  exact Prod.mk.inj he

lemma Matching25886_matrix_row {α : Type*} [Fintype α]
    {n : ℕ} (l r : α → Fin n) (i : Fin n) :
    (∑ j : Fin n, (Finset.univ.filter (fun x => l x = i ∧ r x = j)).card) =
      (Finset.univ.filter (fun x => l x = i)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_and]

lemma Matching25886_matrix_col {α : Type*} [Fintype α]
    {n : ℕ} (l r : α → Fin n) (j : Fin n) :
    (∑ i : Fin n, (Finset.univ.filter (fun x => l x = i ∧ r x = j)).card) =
      (Finset.univ.filter (fun x => r x = j)).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_and]

def Matching25886Type (n b : ℕ) (hn : 0 < n) (i : Fin (n * b)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ hn⟩

lemma Matching25886_mod_fiber (n b : ℕ) (hn : 0 < n) (u : Fin n) :
    (Finset.univ.filter (fun x : Fin (n * b) => Matching25886Type n b hn x = u)).card = b := by
  classical
  have hlt (k : Fin b) : u.val + k.val * n < n * b := by
    have := Nat.mul_le_mul_right n k.isLt
    nlinarith [u.isLt]
  let emb := fun k : Fin b => (⟨u.val + k.val * n, hlt k⟩ : Fin (n * b))
  have htyp : ∀ k, Matching25886Type n b hn (emb k) = u := by
    intro k
    apply Fin.ext
    simp [Matching25886Type, emb, Nat.mod_eq_of_lt u.isLt]
  have hinj : Function.Injective emb := by
    intro a b hab
    have he := congrArg Fin.val hab
    simp only [emb, Fin.mk.injEq] at he
    apply Fin.ext
    nlinarith
  have himage : Finset.univ.filter (fun x : Fin (n * b) => Matching25886Type n b hn x = u) =
      Finset.univ.image emb := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      refine ⟨⟨x.val / n, Nat.div_lt_of_lt_mul x.isLt⟩, ?_⟩
      apply Fin.ext
      have he := congrArg Fin.val hx
      dsimp only [Matching25886Type] at he
      dsimp only [emb]
      rw [← he, Nat.mul_comm (x.val / n) n]
      exact Nat.mod_add_div x.val n
    · rintro ⟨k, rfl⟩
      exact htyp k
  rw [himage, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma Matching25886_perm_fiber {α β : Type*} [Fintype α] [DecidableEq β]
    (typ : α → β) (π : Equiv.Perm α) (v : β) :
    (Finset.univ.filter (fun x => typ (π x) = v)).card =
      (Finset.univ.filter (fun x => typ x = v)).card := by
  classical
  apply Finset.card_bij (fun x _ => π x)
  · intro x hx
    simpa using hx
  · intro x _ y _ hxy
    exact π.injective hxy
  · intro y hy
    exact ⟨π.symm y, by simpa using hy, by simp⟩

end PEqualNP.Outside.L_meta_25886

namespace PEqualNP.Outside.L_meta_25886

lemma Matching25886_disjoint_squares {n N t : ℕ} (h : Fin t → ℕ)
    (e : (Σ a : Fin t, Fin n × Fin (h a)) ≃ Fin N)
    (bad : Fin N × Fin N → ℕ) :
    (∑ a : Fin t, ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then
        ∑ k : Fin (h a), ∑ l : Fin (h a), bad (e ⟨a,z.1,k⟩, e ⟨a,z.2,l⟩) else 0) ≤
      ∑ z : Fin N × Fin N, bad z := by
  classical
  let D := Σ a : Fin t, (Fin n × Fin (h a)) × (Fin n × Fin (h a))
  let φ := fun x : D => (e ⟨x.1,x.2.1⟩, e ⟨x.1,x.2.2⟩)
  have hinj : Function.Injective φ := by
    rintro ⟨a,x,y⟩ ⟨a',x',y'⟩ he
    have hx : (⟨a,x⟩ : Σ a : Fin t, Fin n × Fin (h a)) = ⟨a',x'⟩ :=
      e.injective (congrArg Prod.fst he)
    have ha : a = a' := congrArg Sigma.fst hx
    subst a'
    have hx' : x = x' := by simpa using hx
    have hy : (⟨a,y⟩ : Σ a : Fin t, Fin n × Fin (h a)) = ⟨a,y'⟩ :=
      e.injective (congrArg Prod.snd he)
    have hy' : y = y' := by simpa using hy
    subst x'
    subst y'
    rfl
  calc
    _ ≤ ∑ a : Fin t, ∑ z : Fin n × Fin n,
        ∑ k : Fin (h a), ∑ l : Fin (h a), bad (e ⟨a,z.1,k⟩, e ⟨a,z.2,l⟩) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro z _
      split_ifs <;> omega
    _ = ∑ x : D, bad (φ x) := by
      simp only [D, φ, Fintype.sum_sigma, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ z ∈ Finset.univ.image φ, bad z :=
      (Finset.sum_image (fun _ _ _ _ he => hinj he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma Matching25886_fits_mono {n q : ℕ} {rowCap colCap : Fin q → ℕ}
    {G : Fin n → Fin n → Bool} {a b : ℕ}
    (ha : Matching25886Fits n q rowCap colCap G a) (hab : a ≤ b) :
    Matching25886Fits n q rowCap colCap G b := by
  obtain ⟨π,rf,cf,R,C,out,hcap,herr⟩ := ha
  exact ⟨π,rf,cf,R,C,out,hcap,herr.trans hab⟩

lemma Matching25886_from_groups {n N q t W E : ℕ} (hn : 2 ≤ n)
    (rowCap colCap : Fin q → ℕ) (G : Fin n → Fin n → Bool) (typ : Fin N → Fin n)
    (π : Equiv.Perm (Fin N)) (rf cf : Fin N → Bool)
    (R C : Fin q → Finset (Fin N))
    (out : Finset (Fin N) → (Fin q → Bool) → Bool)
    (hcaps : ∀ j, (R j).card ≤ rowCap j ∧ (C j).card ≤ colCap j)
    (hErr : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
      out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
        Bool.xor (G (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ E)
    (σ : Fin t → Equiv.Perm (Fin n)) (h : Fin t → ℕ) (hh : ∀ a, 0 < h a)
    (e : (Σ a : Fin t, Fin n × Fin (h a)) ≃ Fin N)
    (he : ∀ a i k, typ (e ⟨a,i,k⟩) = i ∧ typ (π (e ⟨a,i,k⟩)) = σ a i)
    (hW : 0 < W) (hw : W ≤ ∑ a, (h a) ^ 2) :
    Matching25886Fits n q rowCap colCap G (E / W) := by
  classical
  let bad := fun z : Fin N × Fin N =>
    if out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
      Bool.xor (G (typ z.1) (typ (π z.2))) (Bool.xor (rf z.1) (cf (π z.2))) then 1 else 0
  let cost := fun a (f : Fin n → Fin (h a)) =>
    ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then bad (e ⟨a,z.1,f z.1⟩,e ⟨a,z.2,f z.2⟩) else 0
  let B := fun a => ∑ z : Fin n × Fin n, if z.1 ≠ z.2 then
    ∑ k : Fin (h a), ∑ l : Fin (h a), bad (e ⟨a,z.1,k⟩,e ⟨a,z.2,l⟩) else 0
  have hsamp : ∀ a, ∃ f : Fin n → Fin (h a), cost a f * (h a) ^ 2 ≤ B a := by
    intro a
    exact Matching25886_sample_bound hn (hh a)
      (fun i j k l => bad (e ⟨a,i,k⟩, e ⟨a,j,l⟩))
  let f := fun a => Classical.choose (hsamp a)
  have hf : ∀ a, cost a (f a) * (h a) ^ 2 ≤ B a :=
    fun a => Classical.choose_spec (hsamp a)
  have hsum : (∑ a, cost a (f a) * (h a) ^ 2) ≤ E := by
    calc
      _ ≤ ∑ a, B a := Finset.sum_le_sum (fun a _ => hf a)
      _ ≤ ∑ z, bad z := Matching25886_disjoint_squares h e bad
      _ ≤ E := by simpa only [Finset.card_filter] using hErr
  obtain ⟨a, _, ha⟩ := Matching25886_group_average
    (fun a => cost a (f a)) (fun a => (h a) ^ 2) W E hW hw hsum
  have hfits : Matching25886Fits n q rowCap colCap G (cost a (f a)) := by
    have hr := Matching25886_restrict rowCap colCap G typ π rf cf R C out hcaps
      (fun i => e ⟨a,i,f a i⟩) (σ a)
      (fun i => (he a i (f a i)).1) (fun i => (he a i (f a i)).2)
    simpa only [Finset.card_filter, ite_and] using hr
  exact Matching25886_fits_mono hfits ha

end PEqualNP.Outside.L_meta_25886
theorem PEqualNP.Outside.L_meta_25886 : (∀ (n b q : ℕ) (hn : 0 < n), 0 < b →
  ∀ (rowCap colCap : Fin q → ℕ),
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool)
      (R C : Fin q → Finset (Fin s)) (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      (∀ j, (R j).card ≤ rowCap j ∧ (C j).card ≤ colCap j) ∧
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  let typ := fun label : Fin (n*b) => (⟨label.val % n, Nat.mod_lt _ hn⟩ : Fin n)
  let K := (n-1)^2+1
  let d := b/K
  let W := K*d^2 + (2*d+1)*(b % K)
  ∀ (G : Fin n → Fin n → Bool) (E : ℕ),
    fits (n*b) (fun i j => G (typ i) (typ j)) E → fits n G (E/W)) := by
  classical
  intro n b q hn hb rowCap colCap fits typ K d W G E hfit
  change PEqualNP.Outside.L_meta_25886.Matching25886Fits n q rowCap colCap G (E / W)
  by_cases hn1 : n = 1
  · subst n
    exact PEqualNP.Outside.L_meta_25886.Matching25886_singleton q rowCap colCap G (E / W)
  have hn2 : 2 ≤ n := by omega
  obtain ⟨π,rf,cf,R,C,out,hcaps,hErr⟩ := hfit
  let M := fun i j : Fin n =>
    (Finset.univ.filter (fun x : Fin (n*b) => typ x = i ∧ typ (π x) = j)).card
  have hr : ∀ i, ∑ j, M i j = b := by
    intro i
    exact (PEqualNP.Outside.L_meta_25886.Matching25886_matrix_row typ (typ ∘ π) i).trans
      (PEqualNP.Outside.L_meta_25886.Matching25886_mod_fiber n b hn i)
  have hc : ∀ j, ∑ i, M i j = b := by
    intro j
    exact (PEqualNP.Outside.L_meta_25886.Matching25886_matrix_col typ (typ ∘ π) j).trans
      ((PEqualNP.Outside.L_meta_25886.Matching25886_perm_fiber typ π j).trans
        (PEqualNP.Outside.L_meta_25886.Matching25886_mod_fiber n b hn j))
  obtain ⟨t,σ,h,hh,hM,hLI⟩ :=
    PEqualNP.Outside.L_meta_25886.Matching25886_decompose hn b M hr hc
  have ht : t ≤ K :=
    PEqualNP.Outside.L_meta_25886.Matching25886_independent_bound hn σ hLI
  have hsum : ∑ a, h a = b := by
    let i : Fin n := ⟨0, hn⟩
    have hs := congrArg (fun f : Fin n → ℕ => ∑ j, f j) (funext (hM i))
    rw [Finset.sum_comm] at hs
    simpa [hr] using hs
  obtain ⟨e,he⟩ := PEqualNP.Outside.L_meta_25886.Matching25886_allocate typ (typ ∘ π) σ h hM
  have hW : 0 < W :=
    PEqualNP.Outside.L_meta_25886.Matching25886_weight_pos (by dsimp [K]; omega) hb
  have hw : W ≤ ∑ a, (h a) ^ 2 :=
    PEqualNP.Outside.L_meta_25886.Matching25886_balanced_squares_le ht h hsum
  exact PEqualNP.Outside.L_meta_25886.Matching25886_from_groups hn2 rowCap colCap G typ
    π rf cf R C out hcaps hErr σ h hh e he hW hw
