import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1076_aux

open Finset

lemma exists_proj {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (U : Submodule K (n → K)) :
    ∃ L : Matrix n n K, L * L = L ∧ (∀ u ∈ U, L.mulVec u = 0) ∧
      L.rank + Module.finrank K U = Fintype.card n := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl U
  have hQ' : IsCompl Q U := hQ.symm
  refine ⟨LinearMap.toMatrix' (Q.projection U hQ'), ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    congr 1
    exact (Submodule.isIdempotentElem_projection hQ')
  · intro u hu
    rw [LinearMap.toMatrix'_mulVec]
    have hk : u ∈ LinearMap.ker (Q.projection U hQ') := by
      rw [Submodule.ker_projection]; exact hu
    exact hk
  · have h1 : (LinearMap.toMatrix' (Q.projection U hQ')).rank
        = Module.finrank K (LinearMap.range (Q.projection U hQ')) := by
      unfold Matrix.rank
      rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    rw [h1, Submodule.range_projection]
    have h2 := Submodule.finrank_add_eq_of_isCompl hQ
    rw [Module.finrank_fintype_fun_eq_card] at h2
    omega

lemma half_active (q : ℕ) (P : Submodule (ZMod 2) (Fin q → ZMod 2)) (c : Fin q → ZMod 2)
    (hc : c ∉ P) (Z : Finset (Fin q → ZMod 2))
    (hZ : ∀ z, z ∈ Z ↔ ∀ u ∈ P, ∑ k, u k * z k = 0) :
    2 * (Z.filter (fun z => ∑ k, c k * z k ≠ 0)).card = Z.card := by
  classical
  obtain ⟨f, hf, hfP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
  let z0 : Fin q → ZMod 2 := fun k => f (Pi.single k 1)
  have hdot : ∀ u : Fin q → ZMod 2, f u = ∑ k, u k * z0 k := by
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have : (fun j => if k = j then (1 : ZMod 2) else 0) = Pi.single k 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [this]
    rfl
  have hz0 : z0 ∈ Z := by
    rw [hZ]
    intro u hu
    rw [← hdot]
    exact (Submodule.eq_bot_iff _).mp hfP (f u) (Submodule.mem_map_of_mem hu)
  have hcz0 : ∑ k, c k * z0 k ≠ 0 := by
    rw [← hdot]
    exact hf
  have hadd : ∀ (u z z' : Fin q → ZMod 2),
      ∑ k, u k * (z + z') k = ∑ k, u k * z k + ∑ k, u k * z' k := by
    intro u z z'
    simp [mul_add, Finset.sum_add_distrib]
  have hmemadd : ∀ z, z ∈ Z → z + z0 ∈ Z := by
    intro z hz
    rw [hZ] at hz ⊢
    intro u hu
    rw [hadd, hz u hu, (hZ z0).mp hz0 u hu, add_zero]
  have hinv : ∀ z : Fin q → ZMod 2, z + z0 + z0 = z := by
    intro z
    funext k
    have key : ∀ a b : ZMod 2, a + b + b = a := by decide
    exact key _ _
  have key1 : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → ¬ (a + b ≠ 0) := by decide
  have key2 : ∀ a b : ZMod 2, ¬ (a ≠ 0) → b ≠ 0 → a + b ≠ 0 := by decide
  have hcard : (Z.filter (fun z => ∑ k, c k * z k ≠ 0)).card
      = (Z.filter (fun z => ¬ (∑ k, c k * z k ≠ 0))).card := by
    apply Finset.card_nbij' (fun z => z + z0) (fun z => z + z0)
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      exact ⟨hmemadd z hz.1, by rw [hadd]; exact key1 _ _ hz.2 hcz0⟩
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      exact ⟨hmemadd z hz.1, by rw [hadd]; exact key2 _ _ hz.2 hcz0⟩
    · intro z _
      exact hinv z
    · intro z _
      exact hinv z
  have := Finset.card_filter_add_card_filter_not (s := Z)
    (fun z => ∑ k, c k * z k ≠ 0)
  omega

lemma freq_bound {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    {γ τ ζ : Type} [Finite γ] (g : γ → E) (tag : γ → τ) (Z : Finset ζ) (act : ζ → τ → Prop)
    [∀ z t, Decidable (act z t)] (Out : τ → Prop)
    (hhalf : ∀ t, Out t → 2 * (Z.filter (fun z => act z t)).card = Z.card) :
    Z.card * Module.finrank K (Submodule.span K (g '' {k | Out (tag k)})) ≤
      2 * ∑ z ∈ Z, Module.finrank K (Submodule.span K (g '' {k | act z (tag k)})) := by
  classical
  obtain ⟨κ, a, hinj, hspan, hli⟩ :=
    exists_linearIndependent' K (fun k : {k : γ // Out (tag k)} => g k.1)
  have : Finite κ := Finite.of_injective a hinj
  have := Fintype.ofFinite κ
  have hrange : Set.range (fun k : {k : γ // Out (tag k)} => g k.1) = g '' {k | Out (tag k)} := by
    ext v
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hcard : Module.finrank K (Submodule.span K (g '' {k | Out (tag k)})) = Fintype.card κ := by
    rw [← hrange, ← hspan]
    exact finrank_span_eq_card hli
  have hz : ∀ z ∈ Z, (Finset.univ.filter (fun x : κ => act z (tag (a x).1))).card ≤
      Module.finrank K (Submodule.span K (g '' {k | act z (tag k)})) := by
    intro z _
    have hli' : LinearIndependent K
        (fun x : {x : κ // act z (tag (a x).1)} => g (a x.1).1) :=
      hli.comp Subtype.val Subtype.val_injective
    have h1 := finrank_span_eq_card hli'
    rw [Fintype.card_subtype] at h1
    rw [← h1]
    apply Submodule.finrank_mono
    apply Submodule.span_mono
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact ⟨(a x).1, hx, rfl⟩
  calc Z.card * Module.finrank K (Submodule.span K (g '' {k | Out (tag k)}))
      = ∑ _x : κ, Z.card := by rw [hcard]; simp [mul_comm]
    _ = ∑ x : κ, 2 * (Z.filter (fun z => act z (tag (a x).1))).card := by
        refine Finset.sum_congr rfl (fun x _ => (hhalf _ (a x).2).symm)
    _ = 2 * ∑ z ∈ Z, (Finset.univ.filter (fun x : κ => act z (tag (a x).1))).card := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ 2 * ∑ z ∈ Z, Module.finrank K (Submodule.span K (g '' {k | act z (tag k)})) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum hz)

lemma abs_rank {K : Type} [Field K] {Y Z A V B : Type}
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z] [AddCommGroup A] [Module K A]
    [AddCommGroup V] [Module K V] [AddCommGroup B] [Module K B]
    (f : Y →ₗ[K] Z) (p : Z →ₗ[K] A) (k : V →ₗ[K] Y) (k' : B →ₗ[K] Y)
    (h1 : ∀ v, p (f (k v)) = 0) (h2 : ∀ w, f (k' w) = 0) :
    Module.finrank K (LinearMap.range (f ∘ₗ k)) + Module.finrank K (LinearMap.range (p ∘ₗ f))
      + Module.finrank K (LinearMap.range k') ≤ Module.finrank K Y := by
  have e1 := LinearMap.finrank_range_add_finrank_ker (p ∘ₗ f)
  have e2 := LinearMap.finrank_range_add_finrank_ker (f.domRestrict (LinearMap.ker (p ∘ₗ f)))
  have e3 : Module.finrank K (LinearMap.range (f ∘ₗ k)) ≤
      Module.finrank K (LinearMap.range (f.domRestrict (LinearMap.ker (p ∘ₗ f)))) := by
    apply Submodule.finrank_mono
    rintro _ ⟨v, rfl⟩
    exact ⟨⟨k v, by simpa using h1 v⟩, rfl⟩
  have e4 : Module.finrank K (LinearMap.range k') ≤
      Module.finrank K (LinearMap.ker (f.domRestrict (LinearMap.ker (p ∘ₗ f)))) := by
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.ker (p ∘ₗ f))
      (LinearMap.ker (f.domRestrict (LinearMap.ker (p ∘ₗ f))))]
    apply Submodule.finrank_mono
    rintro _ ⟨w, rfl⟩
    refine ⟨⟨k' w, by simp [h2 w]⟩, ?_, rfl⟩
    simp [h2 w]
  omega

lemma two_sided_rank {K : Type} [Field K] {ι I J A B : Type} [Fintype ι] [Fintype I] [Fintype J]
    [Fintype A] [Fintype B]
    (R : ι → Matrix I J K) (r : A → I) (s : B → J)
    (hr : ∀ a y, (∑ j, R j) (r a) y = 0) (hs : ∀ x b, (∑ j, R j) x (s b) = 0) :
    (∑ j, R j).rank
      + Module.finrank K (Submodule.span K
          (Set.range (fun k : ι × J => fun a => R k.1 (r a) k.2)))
      + Module.finrank K (Submodule.span K
          (Set.range (fun k : ι × I => fun b => R k.1 k.2 (s b))))
      ≤ ∑ j, (R j).rank := by
  classical
  let Y : Type := ∀ j : ι, LinearMap.range (R j).mulVecLin
  let f : Y →ₗ[K] (I → K) :=
    ∑ j, (LinearMap.range (R j).mulVecLin).subtype ∘ₗ LinearMap.proj j
  let kk : (J → K) →ₗ[K] Y := LinearMap.pi (fun j => (R j).mulVecLin.rangeRestrict)
  let p : (I → K) →ₗ[K] (A → K) := LinearMap.funLeft K K r
  let ιs : (B → K) →ₗ[K] (J → K) := Fintype.linearCombination K (fun b => Pi.single (s b) (1 : K))
  have hf : ∀ y : Y, f y = ∑ j, (y j : I → K) := by
    intro y
    show (∑ j, (LinearMap.range (R j).mulVecLin).subtype ∘ₗ LinearMap.proj j) y = _
    rw [LinearMap.sum_apply]
    rfl
  have hfk : ∀ v, f (kk v) = (∑ j, R j).mulVec v := by
    intro v
    rw [hf, Matrix.sum_mulVec]
    rfl
  have hιs : ∀ (M : Matrix I J K) (w : B → K) (x : I),
      (M.mulVec (ιs w)) x = ∑ b, M x (s b) * w b := by
    intro M w x
    simp only [ιs, Fintype.linearCombination_apply, Matrix.mulVec_sum, Finset.sum_apply,
      Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [mul_comm]
  have h1 : ∀ v, p (f (kk v)) = 0 := by
    intro v
    rw [hfk]
    funext a
    simp only [p, LinearMap.funLeft_apply, Pi.zero_apply, Matrix.mulVec, dotProduct]
    exact Finset.sum_eq_zero (fun y _ => by rw [hr a y, zero_mul])
  have h2 : ∀ w, f ((kk ∘ₗ ιs) w) = 0 := by
    intro w
    rw [LinearMap.comp_apply, hfk]
    funext x
    rw [hιs]
    exact Finset.sum_eq_zero (fun b _ => by rw [hs x b, zero_mul])
  have key := abs_rank f p kk (kk ∘ₗ ιs) h1 h2
  have c0 : Module.finrank K Y = ∑ j, (R j).rank := by
    rw [Module.finrank_pi_fintype]
    rfl
  have c1 : (∑ j, R j).rank = Module.finrank K (LinearMap.range (f ∘ₗ kk)) := by
    have : f ∘ₗ kk = (∑ j, R j).mulVecLin := LinearMap.ext (fun v => hfk v)
    rw [this]
    rfl
  have c2 : Module.finrank K (Submodule.span K
      (Set.range (fun k : ι × J => fun a => R k.1 (r a) k.2))) ≤
      Module.finrank K (LinearMap.range (p ∘ₗ f)) := by
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro _ ⟨⟨j, y⟩, rfl⟩
    refine ⟨Pi.single j ⟨(R j).mulVecLin (Pi.single y 1), LinearMap.mem_range_self _ _⟩, ?_⟩
    rw [LinearMap.comp_apply, hf, Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
      funext a
      simp [p]
    · intro j' _ hne
      rw [Pi.single_eq_of_ne hne]
      rfl
    · intro h
      exact absurd (Finset.mem_univ j) h
  have c3 : Module.finrank K (Submodule.span K
      (Set.range (fun k : ι × I => fun b => R k.1 k.2 (s b)))) ≤
      Module.finrank K (LinearMap.range (kk ∘ₗ ιs)) := by
    let C : Matrix (ι × I) B K := Matrix.of (fun k b => R k.1 k.2 (s b))
    let emb : Y →ₗ[K] (ι × I → K) :=
      LinearMap.pi (fun k => LinearMap.proj k.2 ∘ₗ
        (LinearMap.range (R k.1).mulVecLin).subtype ∘ₗ LinearMap.proj k.1)
    have hC : Submodule.span K (Set.range (fun k : ι × I => fun b => R k.1 k.2 (s b)))
        = Submodule.span K (Set.range C.row) := rfl
    have hCe : C.mulVecLin = emb ∘ₗ (kk ∘ₗ ιs) := by
      refine LinearMap.ext (fun w => ?_)
      funext k
      show C.mulVec w k = ((R k.1).mulVec (ιs w)) k.2
      rw [hιs]
      rfl
    rw [hC, ← Matrix.rank_eq_finrank_span_row]
    unfold Matrix.rank
    rw [hCe, LinearMap.range_comp]
    exact Submodule.finrank_map_le _ _
  omega

lemma bd_mul_apply {K : Type} [Field K] {l : ℕ} {m : Fin l → ℕ} {J : Type}
    (L : (i : Fin l) → Matrix (Fin (m i)) (Fin (m i)) K)
    (M : Matrix (Σ i : Fin l, Fin (m i)) J K) (i : Fin l) (a : Fin (m i)) (y : J) :
    (Matrix.blockDiagonal' L * M) ⟨i, a⟩ y = ∑ a', L i a a' * M ⟨i, a'⟩ y := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro a' _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hne), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma mul_bd_apply {K : Type} [Field K] {l : ℕ} {n : Fin l → ℕ} {I : Type}
    (T : (i : Fin l) → Matrix (Fin (n i)) (Fin (n i)) K)
    (M : Matrix I (Σ i : Fin l, Fin (n i)) K) (x : I) (i : Fin l) (b : Fin (n i)) :
    (M * Matrix.blockDiagonal' T) x ⟨i, b⟩ = ∑ b', M x ⟨i, b'⟩ * T i b' b := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp [Matrix.blockDiagonal'_apply_eq]
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro b' _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma unique_nonzero {q : ℕ} (S : Submodule (ZMod 2) (Fin q → ZMod 2))
    (hS : Module.finrank (ZMod 2) S ≤ 1) {u v : Fin q → ZMod 2} (hu : u ∈ S) (hv : v ∈ S)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) : u = v := by
  obtain ⟨w, hw⟩ := finrank_le_one_iff.mp hS
  obtain ⟨a, ha⟩ := hw ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hw ⟨v, hv⟩
  have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have ha' : (a • w : S).1 = u := congrArg Subtype.val ha
  have hb' : (b • w : S).1 = v := congrArg Subtype.val hb
  have ha1 : a = 1 := by
    apply key
    rintro rfl
    apply hu0
    rw [← ha']
    simp
  have hb1 : b = 1 := by
    apply key
    rintro rfl
    apply hv0
    rw [← hb']
    simp
  rw [← ha', ← hb', ha1, hb1]

lemma exists_dot_ne {q : ℕ} (u : Fin q → ZMod 2) (hu : u ≠ 0) :
    ∃ z : Fin q → ZMod 2, ∑ k, u k * z k ≠ 0 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hu
  refine ⟨Pi.single k 1, ?_⟩
  simpa [Pi.single_apply] using hk

theorem core (q l t : ℕ) (m n : Fin l → ℕ)
    (P : Fin l → Submodule (ZMod 2) (Fin q → ZMod 2))
    (hP : ∀ i j, i ≠ j →
      Module.finrank (ZMod 2) (P i ⊓ P j : Submodule (ZMod 2) (Fin q → ZMod 2)) ≤ 1)
    (Zs : Fin l → Finset (Fin q → ZMod 2))
    (hZs : ∀ i z, z ∈ Zs i ↔ ∀ u ∈ P i, ∑ k, u k * z k = 0)
    (D : (i : Fin l) → (Fin q → ZMod 2) → Matrix (Fin (m i)) (Fin (n i)) (ZMod 2))
    (R : Fin t → Matrix (Σ i : Fin l, Fin (m i)) (Σ i : Fin l, Fin (n i)) (ZMod 2))
    (c : Fin t → (Fin q → ZMod 2))
    (hD : ∀ i z, z ∈ Zs i → D i z = 0)
    (on : (Fin q → ZMod 2) → Finset (Fin t))
    (hon : ∀ z j, j ∈ on z ↔ ∑ k, c j k * z k ≠ 0)
    (eqs : (Fin q → ZMod 2) → Finset (Fin t))
    (heqs : ∀ u j, j ∈ eqs u ↔ c j = u)
    (hX : ∀ z, Matrix.blockDiagonal' (fun i => D i z) = ∑ j ∈ on z, R j) :
    ∃ (L : (i : Fin l) → Matrix (Fin (m i)) (Fin (m i)) (ZMod 2))
      (T : (i : Fin l) → Matrix (Fin (n i)) (Fin (n i)) (ZMod 2)),
      (∀ i, L i * L i = L i ∧ T i * T i = T i ∧
        (Zs i).card * ((m i - (L i).rank) + (n i - (T i).rank)) ≤
          2 * ∑ z ∈ Zs i, ((∑ j ∈ on z, (R j).rank)
            - (Matrix.blockDiagonal' (fun i => D i z)).rank)) ∧
      (∀ j, c j ≠ 0 → ∀ x y, (c j ∉ P x.1 ∨ c j ∉ P y.1) →
        (Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' T) x y = 0) ∧
      ∀ u : Fin q → ZMod 2, u ≠ 0 →
        ∃ E : (i : Fin l) → Matrix (Fin (m i)) (Fin (n i)) (ZMod 2),
          (∑ j ∈ eqs u, Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' T)
            = Matrix.blockDiagonal' E ∧
          ∀ i, u ∉ P i → E i = 0 := by
  classical
  let colgen : (i : Fin l) → (Fin t × (Σ i : Fin l, Fin (n i))) → (Fin (m i) → ZMod 2) :=
    fun i k a => R k.1 ⟨i, a⟩ k.2
  let rowgen : (i : Fin l) → (Fin t × (Σ i : Fin l, Fin (m i))) → (Fin (n i) → ZMod 2) :=
    fun i k b => R k.1 k.2 ⟨i, b⟩
  have hL := fun i => exists_proj (Submodule.span (ZMod 2) (colgen i '' {k | c k.1 ∉ P i}))
  have hT := fun i => exists_proj (Submodule.span (ZMod 2) (rowgen i '' {k | c k.1 ∉ P i}))
  choose L hLL hLU hLr using hL
  choose T' hTT hTW hTr using hT
  have K1 : ∀ i j, c j ∉ P i → ∀ a y, ∑ a', L i a a' * R j ⟨i, a'⟩ y = 0 := by
    intro i j hj a y
    have h := hLU i (colgen i (j, y)) (Submodule.subset_span ⟨(j, y), hj, rfl⟩)
    exact congrFun h a
  have K2 : ∀ i j, c j ∉ P i → ∀ x b, ∑ b', R j x ⟨i, b'⟩ * (T' i).transpose b' b = 0 := by
    intro i j hj x b
    have h := hTW i (rowgen i (j, x)) (Submodule.subset_span ⟨(j, x), hj, rfl⟩)
    have h2 : ∑ b', T' i b b' * R j x ⟨i, b'⟩ = 0 := congrFun h b
    rw [← h2]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Matrix.transpose_apply, mul_comm]
  have hG : ∀ j i a i' b,
      (Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose)) ⟨i, a⟩ ⟨i', b⟩
        = ∑ a', L i a a' * ∑ b', R j ⟨i, a'⟩ ⟨i', b'⟩ * (T' i').transpose b' b := by
    intro j i a i' b
    rw [Matrix.mul_assoc, bd_mul_apply]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [mul_bd_apply]
  have hP3 : ∀ j x y, (c j ∉ P x.1 ∨ c j ∉ P y.1) →
      (Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose)) x y = 0 := by
    intro j x y hxy
    obtain ⟨i, a⟩ := x
    obtain ⟨i', b⟩ := y
    rw [hG]
    rcases hxy with h | h
    · simp only [Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, K1 i j h, zero_mul, Finset.sum_const_zero]
    · exact Finset.sum_eq_zero (fun a' _ => by rw [K2 i' j h, mul_zero])
  refine ⟨L, fun i => (T' i).transpose, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hLL i, ?_, ?_⟩
    · rw [← Matrix.transpose_mul, hTT i]
    · have hLr' : m i - (L i).rank
          = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (colgen i '' {k | c k.1 ∉ P i})) := by
        have h := hLr i
        rw [Fintype.card_fin] at h
        omega
      have hTr' : n i - ((T' i).transpose).rank
          = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (rowgen i '' {k | c k.1 ∉ P i})) := by
        have h := hTr i
        rw [Fintype.card_fin] at h
        rw [Matrix.rank_transpose]
        omega
      have hhalf : ∀ j, c j ∉ P i →
          2 * ((Zs i).filter (fun z => j ∈ on z)).card = (Zs i).card := by
        intro j hj
        have h := half_active q (P i) (c j) hj (Zs i) (hZs i)
        rw [← h]
        congr 2
        exact Finset.filter_congr (fun z _ => hon z j)
      have fU := freq_bound (K := ZMod 2) (colgen i) Prod.fst (Zs i) (fun z j => j ∈ on z)
        (fun j => c j ∉ P i) hhalf
      have fW := freq_bound (K := ZMod 2) (rowgen i) Prod.fst (Zs i) (fun z j => j ∈ on z)
        (fun j => c j ∉ P i) hhalf
      have hloss : ∀ z ∈ Zs i,
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (colgen i '' {k | k.1 ∈ on z}))
            + Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (rowgen i '' {k | k.1 ∈ on z}))
          ≤ (∑ j ∈ on z, (R j).rank) - (Matrix.blockDiagonal' (fun i => D i z)).rank := by
        intro z hz
        have hDz := hD i z hz
        have hsum : (∑ j : on z, R j.1) = Matrix.blockDiagonal' (fun i => D i z) := by
          rw [hX z]
          exact Finset.sum_coe_sort (on z) R
        have hr : ∀ a y, (∑ j : on z, R j.1) (⟨i, a⟩ : Σ i : Fin l, Fin (m i)) y = 0 := by
          intro a y
          rw [hsum]
          obtain ⟨i', b⟩ := y
          by_cases hii : i = i'
          · subst hii
            rw [Matrix.blockDiagonal'_apply_eq, hDz]
            rfl
          · exact Matrix.blockDiagonal'_apply_ne _ _ _ hii
        have hs : ∀ x b, (∑ j : on z, R j.1) x (⟨i, b⟩ : Σ i : Fin l, Fin (n i)) = 0 := by
          intro x b
          rw [hsum]
          obtain ⟨i', a⟩ := x
          by_cases hii : i' = i
          · subst hii
            rw [Matrix.blockDiagonal'_apply_eq, hDz]
            rfl
          · exact Matrix.blockDiagonal'_apply_ne _ _ _ hii
        have h := two_sided_rank (fun j : on z => R j.1)
          (fun a : Fin (m i) => (⟨i, a⟩ : Σ i : Fin l, Fin (m i)))
          (fun b : Fin (n i) => (⟨i, b⟩ : Σ i : Fin l, Fin (n i))) hr hs
        rw [hsum] at h
        have hrk : (∑ j : on z, (R j.1).rank) = ∑ j ∈ on z, (R j).rank :=
          Finset.sum_coe_sort (on z) (fun j => (R j).rank)
        rw [hrk] at h
        have hU : Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (colgen i '' {k | k.1 ∈ on z})) ≤
            Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
              (Set.range (fun k : (on z) × (Σ i : Fin l, Fin (n i)) =>
                fun a : Fin (m i) => R k.1.1 ⟨i, a⟩ k.2))) := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨⟨j, y⟩, hj, rfl⟩
          exact Submodule.subset_span ⟨(⟨j, hj⟩, y), rfl⟩
        have hW : Module.finrank (ZMod 2)
            (Submodule.span (ZMod 2) (rowgen i '' {k | k.1 ∈ on z})) ≤
            Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
              (Set.range (fun k : (on z) × (Σ i : Fin l, Fin (m i)) =>
                fun b : Fin (n i) => R k.1.1 k.2 ⟨i, b⟩))) := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨⟨j, x⟩, hj, rfl⟩
          exact Submodule.subset_span ⟨(⟨j, hj⟩, x), rfl⟩
        omega
      rw [hLr', hTr', Nat.mul_add]
      calc _ ≤ 2 * ∑ z ∈ Zs i, Module.finrank (ZMod 2)
                (Submodule.span (ZMod 2) (colgen i '' {k | k.1 ∈ on z}))
              + 2 * ∑ z ∈ Zs i, Module.finrank (ZMod 2)
                (Submodule.span (ZMod 2) (rowgen i '' {k | k.1 ∈ on z})) :=
            Nat.add_le_add fU fW
        _ = 2 * ∑ z ∈ Zs i, (Module.finrank (ZMod 2)
                (Submodule.span (ZMod 2) (colgen i '' {k | k.1 ∈ on z}))
              + Module.finrank (ZMod 2)
                (Submodule.span (ZMod 2) (rowgen i '' {k | k.1 ∈ on z}))) := by
            rw [Finset.sum_add_distrib, Nat.mul_add]
        _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum hloss)
  · intro j _ x y hxy
    exact hP3 j x y hxy
  · intro u hu
    refine ⟨fun i => Matrix.of (fun a b => (∑ j ∈ eqs u,
      Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose))
        ⟨i, a⟩ ⟨i, b⟩), ?_, ?_⟩
    · refine Matrix.ext (fun x y => ?_)
      obtain ⟨i, a⟩ := x
      obtain ⟨i', b⟩ := y
      by_cases hii : i = i'
      · subst hii
        rw [Matrix.blockDiagonal'_apply_eq]
        rfl
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hii, Matrix.sum_apply]
        by_cases hmem : u ∈ P i ∧ u ∈ P i'
        · obtain ⟨z, hz⟩ := exists_dot_ne u hu
          have hsub : eqs u ⊆ on z := by
            intro j hj
            rw [hon]
            rw [heqs] at hj
            rw [hj]
            exact hz
          have hall : (∑ j ∈ on z,
              Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose))
              = Matrix.blockDiagonal' (fun i => L i * D i z * (T' i).transpose) := by
            rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul, hX z, Matrix.mul_sum,
              Matrix.sum_mul]
          have hsum0 : ∑ j ∈ on z,
              (Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose))
                ⟨i, a⟩ ⟨i', b⟩ = 0 := by
            rw [← Matrix.sum_apply, hall]
            exact Matrix.blockDiagonal'_apply_ne _ _ _ hii
          rw [← hsum0]
          apply Finset.sum_subset hsub
          intro j hj hne
          have hor : c j ∉ P i ∨ c j ∉ P i' := by
            by_contra hcon
            rw [not_or, not_not, not_not] at hcon
            apply hne
            rw [heqs]
            have hcj0 : c j ≠ 0 := by
              intro h0
              have h1 := (hon z j).mp hj
              rw [h0] at h1
              simp at h1
            exact unique_nonzero (P i ⊓ P i') (hP i i' hii) ⟨hcon.1, hcon.2⟩ ⟨hmem.1, hmem.2⟩
              hcj0 hu
          exact hP3 j ⟨i, a⟩ ⟨i', b⟩ hor
        · apply Finset.sum_eq_zero
          intro j hj
          rw [heqs] at hj
          have hor : c j ∉ P i ∨ c j ∉ P i' := by
            rw [hj]
            exact not_and_or.mp hmem
          exact hP3 j ⟨i, a⟩ ⟨i', b⟩ hor
    · intro i hi
      refine Matrix.ext (fun a b => ?_)
      show (∑ j ∈ eqs u,
        Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' (fun i => (T' i).transpose))
          ⟨i, a⟩ ⟨i, b⟩ = 0
      rw [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro j hj
      apply hP3
      left
      rw [heqs] at hj
      rw [hj]
      exact hi

end PEqualNP.Outside.L_lib_1076_aux

theorem PEqualNP.Outside.L_lib_1076 : (let F := ZMod 2
∀ (q l t : ℕ) (m n : Fin l → ℕ),
  let V := Fin q → F
  let I := Σ i : Fin l, Fin (m i)
  let J := Σ i : Fin l, Fin (n i)
  let dot := fun (u z : V) => ∑ k, u k * z k
  ∀ (P : Fin l → Submodule F V),
    (∀ i j, i ≠ j → Module.finrank F (P i ⊓ P j : Submodule F V) ≤ 1) →
    let zeroAt := fun i : Fin l => @Finset.filter V (fun z =>
      ∀ u ∈ P i, dot u z = 0) (Classical.decPred _) Finset.univ
    ∀ (D : (i : Fin l) → V → Matrix (Fin (m i)) (Fin (n i)) F)
      (R : Fin t → Matrix I J F) (c : Fin t → V),
      (∀ i z, z ∈ zeroAt i → D i z = 0) →
      let X := fun z : V => Matrix.blockDiagonal' (fun i => D i z)
      let on := fun z : V => Finset.univ.filter (fun j => dot (c j) z ≠ 0)
      let loss := fun z : V => (∑ j ∈ on z, (R j).rank) - (X z).rank
      (∀ z, X z = ∑ j ∈ on z, R j) →
      ∃ (L : (i : Fin l) → Matrix (Fin (m i)) (Fin (m i)) F)
        (T : (i : Fin l) → Matrix (Fin (n i)) (Fin (n i)) F),
        let G := fun j : Fin t => Matrix.blockDiagonal' L * R j * Matrix.blockDiagonal' T
        (∀ i, L i * L i = L i ∧ T i * T i = T i ∧
          (zeroAt i).card * ((m i - (L i).rank) + (n i - (T i).rank)) ≤
            2 * ∑ z ∈ zeroAt i, loss z) ∧
        (∀ j, c j ≠ 0 → ∀ x y, (c j ∉ P x.1 ∨ c j ∉ P y.1) → G j x y = 0) ∧
        ∀ u : V, u ≠ 0 →
          ∃ E : (i : Fin l) → Matrix (Fin (m i)) (Fin (n i)) F,
            (∑ j ∈ Finset.univ.filter (fun j => c j = u), G j) = Matrix.blockDiagonal' E ∧
            ∀ i, u ∉ P i → E i = 0) := by
  intro F q l t m n V I J dot P hP zeroAt D R c hD X on loss hX
  have hZ : ∀ i z, z ∈ zeroAt i ↔ ∀ u ∈ P i, ∑ k, u k * z k = 0 := by
    intro i z
    show z ∈ @Finset.filter V (fun z => ∀ u ∈ P i, dot u z = 0) (Classical.decPred _)
      Finset.univ ↔ _
    exact (@Finset.mem_filter V (fun z => ∀ u ∈ P i, dot u z = 0) (Classical.decPred _)
      Finset.univ z).trans (and_iff_right (Finset.mem_univ z))
  have hon : ∀ z j, j ∈ on z ↔ ∑ k, c j k * z k ≠ 0 := by
    intro z j
    show j ∈ Finset.univ.filter (fun j => dot (c j) z ≠ 0) ↔ _
    exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ j))
  exact PEqualNP.Outside.L_lib_1076_aux.core q l t m n P hP zeroAt hZ D R c hD on hon
    (fun u => Finset.univ.filter (fun j => c j = u))
    (fun u j => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ j))) hX
