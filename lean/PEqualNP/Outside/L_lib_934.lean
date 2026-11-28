import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_934_aux

abbrev F := ZMod 2

section Run
variable {W : Type*} [AddCommGroup W] [Module F W]

def step (T : Finset (List Bool)) (ask : List Bool → W →ₗ[F] F) (bias : List Bool → F) (x : W)
    (p : List Bool) : List Bool :=
  if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p

def runK (T : Finset (List Bool)) (ask : List Bool → W →ₗ[F] F) (bias : List Bool → F) (x : W) :
    ℕ → List Bool
  | 0 => []
  | k + 1 => step T ask bias x (runK T ask bias x k)

variable (T : Finset (List Bool)) (ask : List Bool → W →ₗ[F] F) (bias : List Bool → F)

theorem foldl_eq_runK (x : W) (k : ℕ) :
    (List.range k).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (ask p x + bias p ≠ 0)] else p) [] = runK T ask bias x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem runK_succ (x : W) (k : ℕ) :
    runK T ask bias x (k + 1) = step T ask bias x (runK T ask bias x k) := rfl

theorem runK_prefix_succ (x : W) (k : ℕ) : runK T ask bias x k <+: runK T ask bias x (k + 1) := by
  rw [runK_succ, step]
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem runK_prefix (x : W) {j k : ℕ} (h : j ≤ k) :
    runK T ask bias x j <+: runK T ask bias x k := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact List.prefix_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · exact (ih (by omega)).trans (runK_prefix_succ T ask bias x k)
    · obtain rfl : j = k + 1 := by omega
      exact List.prefix_refl _

theorem runK_stay (x : W) {j : ℕ} (h : runK T ask bias x j ∉ T) :
    ∀ k, j ≤ k → runK T ask bias x k = runK T ask bias x j := by
  intro k hk
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            rfl
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hj | hj
    · have e := ih (by omega)
      rw [runK_succ, e, step, if_neg h]
    · obtain rfl : j = k + 1 := by omega
      rfl

theorem runK_take_mem (x : W) (k : ℕ) :
    ∀ j < (runK T ask bias x k).length, (runK T ask bias x k).take j ∈ T := by
  induction k with
  | zero => intro j hj; simp [runK] at hj
  | succ k ih =>
    intro j hj
    rw [runK_succ, step] at hj ⊢
    split_ifs at hj ⊢ with hp
    · simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_ge j (runK T ask bias x k).length with hj' | hj'
      · rw [List.take_append_of_le_length hj'.le]
        exact ih j hj'
      · obtain rfl : j = (runK T ask bias x k).length := by omega
        simpa using hp
    · exact ih j hj

theorem runK_getElem (x : W) (k : ℕ) :
    ∀ j (hj : j < (runK T ask bias x k).length),
      (runK T ask bias x k)[j] =
        decide (ask ((runK T ask bias x k).take j) x + bias ((runK T ask bias x k).take j) ≠ 0) := by
  induction k with
  | zero => intro j hj; simp [runK] at hj
  | succ k ih =>
    intro j hj
    simp only [runK_succ, step] at hj ⊢
    split_ifs at hj ⊢ with hp
    · simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_ge j (runK T ask bias x k).length with hj' | hj'
      · rw [List.getElem_append_left hj', List.take_append_of_le_length hj'.le]
        exact ih j hj'
      · obtain rfl : j = (runK T ask bias x k).length := by omega
        simp
    · exact ih j hj

theorem runK_length_of_mem (x : W) (k : ℕ) (h : runK T ask bias x k ∈ T) :
    (runK T ask bias x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : runK T ask bias x k ∈ T
    · rw [runK_succ, step, if_pos hk]
      simp [ih hk]
    · rw [runK_succ, step, if_neg hk] at h
      exact absurd h hk

theorem runK_length_le (x : W) (k : ℕ) : (runK T ask bias x k).length ≤ k := by
  induction k with
  | zero => simp [runK]
  | succ k ih =>
    rw [runK_succ, step]; split_ifs
    · simp; omega
    · omega

theorem runK_card_not_mem (x : W) : runK T ask bias x T.card ∉ T := by
  intro h
  set p := runK T ask bias x T.card with hp
  have hlen := runK_length_of_mem T ask bias x T.card h
  have sub : (Finset.range (T.card + 1)).image (fun j => p.take j) ⊆ T := by
    intro q hq
    simp only [Finset.mem_image, Finset.mem_range] at hq
    obtain ⟨j, hj, rfl⟩ := hq
    rcases Nat.lt_or_ge j T.card with hj' | hj'
    · exact runK_take_mem T ask bias x T.card j (by omega)
    · obtain rfl : j = T.card := by omega
      rw [← hlen, List.take_length]; exact h
  have inj : Set.InjOn (fun j => p.take j) (Finset.range (T.card + 1) : Set ℕ) := by
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := congrArg List.length e
    have hl : p.length = T.card := hlen
    simp only [List.length_take] at this
    omega
  have := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn inj, Finset.card_range] at this
  omega

theorem final_prop (x : W) :
    runK T ask bias x T.card ∉ T ∧
      ∀ j < (runK T ask bias x T.card).length, (runK T ask bias x T.card).take j ∈ T :=
  ⟨runK_card_not_mem T ask bias x, runK_take_mem T ask bias x T.card⟩

end Run

theorem leaves_card_le (T R : Finset (List Bool))
    (hR : ∀ p ∈ R, p ∉ T ∧ ∀ j < p.length, p.take j ∈ T) : R.card ≤ T.card + 1 := by
  classical
  by_cases h0 : ([] : List Bool) ∈ T
  · set T' := T.filter (fun q => ∀ j < q.length, q.take j ∈ T) with hT'
    set C := (T' ×ˢ (Finset.univ : Finset Bool)).image (fun qb => qb.1 ++ [qb.2]) with hC
    have hCcard : C.card ≤ 2 * T'.card := by
      calc C.card ≤ (T' ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
        _ = 2 * T'.card := by simp [Finset.card_product, mul_comm]
    have child : ∀ p : List Bool, p ≠ [] → (∀ j < p.length, p.take j ∈ T) → p ∈ C := by
      intro p hp hpre
      have hl : 0 < p.length := List.length_pos_iff.mpr hp
      refine Finset.mem_image.mpr ⟨(p.dropLast, p.getLast hp), ?_, List.dropLast_append_getLast hp⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true, hT', Finset.mem_filter]
      have hd : p.dropLast = p.take (p.length - 1) := List.dropLast_eq_take
      refine ⟨?_, ?_⟩
      · rw [hd]; exact hpre _ (by omega)
      · intro j hj
        rw [hd, List.take_take]
        simp only [List.length_dropLast] at hj
        exact hpre _ (by omega)
    have sub : R ∪ T'.erase [] ⊆ C := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · obtain ⟨hpT, hpre⟩ := hR p hp
        exact child p (by rintro rfl; exact hpT h0) hpre
      · obtain ⟨hne, hpT'⟩ := Finset.mem_erase.mp hp
        exact child p hne (Finset.mem_filter.mp hpT').2
    have disj : Disjoint R (T'.erase []) := by
      rw [Finset.disjoint_left]
      intro p hp hp'
      exact (hR p hp).1 (Finset.mem_filter.mp (Finset.mem_of_mem_erase hp')).1
    have h1 := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint disj] at h1
    have h0' : ([] : List Bool) ∈ T' := Finset.mem_filter.mpr ⟨h0, by simp⟩
    have h2 := Finset.card_erase_of_mem h0'
    have h3 : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h4 : 1 ≤ T'.card := Finset.card_pos.mpr ⟨_, h0'⟩
    omega
  · have : R ⊆ {[]} := by
      intro p hp
      obtain ⟨_, hpre⟩ := hR p hp
      rcases p with _ | ⟨b, p⟩
      · simp
      · exact absurd (by simpa using hpre 0 (by simp)) h0
    have := Finset.card_le_card this
    simp at this; omega

section Leaf
variable {W : Type*} [AddCommGroup W] [Module F W]
variable (T : Finset (List Bool)) (ask : List Bool → W →ₗ[F] F) (bias : List Bool → F)

theorem f2_eq_of_decide (u v : F) (h : decide (u ≠ 0) = decide (v ≠ 0)) : u = v := by
  revert u v; decide

def dirs (p0 : List Bool) : Submodule F W :=
  ⨅ j : Fin p0.length, LinearMap.ker (ask (p0.take j))

theorem mem_dirs (p0 : List Bool) (y : W) :
    y ∈ dirs ask p0 ↔ ∀ j < p0.length, ask (p0.take j) y = 0 := by
  simp only [dirs, Submodule.mem_iInf, LinearMap.mem_ker]
  exact ⟨fun h j hj => h ⟨j, hj⟩, fun h j => h j j.2⟩

theorem leaf_shift (x0 y : W) (hy : y ∈ dirs ask (runK T ask bias x0 T.card)) :
    ∀ k ≤ T.card, runK T ask bias (x0 + y) k = runK T ask bias x0 k := by
  rw [mem_dirs] at hy
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [runK_succ, runK_succ, ih (by omega)]
    simp only [step]
    split_ifs with hp
    · have hpre : runK T ask bias x0 (k + 1) <+: runK T ask bias x0 T.card := runK_prefix T ask bias x0 hk
      rw [runK_succ, step, if_pos hp] at hpre
      have hl := hpre.length_le
      simp only [List.length_append, List.length_singleton] at hl
      have htake := List.prefix_iff_eq_take.mp ((List.prefix_append _ _).trans hpre)
      have h0 := hy (runK T ask bias x0 k).length (by omega)
      rw [← htake] at h0
      rw [map_add, h0, add_zero]
    · rfl

theorem leaf_sub (x0 x : W) (h : runK T ask bias x T.card = runK T ask bias x0 T.card) :
    x - x0 ∈ dirs ask (runK T ask bias x0 T.card) := by
  rw [mem_dirs]
  intro j hj
  have e1 := runK_getElem T ask bias x T.card j (by rw [h]; exact hj)
  have e0 := runK_getElem T ask bias x0 T.card j hj
  have : (runK T ask bias x T.card)[j]'(by rw [h]; exact hj) = (runK T ask bias x0 T.card)[j] := by
    simp only [h]
  rw [e1, e0] at this
  simp only [h] at this
  have := f2_eq_of_decide _ _ this
  rw [map_sub]
  linear_combination this

end Leaf

section Quarter
variable {W : Type*} [AddCommGroup W] [Module F W]

theorem quarter (V : Submodule F W) (Vf : Finset W) (hVf : ∀ s, s ∈ Vf ↔ s ∈ V)
    (α β μ : W →ₗ[F] F) (κ : F) (u v : W) (hu : u ∈ V) (hv : v ∈ V)
    (h1 : α u = 1) (h2 : β u = 0) (h3 : α v = 0) (h4 : β v = 1) :
    Vf.card ≤ 4 * (Vf.filter (fun s => α s * β s + μ s + κ ≠ 0)).card := by
  classical
  set q : W → F := fun s => α s * β s + μ s + κ with hq
  have key : ∀ s, q s + q (s + u) + q (s + v) + q (s + u + v) = 1 := by
    intro s
    simp only [hq, map_add, h1, h2, h3, h4]
    generalize α s = a, β s = b, μ s = m, μ u = mu, μ v = mv, κ = k
    revert a b m mu mv k; decide
  set A : W → Finset W := fun t => Vf.filter (fun s => q (s + t) ≠ 0) with hA
  have hA0 : ∀ t ∈ V, (A t).card ≤ (Vf.filter (fun s => q s ≠ 0)).card := by
    intro t ht
    apply Finset.card_le_card_of_injOn (fun s => s + t)
    · intro s hs
      simp only [hA, Finset.coe_filter, Set.mem_setOf_eq] at hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨(hVf _).mpr (V.add_mem ((hVf s).mp hs.1) ht), hs.2⟩
    · intro s _ s' _ e; simpa using e
  have cover : Vf ⊆ A 0 ∪ A u ∪ A v ∪ A (u + v) := by
    intro s hs
    have mem : ∀ t, q (s + t) ≠ 0 → s ∈ A t := fun t ht => Finset.mem_filter.mpr ⟨hs, ht⟩
    by_contra hn
    simp only [Finset.mem_union, not_or] at hn
    have f0 : q (s + 0) = 0 := by by_contra h; exact hn.1.1.1 (mem 0 h)
    have fu : q (s + u) = 0 := by by_contra h; exact hn.1.1.2 (mem u h)
    have fv : q (s + v) = 0 := by by_contra h; exact hn.1.2 (mem v h)
    have fuv : q (s + (u + v)) = 0 := by by_contra h; exact hn.2 (mem (u + v) h)
    have := key s
    rw [add_zero] at f0
    rw [← add_assoc] at fuv
    rw [f0, fu, fv, fuv] at this
    simp at this
  have c1 := Finset.card_le_card cover
  have c2 : (A 0 ∪ A u ∪ A v ∪ A (u + v)).card ≤
      (A 0).card + (A u).card + (A v).card + (A (u + v)).card := by
    have e1 := Finset.card_union_le (A 0 ∪ A u ∪ A v) (A (u + v))
    have e2 := Finset.card_union_le (A 0 ∪ A u) (A v)
    have e3 := Finset.card_union_le (A 0) (A u)
    omega
  have d0 := hA0 0 V.zero_mem
  have d1 := hA0 u hu
  have d2 := hA0 v hv
  have d3 := hA0 (u + v) (V.add_mem hu hv)
  show Vf.card ≤ 4 * (Vf.filter (fun s => q s ≠ 0)).card
  omega

theorem exists_uv (V : Submodule F W) (α β : W →ₗ[F] F)
    (ha : ∃ s ∈ V, α s ≠ 0) (hb : ∃ s ∈ V, β s ≠ 0) (hab : ∃ s ∈ V, α s + β s ≠ 0) :
    ∃ u ∈ V, ∃ v ∈ V, α u = 1 ∧ β u = 0 ∧ α v = 0 ∧ β v = 1 := by
  obtain ⟨s1, m1, e1⟩ := ha
  obtain ⟨s2, m2, e2⟩ := hb
  obtain ⟨s3, m3, e3⟩ := hab
  have fin : ∀ a1 b1 a2 b2 a3 b3 : F, a1 ≠ 0 → b2 ≠ 0 → a3 + b3 ≠ 0 →
      (∃ c1 c2 c3 : F, c1*a1+c2*a2+c3*a3 = 1 ∧ c1*b1+c2*b2+c3*b3 = 0) ∧
      (∃ c1 c2 c3 : F, c1*a1+c2*a2+c3*a3 = 0 ∧ c1*b1+c2*b2+c3*b3 = 1) := by decide
  obtain ⟨⟨c1, c2, c3, hu1, hu2⟩, ⟨d1, d2, d3, hv1, hv2⟩⟩ :=
    fin (α s1) (β s1) (α s2) (β s2) (α s3) (β s3) e1 e2 e3
  refine ⟨c1 • s1 + c2 • s2 + c3 • s3, ?_, d1 • s1 + d2 • s2 + d3 • s3, ?_, ?_, ?_, ?_, ?_⟩
  · exact V.add_mem (V.add_mem (V.smul_mem _ m1) (V.smul_mem _ m2)) (V.smul_mem _ m3)
  · exact V.add_mem (V.add_mem (V.smul_mem _ m1) (V.smul_mem _ m2)) (V.smul_mem _ m3)
  all_goals simp only [map_add, map_smul, smul_eq_mul]; assumption

end Quarter

section Fwd

theorem sum_filter_comm {α β : Type*} (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    ∑ a ∈ s, (t.filter (fun b => P a b)).card = ∑ b ∈ t, (s.filter (fun a => P a b)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

def vmap {n m : ℕ} (a b : Fin m → (Fin n → F) →ₗ[F] F) (J : Finset (Fin m)) :
    (Fin n → F) →ₗ[F] (↥J → Fin 2 → F) where
  toFun x := fun i v => if v = 0 then a i.val x else b i.val x
  map_add' x y := by
    funext i v; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r x := by
    funext i v; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem vmap_apply {n m : ℕ} (a b : Fin m → (Fin n → F) →ₗ[F] F) (J : Finset (Fin m)) (x) :
    vmap a b J x = fun (i : ↥J) (v : Fin 2) => if v = 0 then a i.val x else b i.val x := rfl

theorem fwd (n m e L : ℕ) (a b c : Fin m → (Fin n → F) →ₗ[F] F) (f g h : Fin m → F)
    (T : Finset (List Bool)) (ask : List Bool → (Fin n → F) →ₗ[F] F) (bias : List Bool → F)
    (pred : List Bool → Fin m → (Fin n → F) →ₗ[F] F) (off : List Bool → Fin m → F)
    (hT : T.card < L)
    (herr : ∀ x : Fin n → F, ((Finset.univ : Finset (Fin m)).filter (fun i =>
      (a i x + f i) * (b i x + g i) + c i x + h i ≠
        pred (runK T ask bias x T.card) i x + off (runK T ask bias x T.card) i)).card ≤ e) :
    ∃ (J : Finset (Fin m)) (pick : Fin m → (Fin n → F) →ₗ[F] F), J.card ≤ 4 * e ∧
      (∀ i ∈ J, pick i = 0) ∧ (∀ i ∉ J, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i) ∧
      ∃ (B : Submodule F (↥J → Fin 2 → F)) (P : ↥J → (↥J → Fin 2 → F) →ₗ[F] F) (d : ↥J → F),
        (∀ z ∈ B, ((Finset.univ : Finset ↥J).filter
          (fun i => z i 0 * z i 1 ≠ P i z + d i)).card ≤ e) ∧
        2 ^ n ≤ L * ((Finset.univ : Finset (Fin n → F)).filter (fun x =>
          @decide ((∀ i, pick i x = 0) ∧
            (fun (i : ↥J) (v : Fin 2) => if v = 0 then a i.val x else b i.val x) ∈ B)
            (Classical.propDecidable _) = true)).card := by
  classical
  set W := Fin n → F
  set rn : W → List Bool := fun x => runK T ask bias x T.card with hrn
  set R := (Finset.univ : Finset W).image rn with hRdef
  have hR : R.card ≤ T.card + 1 := leaves_card_le T R (by
    intro p hp
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
    exact final_prop T ask bias x)
  set leaf : List Bool → ℕ := fun p => ((Finset.univ : Finset W).filter (fun x => rn x = p)).card
  obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image R leaf
    ⟨_, Finset.mem_image_of_mem rn (Finset.mem_univ 0)⟩
  obtain ⟨x0, -, hx0⟩ := Finset.mem_image.mp hp0
  have hcardW : (Finset.univ : Finset W).card = 2 ^ n := by simp [W]
  have hsum : 2 ^ n ≤ R.card * leaf p0 := by
    rw [← hcardW, Finset.card_eq_sum_card_fiberwise (f := rn) (t := R)
      (fun x _ => Finset.mem_image_of_mem rn (Finset.mem_univ x))]
    have := Finset.sum_le_card_nsmul R leaf (leaf p0) hmax
    simpa [smul_eq_mul] using this

  set V : Submodule F W := dirs ask p0 with hV
  set Vf := (Finset.univ : Finset W).filter (fun s => s ∈ V) with hVf
  have memVf : ∀ s, s ∈ Vf ↔ s ∈ V := by intro s; simp [hVf]
  have hleaf : leaf p0 ≤ Vf.card := by
    apply Finset.card_le_card_of_injOn (fun x => x - x0)
    · intro x hx
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      rw [Finset.mem_coe, memVf, hV, ← hx0]
      exact leaf_sub T ask bias x0 x (hx.trans hx0.symm)
    · intro x _ y _ e; simpa using e
  have hshift : ∀ s ∈ V, rn (x0 + s) = p0 := by
    intro s hs
    have hx0' : runK T ask bias x0 T.card = p0 := hx0
    have := leaf_shift T ask bias x0 s (by rw [hx0']; exact hs) T.card le_rfl
    exact this.trans hx0'

  set μ : Fin m → W →ₗ[F] F := fun i =>
    (b i x0 + g i) • a i + (a i x0 + f i) • b i + c i - pred p0 i with hμ
  set κ : Fin m → F := fun i =>
    (a i x0 + f i) * (b i x0 + g i) + c i x0 + h i - pred p0 i x0 - off p0 i with hκ
  have hform : ∀ i s, (a i (x0 + s) + f i) * (b i (x0 + s) + g i) + c i (x0 + s) + h i ≠
      pred p0 i (x0 + s) + off p0 i ↔ a i s * b i s + μ i s + κ i ≠ 0 := by
    intro i s
    rw [← sub_ne_zero]
    apply Iff.of_eq; congr 1
    simp only [hμ, hκ, map_add, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  have herrV : ∀ s ∈ V, ((Finset.univ : Finset (Fin m)).filter
      (fun i => a i s * b i s + μ i s + κ i ≠ 0)).card ≤ e := by
    intro s hs
    have := herr (x0 + s)
    rw [show runK T ask bias (x0 + s) T.card = p0 from hshift s hs] at this
    simpa only [hform] using this

  set J := (Finset.univ : Finset (Fin m)).filter (fun i =>
    (∃ s ∈ V, a i s ≠ 0) ∧ (∃ s ∈ V, b i s ≠ 0) ∧ (∃ s ∈ V, a i s + b i s ≠ 0)) with hJ
  have hJcard : J.card ≤ 4 * e := by
    have hpos : 0 < Vf.card := Finset.card_pos.mpr ⟨0, (memVf 0).mpr V.zero_mem⟩
    have each : ∀ i ∈ J, Vf.card ≤ 4 * (Vf.filter (fun s => a i s * b i s + μ i s + κ i ≠ 0)).card := by
      intro i hi
      obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨u, hu, v, hv, e1, e2, e3, e4⟩ := exists_uv V (a i) (b i) h1 h2 h3
      exact quarter V Vf memVf (a i) (b i) (μ i) (κ i) u v hu hv e1 e2 e3 e4
    have s1 : J.card * Vf.card ≤ 4 * ∑ i ∈ J, (Vf.filter (fun s => a i s * b i s + μ i s + κ i ≠ 0)).card := by
      rw [Finset.mul_sum, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum each
    have s2 : ∑ i ∈ J, (Vf.filter (fun s => a i s * b i s + μ i s + κ i ≠ 0)).card ≤
        ∑ i, (Vf.filter (fun s => a i s * b i s + μ i s + κ i ≠ 0)).card :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ J)
    have s3 : ∑ i, (Vf.filter (fun s => a i s * b i s + μ i s + κ i ≠ 0)).card ≤ Vf.card * e := by
      rw [sum_filter_comm]
      have := Finset.sum_le_card_nsmul Vf (fun s => ((Finset.univ : Finset (Fin m)).filter
        (fun i => a i s * b i s + μ i s + κ i ≠ 0)).card) e (fun s hs => herrV s ((memVf s).mp hs))
      simpa [smul_eq_mul] using this
    have : J.card * Vf.card ≤ (4 * e) * Vf.card := by nlinarith
    exact Nat.le_of_mul_le_mul_right this hpos
  set pick : Fin m → W →ₗ[F] F := fun i =>
    if ∀ s ∈ V, a i s = 0 then a i else if ∀ s ∈ V, b i s = 0 then b i
    else if ∀ s ∈ V, a i s + b i s = 0 then a i + b i else 0 with hpick
  have pickJ : ∀ i ∈ J, pick i = 0 := by
    intro i hi
    obtain ⟨⟨s1, m1, e1⟩, ⟨s2, m2, e2⟩, ⟨s3, m3, e3⟩⟩ := (Finset.mem_filter.mp hi).2
    simp only [hpick]
    rw [if_neg (fun hh => e1 (hh s1 m1)), if_neg (fun hh => e2 (hh s2 m2)),
      if_neg (fun hh => e3 (hh s3 m3))]
  have pickNJ : ∀ i ∉ J, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i := by
    intro i hi
    have hn : ¬((∃ s ∈ V, a i s ≠ 0) ∧ (∃ s ∈ V, b i s ≠ 0) ∧ (∃ s ∈ V, a i s + b i s ≠ 0)) :=
      fun hh => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    simp only [hpick]
    split_ifs with q1 q2 q3
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      push Not at q1 q2 q3
      exact hn ⟨q1, q2, q3⟩
  have pickV : ∀ i, ∀ s ∈ V, pick i s = 0 := by
    intro i s hs
    simp only [hpick]
    split_ifs with q1 q2 q3
    · exact q1 s hs
    · exact q2 s hs
    · simpa using q3 s hs
    · rfl

  set vV : ↥V →ₗ[F] (↥J → Fin 2 → F) := (vmap a b J).comp V.subtype with hvV
  set B := LinearMap.range vV with hB
  obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective vV.rangeRestrict
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_rangeRestrict _))
  have hσz : ∀ z : ↥B, vmap a b J (σ z : W) = z := by
    intro z
    have := congrArg Subtype.val (LinearMap.congr_fun hσ z)
    simpa [hvV] using this
  have hext : ∀ j : ↥J, ∃ Pj : (↥J → Fin 2 → F) →ₗ[F] F,
      Pj.comp B.subtype = (-(μ j.val)).comp (V.subtype.comp σ) :=
    fun j => LinearMap.exists_extend _
  choose P hP using hext
  refine ⟨J, pick, hJcard, pickJ, pickNJ, B, P, fun j => -κ j.val, ?_, ?_⟩
  · intro z hz
    set s : W := (σ ⟨z, hz⟩ : W) with hs
    have hsV : s ∈ V := (σ ⟨z, hz⟩).2
    have hzs : vmap a b J s = z := hσz ⟨z, hz⟩
    have hPz : ∀ j, P j z = -(μ j.val s) := by
      intro j
      have := LinearMap.congr_fun (hP j) ⟨z, hz⟩
      simpa using this
    calc ((Finset.univ : Finset ↥J).filter (fun j => z j 0 * z j 1 ≠ P j z + -κ j.val)).card
        = (((Finset.univ : Finset ↥J).filter (fun j => z j 0 * z j 1 ≠ P j z + -κ j.val)).map
            (Function.Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ ((Finset.univ : Finset (Fin m)).filter
            (fun i => a i s * b i s + μ i s + κ i ≠ 0)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coe_subtype] at hi
          obtain ⟨j, hj, rfl⟩ := hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hPz j, ← hzs] at hj
          simp only [vmap_apply, if_true, show ((1 : Fin 2) = 0) = False from by decide,
            if_false, if_true] at hj
          intro h0; apply hj; linear_combination h0
      _ ≤ e := herrV s hsV
  · calc 2 ^ n ≤ R.card * leaf p0 := hsum
      _ ≤ L * Vf.card := Nat.mul_le_mul (by omega) hleaf
      _ ≤ _ := by
          apply Nat.mul_le_mul_left
          apply Finset.card_le_card
          intro s hs
          have hsV := (memVf s).mp hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
          refine ⟨fun i => pickV i s hsV, ?_⟩
          rw [← vmap_apply, hB]
          exact ⟨⟨s, hsV⟩, rfl⟩

end Fwd

section Bwd

theorem geom_two (r : ℕ) : ∑ j ∈ Finset.range r, 2 ^ j + 1 = 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem f2_sq (t : F) : t * t = t := by revert t; decide

theorem bwd (n m e L : ℕ) (a b c : Fin m → (Fin n → F) →ₗ[F] F) (f g h : Fin m → F)
    (J : Finset (Fin m)) (pick : Fin m → (Fin n → F) →ₗ[F] F)
    (hJ0 : ∀ i ∈ J, pick i = 0) (hJp : ∀ i ∉ J, pick i = a i ∨ pick i = b i ∨ pick i = a i + b i)
    (B : Submodule F (↥J → Fin 2 → F)) (P : ↥J → (↥J → Fin 2 → F) →ₗ[F] F) (d : ↥J → F)
    (hB : ∀ z ∈ B, ((Finset.univ : Finset ↥J).filter
          (fun i => z i 0 * z i 1 ≠ P i z + d i)).card ≤ e)
    (hL : 2 ^ n ≤ L * ((Finset.univ : Finset (Fin n → F)).filter (fun x =>
          @decide ((∀ i, pick i x = 0) ∧
            (fun (i : ↥J) (v : Fin 2) => if v = 0 then a i.val x else b i.val x) ∈ B)
            (Classical.propDecidable _) = true)).card) :
    ∃ (T : Finset (List Bool)) (ask : List Bool → (Fin n → F) →ₗ[F] F) (bias : List Bool → F)
      (pred : List Bool → Fin m → (Fin n → F) →ₗ[F] F) (off : List Bool → Fin m → F),
      T.card < L ∧ ∀ x : Fin n → F, ((Finset.univ : Finset (Fin m)).filter (fun i =>
        (a i x + f i) * (b i x + g i) + c i x + h i ≠
          pred (runK T ask bias x T.card) i x + off (runK T ask bias x T.card) i)).card ≤ e := by
  classical
  set W := Fin n → F
  set vm := vmap a b J with hvm
  set K : Submodule F W := (⨅ i, LinearMap.ker (pick i)) ⊓ B.comap vm with hK
  have memK : ∀ x, x ∈ K ↔ (∀ i, pick i x = 0) ∧ vm x ∈ B := by
    intro x
    simp [hK, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_comap]
  set Kf := (Finset.univ : Finset W).filter (fun x => x ∈ K) with hKf
  have hL' : 2 ^ n ≤ L * Kf.card := by
    refine hL.trans (le_of_eq ?_)
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, hKf, memK, hvm,
      vmap_apply]
  have hKcard : Kf.card = 2 ^ Module.finrank F K := by
    have h1 : Kf.card = Fintype.card ↥K := by
      rw [hKf, ← Fintype.card_subtype]
    rw [h1, Module.card_eq_pow_finrank (K := F)]; simp
  set r := Module.finrank F (W ⧸ K) with hr
  have hrn : r + Module.finrank F K = n := by
    rw [hr, Submodule.finrank_quotient_add_finrank]; exact Module.finrank_fin_fun F
  have hKpos : 0 < Kf.card := by rw [hKcard]; positivity
  have h2r : 2 ^ r ≤ L := by
    have : 2 ^ r * Kf.card ≤ L * Kf.card := by
      rw [hKcard, ← pow_add, hrn]; rw [hKcard] at hL'; exact hL'
    exact Nat.le_of_mul_le_mul_right this hKpos

  set π : W →ₗ[F] (Fin r → F) :=
    (Module.finBasis F (W ⧸ K)).equivFun.toLinearMap ∘ₗ K.mkQ with hπ
  have kerπ : ∀ x, π x = 0 → x ∈ K := by
    intro x hx
    simp only [hπ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff] at hx
    exact (Submodule.Quotient.mk_eq_zero K).mp hx

  set T : Finset (List Bool) := (Finset.range r).biUnion
    (fun j => (Finset.univ : Finset (Fin j → Bool)).image List.ofFn) with hT
  have memT : ∀ p, p ∈ T ↔ p.length < r := by
    intro p
    simp only [hT, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, w, rfl⟩; simpa using hj
    · intro hp; exact ⟨p.length, hp, p.get, List.ofFn_get p⟩
  have hTlt : T.card < L := by
    have : T.card ≤ ∑ j ∈ Finset.range r, 2 ^ j := by
      apply (Finset.card_biUnion_le).trans
      apply Finset.sum_le_sum
      intro j _
      apply (Finset.card_image_le).trans
      simp
    have := geom_two r
    omega
  have hTge : r ≤ T.card := by
    have sub : (Finset.range r).image (fun j => List.replicate j false) ⊆ T := by
      intro p hp
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
      rw [memT]; simpa using hj
    have inj : Set.InjOn (fun j => List.replicate j false) (Finset.range r : Set ℕ) := by
      intro i _ j _ e; simpa using congrArg List.length e
    have := Finset.card_le_card sub
    rwa [Finset.card_image_of_injOn inj, Finset.card_range] at this
  set ask : List Bool → W →ₗ[F] F := fun p =>
    if hp : p.length < r then (LinearMap.proj (R := F) (φ := fun _ : Fin r => F) ⟨p.length, hp⟩).comp π
    else 0 with hask
  set bias : List Bool → F := fun _ => 0 with hbias
  set bits : W → ℕ → Bool := fun x j => if hj : j < r then decide (π x ⟨j, hj⟩ ≠ 0) else false
    with hbits
  have runK_eq : ∀ x k, runK T ask bias x k = (List.range (min k r)).map (bits x) := by
    intro x k
    induction k with
    | zero => simp [runK]
    | succ k ih =>
      rw [runK_succ, ih, step]
      by_cases hk : k < r
      · have hm : min k r = k := by omega
        have hm' : min (k + 1) r = k + 1 := by omega
        rw [if_pos (by rw [memT]; simp [hm, hk]), hm', List.range_succ, List.map_append, hm]
        simp [hask, hbias, hbits, hk]
      · have hm : min k r = r := by omega
        have hm' : min (k + 1) r = r := by omega
        rw [if_neg (by rw [memT]; simp [hm]), hm', hm]
  have run_eq : ∀ x, runK T ask bias x T.card = (List.range r).map (bits x) := by
    intro x; rw [runK_eq, show min T.card r = r by omega]

  set rep : List Bool → W := fun p =>
    if hp : ∃ x, runK T ask bias x T.card = p then hp.choose else 0 with hrep
  have rep_spec : ∀ x, x - rep (runK T ask bias x T.card) ∈ K := by
    intro x
    have hex : ∃ y, runK T ask bias y T.card = runK T ask bias x T.card := ⟨x, rfl⟩
    have h0 : runK T ask bias (rep (runK T ask bias x T.card)) T.card = runK T ask bias x T.card := by
      simp only [hrep, dif_pos hex]; exact hex.choose_spec
    set x0 := rep (runK T ask bias x T.card)
    rw [run_eq, run_eq, List.map_inj_left] at h0
    apply kerπ
    funext j
    have := h0 j.val (List.mem_range.mpr j.2)
    simp only [hbits, dif_pos j.2] at this
    have e := f2_eq_of_decide _ _ this
    simp [map_sub, e]

  set pred : List Bool → Fin m → W →ₗ[F] F := fun p i =>
    if hi : i ∈ J then (P ⟨i, hi⟩).comp vm + (b i (rep p) + g i) • a i + (a i (rep p) + f i) • b i + c i
    else if pick i = a i then (a i (rep p) + f i) • b i + c i
    else if pick i = b i then (b i (rep p) + g i) • a i + c i
    else ((a i (rep p) + f i) - (b i (rep p) + g i) - 1) • b i + c i with hpred
  set off : List Bool → Fin m → F := fun p i =>
    if hi : i ∈ J then d ⟨i, hi⟩ + (a i (rep p) + f i) * (b i (rep p) + g i) + h i -
        (P ⟨i, hi⟩ (vm (rep p)) + (b i (rep p) + g i) * a i (rep p) + (a i (rep p) + f i) * b i (rep p))
    else if pick i = a i then (a i (rep p) + f i) * g i + h i
    else if pick i = b i then (b i (rep p) + g i) * f i + h i
    else (a i (rep p) + f i) * (b i (rep p) + g i) -
      ((a i (rep p) + f i) - (b i (rep p) + g i) - 1) * b i (rep p) + h i with hoff
  refine ⟨T, ask, bias, pred, off, hTlt, ?_⟩
  intro x
  set p := runK T ask bias x T.card
  set x0 := rep p
  set k := x - x0 with hk
  have hkK := rep_spec x
  rw [← hk, memK] at hkK
  obtain ⟨hpk, hvk⟩ := hkK
  have hx : x = x0 + k := by rw [hk]; abel
  calc ((Finset.univ : Finset (Fin m)).filter (fun i =>
        (a i x + f i) * (b i x + g i) + c i x + h i ≠ pred p i x + off p i)).card
      ≤ (((Finset.univ : Finset ↥J).filter
          (fun j => vm k j 0 * vm k j 1 ≠ P j (vm k) + d j)).map (Function.Embedding.subtype _)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Function.Embedding.coe_subtype]
        by_cases hiJ : i ∈ J
        · refine ⟨⟨i, hiJ⟩, ?_, rfl⟩
          intro heq
          apply hi
          have e0 : vm k ⟨i, hiJ⟩ 0 = a i k := by simp [hvm, vmap_apply]
          have e1 : vm k ⟨i, hiJ⟩ 1 = b i k := by simp [hvm, vmap_apply]
          rw [e0, e1] at heq
          simp only [hpred, hoff, dif_pos hiJ, LinearMap.add_apply, LinearMap.comp_apply,
            LinearMap.smul_apply, smul_eq_mul]
          rw [hx]
          simp only [map_add]
          linear_combination heq
        · exfalso
          apply hi
          have hz := hpk i
          by_cases hpa : pick i = a i
          · rw [hpa] at hz
            simp only [hpred, hoff, dif_neg hiJ, if_pos hpa, LinearMap.add_apply,
              LinearMap.smul_apply, smul_eq_mul]
            rw [hx]; simp only [map_add]
            linear_combination (b i x0 + b i k + g i) * hz
          · by_cases hpb : pick i = b i
            · rw [hpb] at hz
              simp only [hpred, hoff, dif_neg hiJ, if_neg hpa, if_pos hpb, LinearMap.add_apply,
                LinearMap.smul_apply, smul_eq_mul]
              rw [hx]; simp only [map_add]
              linear_combination (a i x0 + a i k + f i) * hz
            · have hpab : pick i = a i + b i := by
                rcases hJp i hiJ with h1 | h1 | h1
                · exact absurd h1 hpa
                · exact absurd h1 hpb
                · exact h1
              rw [hpab, LinearMap.add_apply] at hz
              simp only [hpred, hoff, dif_neg hiJ, if_neg hpa, if_neg hpb, LinearMap.add_apply,
                LinearMap.smul_apply, smul_eq_mul]
              rw [hx]; simp only [map_add]
              linear_combination (b i x0 + g i + b i k) * hz - f2_sq (b i k)
    _ = ((Finset.univ : Finset ↥J).filter
          (fun j => vm k j 0 * vm k j 1 ≠ P j (vm k) + d j)).card := Finset.card_map _
    _ ≤ e := hB _ hvk

end Bwd

end PEqualNP.Outside.L_lib_934_aux

open PEqualNP.Outside.L_lib_934_aux in
theorem PEqualNP.Outside.L_lib_934 : (∀ (n m e L : Nat),
  let F := ZMod 2
  let W := Fin n → F
  let D := W →ₗ[F] F
  let I := Fin m
  let H := List Bool
  ∀ (a b c : I → D) (f g h : I → F),
    let target := fun (x : W) (i : I) => (a i x+f i)*(b i x+g i)+c i x+h i
    let run := fun (T : Finset H) (ask : H → D) (bias : H → F) (x : W) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (ask p x+bias p ≠ 0)] else p) []
    (∃ (T : Finset H) (ask : H → D) (bias : H → F) (pred : H → I → D) (off : H → I → F),
      T.card < L ∧ ∀ x : W,
        let p := run T ask bias x
        ((Finset.univ : Finset I).filter (fun i => target x i ≠ pred p i x+off p i)).card ≤ e) ↔
    ∃ (J : Finset I) (pick : I → D), J.card ≤ 4*e ∧
      (∀ i ∈ J, pick i = 0) ∧
      (∀ i ∉ J, pick i = a i ∨ pick i = b i ∨ pick i = a i+b i) ∧
      let Z := ↥J → Fin 2 → F
      let value := fun (x : W) (i : ↥J) (v : Fin 2) => if v = 0 then a i.val x else b i.val x
      ∃ (B : Submodule F Z) (P : ↥J → Z →ₗ[F] F) (d : ↥J → F),
        (∀ z ∈ B, ((Finset.univ : Finset ↥J).filter
          (fun i => z i 0*z i 1 ≠ P i z+d i)).card ≤ e) ∧
        2^n ≤ L * ((Finset.univ : Finset W).filter
          (fun x => @decide ((∀ i, pick i x = 0) ∧ value x ∈ B) (Classical.propDecidable _) = true)).card) := by
  intro n m e L F W D I H a b c f g h target run
  have hrun : ∀ T ask bias x, run T ask bias x = runK T ask bias x T.card :=
    fun T ask bias x => foldl_eq_runK T ask bias x T.card
  constructor
  · rintro ⟨T, ask, bias, pred, off, hT, herr⟩
    refine fwd n m e L a b c f g h T ask bias pred off hT (fun x => ?_)
    have := herr x
    simp only [hrun] at this
    exact this
  · rintro ⟨J, pick, -, hJ0, hJp, B, P, d, hB, hL⟩
    obtain ⟨T, ask, bias, pred, off, hT, herr⟩ := bwd n m e L a b c f g h J pick hJ0 hJp B P d hB hL
    refine ⟨T, ask, bias, pred, off, hT, fun x => ?_⟩
    simp only [hrun]
    exact herr x
