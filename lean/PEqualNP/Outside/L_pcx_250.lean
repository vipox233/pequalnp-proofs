import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_250

/-- The position `d` steps after `r` on the cycle. -/
def pos (n w : ℕ) (hn : 0 < n) (r : Fin n) (d : Fin (w+1)) : Fin n :=
  ⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩

/-- The window of the word `x` that starts at `r`. -/
def window (n w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (r : Fin n) (d : Fin (w+1)) : Bool :=
  x (pos n w hn r d)

/-- The table of a word: in every row, exactly the pattern of its window. -/
def pins (n w : ℕ) (hn : 0 < n) (word : Fin n → Bool) (row : Fin n)
    (pat : Fin (w+1) → Bool) : Bool :=
  decide (pat = window n w hn word row)

/-- A table is feasible when some word passes every row. -/
def feasible (n w : ℕ) (hn : 0 < n) (tab : Fin n → (Fin (w+1) → Bool) → Bool) : Prop :=
  ∃ x : Fin n → Bool, ∀ i, tab i (window n w hn x i) = true

/-- The table in which every row shows the word of its owner. -/
def mix (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (v : Fin 3 → (Fin n → Bool))
    (r : Fin n) (pat : Fin (w+1) → Bool) : Bool :=
  pins n w hn (v (owner r)) r pat

def excess (k : Fin 3 → ℕ) (dim : ℕ) : ℕ := 2*dim - ∑ e : Fin 3, min dim (k e)

/-- The statement's `fits s E`, word for word. -/
def Fits (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (ternary : Bool)
    (s E : ℕ) : Prop :=
  let Word := Fin n → Bool
  let Pattern := Fin (w+1) → Bool
  let pos := fun (r : Fin n) (d : Fin (w+1)) =>
    (⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let window := fun (x : Word) (r : Fin n) (d : Fin (w+1)) => x (pos r d)
  let next := fun e : Fin 3 => e + 1
  let Msg := (e : Fin 3) → Fin (k e) → Bool
  let Table := Fin n → Pattern → Bool
  let pins := fun (word : Word) (row : Fin n) (pat : Pattern) => decide (pat = window word row)
  let V := fun (p : Fin 3) (q : ℕ) =>
      Sum ({r : Fin n // owner r = p} × Pattern)
        (Sum ((e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val)) (Fin q))
  let feasible := fun tableInput : Table => ∃ x : Word, ∀ i, tableInput i (window x i) = true
  let mix := fun (v : Fin 3 → Word) (r : Fin n) (pat : Pattern) => pins (v (owner r)) r pat
  let errors := fun accept : Table → Prop => (@Finset.filter Table
      (fun tab => (∃ v, tab = mix v) ∧ ¬feasible tab ∧ accept tab)
      (Classical.decPred _) Finset.univ).card
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
        (code : Word → Msg) (priv : Fin 3 → ℕ)
        (F : (p : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V p (priv p)))),
        let accepts := fun (tab : Table) (y : Msg) => ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
          PEqualNP.ProofComplexity.Satisfies
            (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => tab h.1.val h.2)
              (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
                y bit.1.val bit.2) a)) (↑(F p) : Set _)
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
        C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ s ∧
        (∀ x : Word,
          (∀ j, code x 0 j = (C.wires (List.ofFn x)).getD (outA j) false) ∧
          (∀ j, code x 1 j = (C.wires (List.ofFn x)).getD (outB j) false)) ∧
        (ternary = true → ∀ p, ∀ cl ∈ F p, cl.card ≤ 3) ∧
        (∀ T : Table, feasible T → ∃ y, accepts T y) ∧
        (∀ x : Word, accepts (pins x) (code x)) ∧ errors (fun queried => ∃ y, accepts queried y) ≤ E

/-- Collision count: if `f` takes its values in `S`, then the number of ordered pairs with
equal values is at least `|G| ^ 2 / |S|` (Cauchy-Schwarz over the fibres of `f`). -/
theorem fc_collide {G Y : Type*} [Fintype G] [DecidableEq Y] (f : G → Y) (S : Finset Y)
    (hS : ∀ g, f g ∈ S) :
    Fintype.card G ^ 2 ≤ S.card * ∑ g : G, ∑ h : G, (if f h = f g then 1 else 0) := by
  have h1 : Fintype.card G = ∑ y ∈ S, (Finset.univ.filter (fun g => f g = y)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun g _ => hS g)
  have h3 : ∀ g : G, ∑ h : G, (if f h = f g then 1 else 0)
      = (Finset.univ.filter (fun h => f h = f g)).card := by
    intro g
    rw [Finset.card_filter]
  have h2 : ∑ g : G, ∑ h : G, (if f h = f g then 1 else 0)
      = ∑ y ∈ S, (Finset.univ.filter (fun g => f g = y)).card ^ 2 := by
    rw [Finset.sum_congr rfl (fun g _ => h3 g)]
    rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := S) (fun g _ => hS g)]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    have h4 : ∀ g ∈ Finset.univ.filter (fun g => f g = y),
        (Finset.univ.filter (fun h => f h = f g)).card
          = (Finset.univ.filter (fun h => f h = y)).card := by
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]
    rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, sq]
  rw [h1, h2]
  exact sq_sum_le_card_mul_sum_sq

/-- Averaging over translations: a group `G` acts on `A` through the additive map `φ`, and `c`
takes its values in `S`. Then the pairs `(x, g)` with `c (x + φ g) = c x` number at least
`|A| * |G| / |S|`. -/
theorem fc_avg {A G Y : Type*} [AddCommGroup A] [AddCommGroup G] [Fintype A] [Fintype G]
    [DecidableEq Y] (φ : G → A) (hφ : ∀ g h, φ (g + h) = φ g + φ h) (c : A → Y)
    (S : Finset Y) (hS : ∀ x, c x ∈ S) :
    Fintype.card A * Fintype.card G ≤
      S.card * (Finset.univ.filter (fun p : A × G => c (p.1 + φ p.2) = c p.1)).card := by
  have hN0 : (Finset.univ.filter (fun p : A × G => c (p.1 + φ p.2) = c p.1)).card
      = ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0) := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
  have hN : ∀ h : G, ∑ x : A, ∑ g : G, (if c (x + φ g) = c (x + φ h) then 1 else 0)
      = ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0) := by
    intro h
    refine Fintype.sum_equiv (Equiv.addRight (φ h)) _ _ (fun x => ?_)
    refine Fintype.sum_equiv (Equiv.subRight h) _ _ (fun g => ?_)
    have e1 : x + φ h + φ (g - h) = x + φ g := by
      have e2 := hφ (g - h) h
      rw [sub_add_cancel] at e2
      rw [e2]
      abel
    simp only [Equiv.coe_addRight, Equiv.subRight_apply, e1]
  have hsum : ∑ x : A, ∑ h : G, ∑ g : G, (if c (x + φ g) = c (x + φ h) then 1 else 0)
      = Fintype.card G * ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun h _ => hN h)]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hcs : ∀ x : A, Fintype.card G ^ 2
      ≤ S.card * ∑ h : G, ∑ g : G, (if c (x + φ g) = c (x + φ h) then 1 else 0) :=
    fun x => fc_collide (fun g => c (x + φ g)) S (fun g => hS _)
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have key : Fintype.card A * Fintype.card G ^ 2
      ≤ S.card * (Fintype.card G * ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0)) := by
    rw [← hsum, Finset.mul_sum]
    calc Fintype.card A * Fintype.card G ^ 2 = ∑ _x : A, Fintype.card G ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => hcs x)
  rw [hN0]
  have key2 : (Fintype.card A * Fintype.card G) * Fintype.card G
      ≤ (S.card * ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0)) * Fintype.card G := by
    calc (Fintype.card A * Fintype.card G) * Fintype.card G
        = Fintype.card A * Fintype.card G ^ 2 := by ring
      _ ≤ S.card * (Fintype.card G * ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0)) := key
      _ = (S.card * ∑ x : A, ∑ g : G, (if c (x + φ g) = c x then 1 else 0)) * Fintype.card G := by
          ring
  exact Nat.le_of_mul_le_mul_right key2 hG

/-- The kernel of a linear map into `k` coordinates is large (rank-nullity). -/
theorem fc_ker {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A] (k : ℕ)
    (lam : A →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    2 ^ (Module.finrank (ZMod 2) A - min (Module.finrank (ZMod 2) A) k) ≤
      Nat.card (LinearMap.ker lam) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker lam
  have h2 : Module.finrank (ZMod 2) (LinearMap.range lam) ≤ k := by
    have h := Submodule.finrank_le (LinearMap.range lam)
    rwa [Module.finrank_fin_fun] at h
  have h3 : Nat.card (LinearMap.ker lam)
      = 2 ^ Module.finrank (ZMod 2) (LinearMap.ker lam) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [h3]
  apply Nat.pow_le_pow_right (by norm_num)
  omega

/-- The count for a finite module `A` over `ZMod 2` (the flat itself, taken as the ambient
space). -/
theorem fc_module {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [Finite A] (k0 k1 k2 : ℕ)
    (lam0 : A →ₗ[ZMod 2] (Fin k0 → ZMod 2)) (lam1 : A →ₗ[ZMod 2] (Fin k1 → ZMod 2))
    {Y : Type} [Fintype Y] (hY : Fintype.card Y ≤ 2 ^ k2) (c : A → Y) :
    2 ^ (Module.finrank (ZMod 2) A + (2 * Module.finrank (ZMod 2) A -
        (min (Module.finrank (ZMod 2) A) k0 + min (Module.finrank (ZMod 2) A) k1 +
          min (Module.finrank (ZMod 2) A) k2))) ≤
      Set.ncard {t : A × A × A |
        lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1} := by
  classical
  have hFA : Fintype A := Fintype.ofFinite A
  have hA : Fintype.card A = 2 ^ Module.finrank (ZMod 2) A := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := A), ZMod.card]
  generalize hd : Module.finrank (ZMod 2) A = d at hA ⊢
  have hTfin : {t : A × A × A |
      lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1}.Finite := Set.toFinite _
  rcases Nat.lt_or_ge (2 * d) (min d k0 + min d k1 + min d k2) with hcase | hcase
  · -- the diagonal suffices
    have hE : d + (2 * d - (min d k0 + min d k1 + min d k2)) = d := by omega
    rw [hE, ← hA]
    have hinj : Set.InjOn (fun x : A => ((x, x, x) : A × A × A)) Set.univ :=
      fun x _ y _ h => (Prod.ext_iff.mp h).1
    have hmem : ∀ x ∈ (Set.univ : Set A), (fun x : A => ((x, x, x) : A × A × A)) x ∈
        {t : A × A × A |
          lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1} :=
      fun x _ => ⟨rfl, rfl, rfl⟩
    have hle := Set.ncard_le_ncard_of_injOn (fun x : A => ((x, x, x) : A × A × A))
      hmem hinj hTfin
    rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hle
    exact hle
  · -- the main case
    have hk0 := fc_ker k0 lam0
    have hk1 := fc_ker k1 lam1
    rw [hd, Nat.card_eq_fintype_card] at hk0 hk1
    have hφ : ∀ g h : LinearMap.ker lam0 × LinearMap.ker lam1,
        (fun p : LinearMap.ker lam0 × LinearMap.ker lam1 => (p.1 : A) + (p.2 : A)) (g + h)
          = (fun p : LinearMap.ker lam0 × LinearMap.ker lam1 => (p.1 : A) + (p.2 : A)) g
            + (fun p : LinearMap.ker lam0 × LinearMap.ker lam1 => (p.1 : A) + (p.2 : A)) h := by
      intro g h
      simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
      abel
    have hS : ∀ x, c x ∈ Finset.univ.image c :=
      fun x => Finset.mem_image_of_mem c (Finset.mem_univ x)
    have havg := fc_avg (fun p : LinearMap.ker lam0 × LinearMap.ker lam1 => (p.1 : A) + (p.2 : A))
      hφ c (Finset.univ.image c) hS
    have hScard : (Finset.univ.image c).card ≤ 2 ^ min d k2 := by
      have s1 : (Finset.univ.image c).card ≤ 2 ^ d := by
        rw [← hA, ← Finset.card_univ]
        exact Finset.card_image_le
      have s2 : (Finset.univ.image c).card ≤ 2 ^ k2 := (Finset.card_le_univ _).trans hY
      rcases le_total d k2 with h | h
      · rw [min_eq_left h]
        exact s1
      · rw [min_eq_right h]
        exact s2
    have hinj : Set.InjOn
        (fun p : A × (LinearMap.ker lam0 × LinearMap.ker lam1) =>
          ((p.1, p.1 + (p.2.1 : A), p.1 + (p.2.1 : A) + (p.2.2 : A)) : A × A × A))
        (↑(Finset.univ.filter (fun p : A × (LinearMap.ker lam0 × LinearMap.ker lam1) =>
          c (p.1 + ((p.2.1 : A) + (p.2.2 : A))) = c p.1))) := by
      rintro ⟨x, a, b⟩ - ⟨x', a', b'⟩ - h
      simp only [Prod.mk.injEq] at h
      obtain ⟨e1, e2, e3⟩ := h
      subst e1
      have ha : a = a' := Subtype.ext (add_left_cancel e2)
      subst ha
      have hb : b = b' := Subtype.ext (add_left_cancel e3)
      subst hb
      rfl
    have hle := Set.ncard_le_ncard_of_injOn
      (s := (↑(Finset.univ.filter (fun p : A × (LinearMap.ker lam0 × LinearMap.ker lam1) =>
          c (p.1 + ((p.2.1 : A) + (p.2.2 : A))) = c p.1)) : Set _))
      (fun p : A × (LinearMap.ker lam0 × LinearMap.ker lam1) =>
          ((p.1, p.1 + (p.2.1 : A), p.1 + (p.2.1 : A) + (p.2.2 : A)) : A × A × A))
      (by
        intro p hp
        have hp2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
        refine ⟨?_, ?_, ?_⟩
        · show lam0 p.1 = lam0 (p.1 + (p.2.1 : A))
          rw [map_add, LinearMap.mem_ker.mp p.2.1.2, add_zero]
        · show lam1 (p.1 + (p.2.1 : A)) = lam1 (p.1 + (p.2.1 : A) + (p.2.2 : A))
          rw [map_add lam1 (p.1 + (p.2.1 : A)), LinearMap.mem_ker.mp p.2.2.2, add_zero]
        · show c (p.1 + (p.2.1 : A) + (p.2.2 : A)) = c p.1
          rw [add_assoc]
          exact hp2)
      hinj hTfin
    rw [Set.ncard_coe_finset] at hle
    rw [Fintype.card_prod, hA] at havg
    have hfin : 2 ^ (d + (2 * d - (min d k0 + min d k1 + min d k2))) * 2 ^ min d k2
        ≤ Set.ncard {t : A × A × A |
            lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1} * 2 ^ min d k2 := by
      calc 2 ^ (d + (2 * d - (min d k0 + min d k1 + min d k2))) * 2 ^ min d k2
          = 2 ^ d * (2 ^ (d - min d k0) * 2 ^ (d - min d k1)) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1
            omega
        _ ≤ 2 ^ d * (Fintype.card (LinearMap.ker lam0) * Fintype.card (LinearMap.ker lam1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul hk0 hk1)
        _ ≤ (Finset.univ.image c).card *
              (Finset.univ.filter (fun p : A × (LinearMap.ker lam0 × LinearMap.ker lam1) =>
                c (p.1 + ((p.2.1 : A) + (p.2.2 : A))) = c p.1)).card := havg
        _ ≤ 2 ^ min d k2 * Set.ncard {t : A × A × A |
              lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1} :=
            Nat.mul_le_mul hScard hle
        _ = Set.ncard {t : A × A × A |
              lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c t.2.2 = c t.1} * 2 ^ min d k2 :=
            Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hfin (Nat.pos_of_ne_zero (by positivity))

/-- Matching triples inside one flat `a0 + L` on which two channels are affine (their linear
parts are `lam0` and `lam1`) and the third channel `c2` is any map into a set of at most
`2 ^ k2` values. -/
theorem flat_count (n k0 k1 k2 : ℕ) (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a0 : Fin n → ZMod 2)
    (lam0 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k0 → ZMod 2))
    (lam1 : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k1 → ZMod 2))
    {Y : Type} [Fintype Y] (hY : Fintype.card Y ≤ 2 ^ k2)
    (c2 : (Fin n → ZMod 2) → Y) :
    2 ^ (Module.finrank (ZMod 2) L + (2 * Module.finrank (ZMod 2) L -
        (min (Module.finrank (ZMod 2) L) k0 + min (Module.finrank (ZMod 2) L) k1 +
          min (Module.finrank (ZMod 2) L) k2))) ≤
      Set.ncard {t : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2) |
        t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L ∧
        lam0 t.1 = lam0 t.2.1 ∧ lam1 t.2.1 = lam1 t.2.2 ∧ c2 (a0 + t.2.2) = c2 (a0 + t.1)} := by
  have h := fc_module k0 k1 k2 (lam0.comp L.subtype) (lam1.comp L.subtype) hY
    (fun x : L => c2 (a0 + (x : Fin n → ZMod 2)))
  refine h.trans ?_
  refine Set.ncard_le_ncard_of_injOn
    (fun t : L × L × L => (((t.1 : Fin n → ZMod 2), (t.2.1 : Fin n → ZMod 2),
      (t.2.2 : Fin n → ZMod 2)) : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2)))
    ?_ ?_ (Set.toFinite _)
  · intro t ht
    exact ⟨t.1.2, t.2.1.2, t.2.2.2, ht.1, ht.2.1, ht.2.2⟩
  · rintro ⟨x, y, z⟩ - ⟨x', y', z'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    rw [Subtype.ext e1, Subtype.ext e2, Subtype.ext e3]

/- The wire lemmas below are adapted from the recorded proofs of L-meta-25647 and L-meta-25830
(Apache-2.0). -/

/-- The wire values of the gate list `gs` on the input bits `x`. -/
def tc_wiresOf (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem tc_wiresOf_length (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    (tc_wiresOf x gs).length = x.length + gs.length := by
  unfold tc_wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem tc_wiresOf_append (x : List Bool) (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) :
    tc_wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (tc_wiresOf x gs1) := by
  unfold tc_wiresOf
  rw [List.foldl_append]

theorem tc_foldl_append_start {A B : Type} (f : List A → B → A) (l : List B) (init : List A) :
    ∃ ext : List A, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem tc_wiresOf_append_getD_lt (x : List Bool)
    (gs1 gs2 : List PEqualNP.CircuitLowerBounds.Gate) {i : ℕ}
    (hi : i < x.length + gs1.length) :
    (tc_wiresOf x (gs1 ++ gs2)).getD i false = (tc_wiresOf x gs1).getD i false := by
  rw [tc_wiresOf_append]
  obtain ⟨ext, hext⟩ := tc_foldl_append_start
    (fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (tc_wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [tc_wiresOf_length]; exact hi)]

theorem tc_wiresOf_getD_input (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    {i : ℕ} (hi : i < x.length) :
    (tc_wiresOf x gs).getD i false = x.getD i false := by
  have h := tc_wiresOf_append_getD_lt x [] gs (by simpa using hi)
  simpa [tc_wiresOf] using h

theorem tc_wiresOf_getD_gate (x : List Bool) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (tc_wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (tc_wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [tc_wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [tc_wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (tc_wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [tc_wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [tc_wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [tc_wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

/-- A bit as an element of the two-element field. -/
def tc_b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem tc_b2z_decide : ∀ v : ZMod 2, tc_b2z (decide (v = 1)) = v := by decide

theorem tc_decide_b2z (b : Bool) : decide (tc_b2z b = 1) = b := by
  cases b <;> simp [tc_b2z]

theorem tc_b2z_inj {b c : Bool} (h : tc_b2z b = tc_b2z c) : b = c := by
  rw [← tc_decide_b2z b, ← tc_decide_b2z c, h]

theorem tc_z2_cases : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide

theorem tc_ev_and : ∀ u v : ZMod 2,
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.and
      [decide (u = 1), decide (v = 1)]) = u * v := by decide

theorem tc_ev_or : ∀ u v : ZMod 2,
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.or
      [decide (u = 1), decide (v = 1)]) = u + v + u * v := by decide

theorem tc_ev_mod0 :
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval (PEqualNP.CircuitLowerBounds.GateOp.mod 2)
      []) = 1 := by decide

theorem tc_ev_mod1 : ∀ u : ZMod 2,
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval (PEqualNP.CircuitLowerBounds.GateOp.mod 2)
      [decide (u = 1)]) = 1 + u := by decide

theorem tc_ev_mod2 : ∀ u v : ZMod 2,
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval (PEqualNP.CircuitLowerBounds.GateOp.mod 2)
      [decide (u = 1), decide (v = 1)]) = 1 + u + v := by decide

theorem tc_ev_not : ∀ u : ZMod 2,
    tc_b2z (PEqualNP.CircuitLowerBounds.GateOp.eval PEqualNP.CircuitLowerBounds.GateOp.not
      [decide (u = 1)]) = 1 + u := by decide

/-- Whether a gate is an AND or an OR gate. -/
noncomputable def tc_nl (g : PEqualNP.CircuitLowerBounds.Gate) : Bool :=
  @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
    g.op = PEqualNP.CircuitLowerBounds.GateOp.or) (Classical.propDecidable _)

theorem tc_nl_iff (g : PEqualNP.CircuitLowerBounds.Gate) :
    tc_nl g = true ↔ (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or) := by
  unfold tc_nl
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

/-- The word of bits of a vector over the two-element field. -/
def tc_bw {n : ℕ} (x : Fin n → ZMod 2) : Fin n → Bool := fun i => decide (x i = 1)

theorem tc_bw_injective (n : ℕ) :
    Function.Injective (fun x : Fin n → ZMod 2 => tc_bw x) := by
  intro x y h
  funext i
  have h1 : decide (x i = 1) = decide (y i = 1) := congrFun h i
  have h2 : tc_b2z (decide (x i = 1)) = tc_b2z (decide (y i = 1)) := congrArg tc_b2z h1
  rw [tc_b2z_decide, tc_b2z_decide] at h2
  exact h2

/-- The value of wire `i` of the gate list `gs` on the vector `x`. -/
def tc_wv (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (i : ℕ)
    (x : Fin n → ZMod 2) : ZMod 2 :=
  tc_b2z ((tc_wiresOf (List.ofFn (tc_bw x)) gs).getD i false)

theorem tc_wv_input (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) {i : ℕ} (h : i < n)
    (x : Fin n → ZMod 2) : tc_wv n gs i x = x ⟨i, h⟩ := by
  unfold tc_wv
  rw [tc_wiresOf_getD_input _ _ (by rw [List.length_ofFn]; exact h),
    List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact h), List.getElem_ofFn]
  exact tc_b2z_decide _

theorem tc_wv_past (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) {i : ℕ}
    (h : n + gs.length ≤ i) (x : Fin n → ZMod 2) : tc_wv n gs i x = 0 := by
  unfold tc_wv
  rw [List.getD_eq_default _ _ (by rw [tc_wiresOf_length, List.length_ofFn]; exact h)]
  simp [tc_b2z]

theorem tc_wv_gate (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) {j : ℕ}
    (hj : j < gs.length) (hrb : ∀ a ∈ (gs[j]).inputs, a < n + j) (x : Fin n → ZMod 2) :
    tc_wv n gs (n + j) x =
      tc_b2z ((gs[j]).op.eval ((gs[j]).inputs.map fun a => decide (tc_wv n gs a x = 1))) := by
  have h2 := tc_wiresOf_getD_gate (List.ofFn (tc_bw x)) gs hj
    (by
      intro a ha
      rw [List.length_ofFn]
      exact hrb a ha)
  rw [List.length_ofFn] at h2
  unfold tc_wv
  rw [h2]
  congr 2
  refine List.map_congr_left fun a _ => ?_
  exact (tc_decide_b2z _).symm

/-- The function `f` agrees on the flat `a0 + L` with a constant plus a linear map. -/
def tc_Aff {n : ℕ} (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∃ (phi : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (beta : ZMod 2),
    ∀ l ∈ L, f (a0 + l) = beta + phi l

theorem tc_Aff_const {n : ℕ} (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (c : ZMod 2) (f : (Fin n → ZMod 2) → ZMod 2) (hf : ∀ l ∈ L, f (a0 + l) = c) :
    tc_Aff a0 L f := by
  unfold tc_Aff
  refine ⟨0, c, fun l hl => ?_⟩
  rw [hf l hl, LinearMap.zero_apply, add_zero]

theorem tc_Aff_comb {n : ℕ} {a0 : Fin n → ZMod 2} {L : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {f g h : (Fin n → ZMod 2) → ZMod 2} (hf : tc_Aff a0 L f) (hg : tc_Aff a0 L g)
    (c0 c1 c2 : ZMod 2)
    (hh : ∀ l ∈ L, h (a0 + l) = c0 + c1 * f (a0 + l) + c2 * g (a0 + l)) :
    tc_Aff a0 L h := by
  obtain ⟨p1, b1, h1⟩ := hf
  obtain ⟨p2, b2, h2⟩ := hg
  unfold tc_Aff
  refine ⟨c1 • p1 + c2 • p2, c0 + c1 * b1 + c2 * b2, fun l hl => ?_⟩
  rw [hh l hl, h1 l hl, h2 l hl, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

theorem tc_Aff_mono {n : ℕ} {a0 : Fin n → ZMod 2}
    {L L' : Submodule (ZMod 2) (Fin n → ZMod 2)} {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : tc_Aff a0 L f) (hL : L' ≤ L) : tc_Aff a0 L' f := by
  obtain ⟨p, b, h⟩ := hf
  unfold tc_Aff
  exact ⟨p, b, fun l hl => h l (hL hl)⟩

theorem tc_Aff_shift {n : ℕ} {a0 l1 : Fin n → ZMod 2}
    {L L' : Submodule (ZMod 2) (Fin n → ZMod 2)} {f : (Fin n → ZMod 2) → ZMod 2}
    (hf : tc_Aff a0 L f) (hl1 : l1 ∈ L) (hL : L' ≤ L) : tc_Aff (a0 + l1) L' f := by
  obtain ⟨p, b, h⟩ := hf
  unfold tc_Aff
  refine ⟨p, b + p l1, fun l hl => ?_⟩
  rw [add_assoc, h (l1 + l) (L.add_mem hl1 (hL hl)), map_add, add_assoc]

theorem tc_gate_aff_lin (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) {j : ℕ}
    (hj : j < gs.length) (hrb : ∀ a ∈ (gs[j]).inputs, a < n + j)
    (hlin : ((gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.mod 2 ∧
        (gs[j]).inputs.length ≤ 2) ∨
      ((gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (gs[j]).inputs.length = 1))
    (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hAff : ∀ i, i < n + j → tc_Aff a0 L (tc_wv n gs i)) :
    tc_Aff a0 L (tc_wv n gs (n + j)) := by
  rcases hlin with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
  · rcases hin : (gs[j]).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · refine tc_Aff_const a0 L 1 _ (fun l _ => ?_)
      rw [tc_wv_gate n gs hj hrb, hop, hin]
      exact tc_ev_mod0
    · have ha : a < n + j := hrb a (by rw [hin]; simp)
      refine tc_Aff_comb (hAff a ha) (hAff a ha) 1 1 0 (fun l _ => ?_)
      rw [tc_wv_gate n gs hj hrb, hop, hin]
      refine (tc_ev_mod1 _).trans ?_
      ring
    · have ha : a < n + j := hrb a (by rw [hin]; simp)
      have hb : b < n + j := hrb b (by rw [hin]; simp)
      refine tc_Aff_comb (hAff a ha) (hAff b hb) 1 1 1 (fun l _ => ?_)
      rw [tc_wv_gate n gs hj hrb, hop, hin]
      refine (tc_ev_mod2 _ _).trans ?_
      ring
    · rw [hin] at hlen
      simp at hlen
  · obtain ⟨a, hin⟩ := List.length_eq_one_iff.mp hlen
    have ha : a < n + j := hrb a (by rw [hin]; simp)
    refine tc_Aff_comb (hAff a ha) (hAff a ha) 1 1 0 (fun l _ => ?_)
    rw [tc_wv_gate n gs hj hrb, hop, hin]
    refine (tc_ev_not _).trans ?_
    ring

theorem tc_gate_aff_nl (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) {j : ℕ}
    (hj : j < gs.length) (hrb : ∀ a ∈ (gs[j]).inputs, a < n + j)
    (hop : (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (gs[j]).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    {a b : ℕ} (hin : (gs[j]).inputs = [a, b])
    (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (beta : ZMod 2)
    (hconst : ∀ l ∈ L, tc_wv n gs a (a0 + l) = beta)
    (hb : tc_Aff a0 L (tc_wv n gs b)) :
    tc_Aff a0 L (tc_wv n gs (n + j)) := by
  rcases hop with hop | hop
  · refine tc_Aff_comb hb hb 0 beta 0 (fun l hl => ?_)
    rw [tc_wv_gate n gs hj hrb, hop, hin]
    refine (tc_ev_and _ _).trans ?_
    rw [hconst l hl]
    ring
  · refine tc_Aff_comb hb hb beta (1 + beta) 0 (fun l hl => ?_)
    rw [tc_wv_gate n gs hj hrb, hop, hin]
    refine (tc_ev_or _ _).trans ?_
    rw [hconst l hl]
    ring

theorem tc_extend (n : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (j : ℕ)
    (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (h : ∀ i, i < n + j → tc_Aff a0 L (tc_wv n gs i))
    (hg : tc_Aff a0 L (tc_wv n gs (n + j))) :
    ∀ i, i < n + (j + 1) → tc_Aff a0 L (tc_wv n gs i) := by
  intro i hi
  by_cases hi' : i < n + j
  · exact h i hi'
  · have e : i = n + j := by omega
    rw [e]
    exact hg

/-- The matching triples inside the flat `a0 + L`. -/
def tc_T {n k0 k1 : ℕ} {Y : Type} (fA : Fin k0 → (Fin n → ZMod 2) → ZMod 2)
    (fB : Fin k1 → (Fin n → ZMod 2) → ZMod 2) (c2 : (Fin n → ZMod 2) → Y)
    (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    Set ((Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2)) :=
  {t | t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L ∧
    (∀ j, fA j (a0 + t.1) = fA j (a0 + t.2.1)) ∧
    (∀ j, fB j (a0 + t.2.1) = fB j (a0 + t.2.2)) ∧
    c2 (a0 + t.2.2) = c2 (a0 + t.1)}

theorem tc_T_mem {n k0 k1 : ℕ} {Y : Type} {fA : Fin k0 → (Fin n → ZMod 2) → ZMod 2}
    {fB : Fin k1 → (Fin n → ZMod 2) → ZMod 2} {c2 : (Fin n → ZMod 2) → Y}
    {a0 : Fin n → ZMod 2} {L : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {t : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2)} :
    t ∈ tc_T fA fB c2 a0 L ↔ (t.1 ∈ L ∧ t.2.1 ∈ L ∧ t.2.2 ∈ L ∧
      (∀ j, fA j (a0 + t.1) = fA j (a0 + t.2.1)) ∧
      (∀ j, fB j (a0 + t.2.1) = fB j (a0 + t.2.2)) ∧
      c2 (a0 + t.2.2) = c2 (a0 + t.1)) := Iff.rfl

/-- The count inside a flat on which both channels are affine. -/
theorem tc_base {n k0 k1 : ℕ} {Y : Type} [Fintype Y]
    (fA : Fin k0 → (Fin n → ZMod 2) → ZMod 2) (fB : Fin k1 → (Fin n → ZMod 2) → ZMod 2)
    (c2 : (Fin n → ZMod 2) → Y) (a0 : Fin n → ZMod 2)
    (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (k2 : ℕ) (hY : Fintype.card Y ≤ 2 ^ k2)
    (hA : ∀ e, tc_Aff a0 L (fA e)) (hB : ∀ e, tc_Aff a0 L (fB e)) :
    2 ^ (Module.finrank (ZMod 2) L + (2 * Module.finrank (ZMod 2) L -
        (min (Module.finrank (ZMod 2) L) k0 + min (Module.finrank (ZMod 2) L) k1 +
          min (Module.finrank (ZMod 2) L) k2))) ≤ (tc_T fA fB c2 a0 L).ncard := by
  have hA' : ∀ e, ∃ (phi : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (beta : ZMod 2),
      ∀ l ∈ L, fA e (a0 + l) = beta + phi l := hA
  have hB' : ∀ e, ∃ (phi : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (beta : ZMod 2),
      ∀ l ∈ L, fB e (a0 + l) = beta + phi l := hB
  choose pA bA hpA using hA'
  choose pB bB hpB using hB'
  have h := flat_count n k0 k1 k2 L a0 (LinearMap.pi pA) (LinearMap.pi pB) hY c2
  refine h.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
  rintro t ⟨h1, h2, h3, h4, h5, h6⟩
  refine tc_T_mem.mpr ⟨h1, h2, h3, fun e => ?_, fun e => ?_, h6⟩
  · have h7 := congrFun h4 e
    rw [LinearMap.pi_apply, LinearMap.pi_apply] at h7
    rw [hpA e _ h1, hpA e _ h2, h7]
  · have h7 := congrFun h5 e
    rw [LinearMap.pi_apply, LinearMap.pi_apply] at h7
    rw [hpB e _ h2, hpB e _ h3, h7]

/-- Cutting a flat by a linear form that is not constant on it. -/
theorem tc_hyperplane {n : ℕ} (L : Submodule (ZMod 2) (Fin n → ZMod 2))
    (phi : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (l1 : Fin n → ZMod 2) (hl1 : l1 ∈ L)
    (h1 : phi l1 ≠ 0) :
    Module.finrank (ZMod 2) (L ⊓ LinearMap.ker phi : Submodule (ZMod 2) (Fin n → ZMod 2)) + 1 =
      Module.finrank (ZMod 2) L := by
  have hne : phi.comp L.subtype ≠ 0 := by
    intro h0
    apply h1
    have h2 := LinearMap.congr_fun h0 ⟨l1, hl1⟩
    simpa using h2
  have h3 := Module.Dual.finrank_ker_add_one_of_ne_zero hne
  rw [← h3, LinearMap.ker_comp, ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

/-- The two halves of a flat cut by a linear form embed disjointly. -/
theorem tc_split {n k0 k1 : ℕ} {Y : Type} (fA : Fin k0 → (Fin n → ZMod 2) → ZMod 2)
    (fB : Fin k1 → (Fin n → ZMod 2) → ZMod 2) (c2 : (Fin n → ZMod 2) → Y)
    (a0 : Fin n → ZMod 2) (L L' : Submodule (ZMod 2) (Fin n → ZMod 2)) (hL : L' ≤ L)
    (phi : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hphi : ∀ x ∈ L', phi x = 0)
    (l1 : Fin n → ZMod 2) (hl1 : l1 ∈ L) (h1 : phi l1 = 1) :
    (tc_T fA fB c2 a0 L').ncard + (tc_T fA fB c2 (a0 + l1) L').ncard ≤
      (tc_T fA fB c2 a0 L).ncard := by
  have hinj : Function.Injective
      (fun t : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2) =>
        ((l1 + t.1, l1 + t.2.1, l1 + t.2.2) :
          (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2))) := by
    intro t t' h
    have h' : ((l1 + t.1, l1 + t.2.1, l1 + t.2.2) :
        (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2)) =
        (l1 + t'.1, l1 + t'.2.1, l1 + t'.2.2) := h
    rw [Prod.mk.injEq, Prod.mk.injEq] at h'
    exact Prod.ext (add_left_cancel h'.1)
      (Prod.ext (add_left_cancel h'.2.1) (add_left_cancel h'.2.2))
  have hdisj : Disjoint (tc_T fA fB c2 a0 L')
      ((fun t : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2) =>
        ((l1 + t.1, l1 + t.2.1, l1 + t.2.2) :
          (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2))) ''
        tc_T fA fB c2 (a0 + l1) L') := by
    rw [Set.disjoint_left]
    rintro _ ht ⟨t', ht', rfl⟩
    have e1 : phi (l1 + t'.1) = 0 := hphi _ (tc_T_mem.mp ht).1
    have e2 : phi t'.1 = 0 := hphi _ (tc_T_mem.mp ht').1
    rw [map_add, h1, e2, add_zero] at e1
    exact one_ne_zero e1
  rw [← Set.ncard_image_of_injective (tc_T fA fB c2 (a0 + l1) L') hinj,
    ← Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  refine Set.ncard_le_ncard (Set.union_subset ?_ ?_) (Set.toFinite _)
  · intro t ht
    obtain ⟨h1', h2', h3', h4, h5, h6⟩ := tc_T_mem.mp ht
    exact tc_T_mem.mpr ⟨hL h1', hL h2', hL h3', h4, h5, h6⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨h1', h2', h3', h4, h5, h6⟩ := tc_T_mem.mp ht
    refine tc_T_mem.mpr ⟨L.add_mem hl1 (hL h1'), L.add_mem hl1 (hL h2'),
      L.add_mem hl1 (hL h3'), fun e => ?_, fun e => ?_, ?_⟩
    · have h := h4 e
      rw [add_assoc, add_assoc] at h
      exact h
    · have h := h5 e
      rw [add_assoc, add_assoc] at h
      exact h
    · rw [add_assoc, add_assoc] at h6
      exact h6

/-- The excess does not decrease with the dimension. -/
theorem tc_excess_mono (k : Fin 3 → ℕ) {d d' : ℕ} (h : d ≤ d') :
    excess k d ≤ excess k d' := by
  unfold excess
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  omega

theorem tc_pow_step (d X N N1 N2 : ℕ) (hd : 1 ≤ d) (h1 : 2 ^ (d - 1 + X) ≤ N1)
    (h2 : 2 ^ (d - 1 + X) ≤ N2) (h3 : N1 + N2 ≤ N) : 2 ^ (d + X) ≤ N := by
  have e : d + X = (d - 1 + X) + 1 := by omega
  rw [e, pow_succ]
  omega

/-- The count inside any flat on which the first wires are affine, by downward induction on
the number of gates already known to be affine there. -/
theorem tc_main (n : ℕ) (k : Fin 3 → ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hrb : ∀ (j : ℕ) (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < n + j)
    (hshape : ∀ g ∈ gs, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
    {Y : Type} [Fintype Y] (hY : Fintype.card Y ≤ 2 ^ k 2) (c2 : (Fin n → ZMod 2) → Y) :
    ∀ (m j : ℕ), j + m = gs.length →
      ∀ (a0 : Fin n → ZMod 2) (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (d : ℕ),
      Module.finrank (ZMod 2) L = d →
      (∀ i, i < n + j → tc_Aff a0 L (tc_wv n gs i)) →
      2 ^ (d + excess k (d - (gs.drop j).countP tc_nl)) ≤
        (tc_T (fun e => tc_wv n gs (outA e)) (fun e => tc_wv n gs (outB e)) c2 a0 L).ncard := by
  intro m
  induction m with
  | zero =>
    intro j hj a0 L d hd hAff
    have hj' : j = gs.length := by omega
    subst hj'
    subst hd
    rw [List.drop_length, List.countP_nil, Nat.sub_zero]
    have hall : ∀ i, tc_Aff a0 L (tc_wv n gs i) := by
      intro i
      by_cases hi : i < n + gs.length
      · exact hAff i hi
      · exact tc_Aff_const a0 L 0 _ (fun l _ => tc_wv_past n gs (by omega) _)
    have h := tc_base (fun e => tc_wv n gs (outA e)) (fun e => tc_wv n gs (outB e)) c2 a0 L
      (k 2) hY (fun e => hall _) (fun e => hall _)
    unfold excess
    rw [Fin.sum_univ_three]
    exact h
  | succ m ih =>
    intro j hj a0 L d hd hAff
    have hj' : j < gs.length := by omega
    have hrbj := hrb j hj'
    have hdrop : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj'
    rw [hdrop]
    rcases hshape gs[j] (List.getElem_mem hj') with ⟨hop, hlen⟩ | hlin
    · have hnl : tc_nl gs[j] = true := (tc_nl_iff _).mpr hop
      rw [List.countP_cons_of_pos hnl]
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      have ha : a < n + j := hrbj a (by rw [hab]; simp)
      have hb : b < n + j := hrbj b (by rw [hab]; simp)
      obtain ⟨phi, beta, hphi⟩ := hAff a ha
      by_cases hall : ∀ l ∈ L, phi l = 0
      · have hg : tc_Aff a0 L (tc_wv n gs (n + j)) :=
          tc_gate_aff_nl n gs hj' hrbj hop hab a0 L beta
            (fun l hl => by rw [hphi l hl, hall l hl, add_zero]) (hAff b hb)
        have r := ih (j + 1) (by omega) a0 L d hd (tc_extend n gs j a0 L hAff hg)
        exact le_trans (Nat.pow_le_pow_right (by norm_num)
          (Nat.add_le_add_left (tc_excess_mono k (by omega)) d)) r
      · obtain ⟨l1, hl1⟩ := not_forall.mp hall
        obtain ⟨hl1L, hl1phi⟩ := Classical.not_imp.mp hl1
        have h1 : phi l1 = 1 := (tc_z2_cases _).resolve_left hl1phi
        have hfr := tc_hyperplane L phi l1 hl1L hl1phi
        rw [hd] at hfr
        have hle : L ⊓ LinearMap.ker phi ≤ L := inf_le_left
        have hker : ∀ x ∈ L ⊓ LinearMap.ker phi, phi x = 0 :=
          fun x hx => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hx).2
        have hc1 : ∀ l ∈ L ⊓ LinearMap.ker phi, tc_wv n gs a (a0 + l) = beta := by
          intro l hl
          rw [hphi l (hle hl), hker l hl, add_zero]
        have hc2 : ∀ l ∈ L ⊓ LinearMap.ker phi, tc_wv n gs a (a0 + l1 + l) = beta + 1 := by
          intro l hl
          rw [add_assoc, hphi (l1 + l) (L.add_mem hl1L (hle hl)), map_add, h1,
            hker l hl, add_zero]
        have hA1 : ∀ i, i < n + j → tc_Aff a0 (L ⊓ LinearMap.ker phi) (tc_wv n gs i) :=
          fun i hi => tc_Aff_mono (hAff i hi) hle
        have hA2 : ∀ i, i < n + j →
            tc_Aff (a0 + l1) (L ⊓ LinearMap.ker phi) (tc_wv n gs i) :=
          fun i hi => tc_Aff_shift (hAff i hi) hl1L hle
        have hg1 := tc_gate_aff_nl n gs hj' hrbj hop hab a0 (L ⊓ LinearMap.ker phi) beta hc1
          (hA1 b hb)
        have hg2 := tc_gate_aff_nl n gs hj' hrbj hop hab (a0 + l1) (L ⊓ LinearMap.ker phi)
          (beta + 1) hc2 (hA2 b hb)
        have r1 := ih (j + 1) (by omega) a0 (L ⊓ LinearMap.ker phi) (d - 1) (by omega)
          (tc_extend n gs j a0 _ hA1 hg1)
        have r2 := ih (j + 1) (by omega) (a0 + l1) (L ⊓ LinearMap.ker phi) (d - 1) (by omega)
          (tc_extend n gs j (a0 + l1) _ hA2 hg2)
        have r3 := tc_split (fun e => tc_wv n gs (outA e)) (fun e => tc_wv n gs (outB e)) c2
          a0 L (L ⊓ LinearMap.ker phi) hle phi hker l1 hl1L h1
        have e1 : d - ((gs.drop (j + 1)).countP tc_nl + 1) =
            d - 1 - (gs.drop (j + 1)).countP tc_nl := by omega
        rw [e1]
        exact tc_pow_step d _ _ _ _ (by omega) r1 r2 r3
    · have hnl : ¬ (tc_nl gs[j] = true) := by
        intro h
        rcases hlin with ⟨hop, _⟩ | ⟨hop, _⟩
        · rcases (tc_nl_iff _).mp h with h' | h' <;> rw [hop] at h' <;> cases h'
        · rcases (tc_nl_iff _).mp h with h' | h' <;> rw [hop] at h' <;> cases h'
      rw [List.countP_cons_of_neg hnl]
      have hg := tc_gate_aff_lin n gs hj' hrbj hlin a0 L hAff
      exact ih (j + 1) (by omega) a0 L d hd (tc_extend n gs j a0 L hAff hg)

/-- Matching triples: at least this many when two of the three channels are computed with at
most `s` AND/OR gates. -/
theorem triangle_count (n s : ℕ) (k : Fin 3 → ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hshape : ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (hcount : C.gates.countP
      (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ s)
    (c2 : (Fin n → Bool) → Fin (k 2) → Bool) :
    2 ^ (n + excess k (n - s)) ≤
      (Finset.univ.filter (fun v : Fin 3 → (Fin n → Bool) =>
        (∀ j, (C.wires (List.ofFn (v 0))).getD (outA j) false =
          (C.wires (List.ofFn (v 1))).getD (outA j) false) ∧
        (∀ j, (C.wires (List.ofFn (v 1))).getD (outB j) false =
          (C.wires (List.ofFn (v 2))).getD (outB j) false) ∧
        c2 (v 2) = c2 (v 0))).card := by
  have hrb' : ∀ (j : ℕ) (hj : j < C.gates.length),
      ∀ a ∈ (C.gates[j]).inputs, a < n + j := by
    intro j hj a ha
    refine hrb j hj a ?_
    show a ∈ (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs
    rw [List.getD_eq_getElem _ _ hj]
    exact ha
  have hcount' : C.gates.countP tc_nl ≤ s := hcount
  have hY : Fintype.card (Fin (k 2) → Bool) ≤ 2 ^ k 2 := by simp
  have hAff0 : ∀ i, i < n + 0 →
      tc_Aff (0 : Fin n → ZMod 2) ⊤ (tc_wv n C.gates i) := by
    intro i hi
    have hi' : i < n := by omega
    unfold tc_Aff
    refine ⟨LinearMap.proj ⟨i, hi'⟩, 0, fun l _ => ?_⟩
    rw [zero_add, zero_add, tc_wv_input n C.gates hi']
    rfl
  have hmain := tc_main n k C.gates hrb' hshape outA outB hY (fun x => c2 (tc_bw x))
    C.gates.length 0 (by omega) 0 ⊤ n (by rw [finrank_top, Module.finrank_fin_fun]) hAff0
  rw [List.drop_zero] at hmain
  have hmono : 2 ^ (n + excess k (n - s)) ≤ 2 ^ (n + excess k (n - C.gates.countP tc_nl)) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.add_le_add_left (tc_excess_mono k (by omega)) n)
  have hinj : Function.Injective
      (fun t : (Fin n → ZMod 2) × (Fin n → ZMod 2) × (Fin n → ZMod 2) =>
        (![tc_bw t.1, tc_bw t.2.1, tc_bw t.2.2] : Fin 3 → (Fin n → Bool))) := by
    intro t t' h
    have h0 : tc_bw t.1 = tc_bw t'.1 := congrFun h 0
    have h1 : tc_bw t.2.1 = tc_bw t'.2.1 := congrFun h 1
    have h2 : tc_bw t.2.2 = tc_bw t'.2.2 := congrFun h 2
    exact Prod.ext (tc_bw_injective n h0)
      (Prod.ext (tc_bw_injective n h1) (tc_bw_injective n h2))
  refine le_trans (hmono.trans hmain) ?_
  rw [← Set.ncard_coe_finset, ← Set.ncard_image_of_injective _ hinj]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := tc_T_mem.mp ht
  rw [Finset.mem_coe, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun j => ?_, fun j => ?_, ?_⟩
  · have h := h4 j
    rw [zero_add, zero_add] at h
    exact tc_b2z_inj h
  · have h := h5 j
    rw [zero_add, zero_add] at h
    exact tc_b2z_inj h
  · rw [zero_add, zero_add] at h6
    exact h6

/-- A word that passes every row of a mixed table is the word of every party. -/
theorem lm_feasible_word (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (v : Fin 3 → (Fin n → Bool)) (x : Fin n → Bool)
    (hx : ∀ i, mix n w hn owner v i (window n w hn x i) = true) (p : Fin 3) : v p = x := by
  funext z
  obtain ⟨r, hr, d, hd⟩ := hcov p z
  have h1 : decide (window n w hn x r = window n w hn (v (owner r)) r) = true := hx r
  have h2 : window n w hn x r = window n w hn (v (owner r)) r := of_decide_eq_true h1
  have h3 : x (pos n w hn r d) = v (owner r) (pos n w hn r d) := congrFun h2 d
  rw [hd, hr] at h3
  exact h3.symm

/-- A feasible mixed table comes from three equal words. -/
theorem lm_feasible_diag (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (v : Fin 3 → (Fin n → Bool)) (hfe : feasible n w hn (mix n w hn owner v)) :
    v 0 = v 1 ∧ v 1 = v 2 := by
  obtain ⟨x, hx⟩ := hfe
  have h := lm_feasible_word n w hn owner hcov v x hx
  exact ⟨(h 0).trans (h 1).symm, (h 1).trans (h 2).symm⟩

/-- The mixed table determines the three words. -/
theorem lm_mix_inj (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (v v' : Fin 3 → (Fin n → Bool))
    (h : mix n w hn owner v = mix n w hn owner v') : v = v' := by
  funext p z
  obtain ⟨r, hr, d, hd⟩ := hcov p z
  have h0 : mix n w hn owner v r (window n w hn (v (owner r)) r) = true :=
    decide_eq_true rfl
  rw [h] at h0
  have h1 : decide (window n w hn (v (owner r)) r = window n w hn (v' (owner r)) r) = true :=
    h0
  have h2 : window n w hn (v (owner r)) r = window n w hn (v' (owner r)) r :=
    of_decide_eq_true h1
  have h3 : v (owner r) (pos n w hn r d) = v' (owner r) (pos n w hn r d) := congrFun h2 d
  rw [hd, hr] at h3
  exact h3

/-- Three words that are all equal are determined by the first one. -/
theorem lm_diag_inj (n : ℕ) (a b : Fin 3 → (Fin n → Bool))
    (ha : a 0 = a 1 ∧ a 1 = a 2) (hb : b 0 = b 1 ∧ b 1 = b 2) (hab : a 0 = b 0) : a = b := by
  have h3 : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  funext p
  rcases h3 p with rfl | rfl | rfl
  · exact hab
  · exact ha.1.symm.trans (hab.trans hb.1)
  · exact ha.2.symm.trans (ha.1.symm.trans (hab.trans (hb.1.trans hb.2)))

/-- On a matching triple, the message of channel `e` is the same for its two readers. -/
theorem lm_code_agree (n : ℕ) (k : Fin 3 → ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
    (code : (Fin n → Bool) → (e : Fin 3) → Fin (k e) → Bool)
    (hcode : ∀ x : Fin n → Bool,
      (∀ j, code x 0 j = (C.wires (List.ofFn x)).getD (outA j) false) ∧
      (∀ j, code x 1 j = (C.wires (List.ofFn x)).getD (outB j) false))
    (v : Fin 3 → (Fin n → Bool))
    (hA : ∀ j, (C.wires (List.ofFn (v 0))).getD (outA j) false =
      (C.wires (List.ofFn (v 1))).getD (outA j) false)
    (hB : ∀ j, (C.wires (List.ofFn (v 1))).getD (outB j) false =
      (C.wires (List.ofFn (v 2))).getD (outB j) false)
    (hC : code (v 2) 2 = code (v 0) 2) (e : Fin 3) (j : Fin (k e)) :
    code (v e) e j = code (v (e + 1)) e j := by
  have h3 : ∀ t : Fin 3, t = 0 ∨ t = 1 ∨ t = 2 := by decide
  rcases h3 e with rfl | rfl | rfl
  · have h01 : (0 : Fin 3) + 1 = 1 := by decide
    rw [h01, (hcode (v 0)).1 j, (hcode (v 1)).1 j]
    exact hA j
  · have h12 : (1 : Fin 3) + 1 = 2 := by decide
    rw [h12, (hcode (v 1)).2 j, (hcode (v 2)).2 j]
    exact hB j
  · have h20 : (2 : Fin 3) + 1 = 0 := by decide
    rw [h20]
    exact congrFun hC j

/-- Satisfaction only depends on the values of the assignment. -/
theorem lm_sat_congr {V : Type} (a b : V → Bool)
    (G : Set (PEqualNP.ProofComplexity.Clause V)) (hab : ∀ t, a t = b t)
    (hb : PEqualNP.ProofComplexity.Satisfies b G) : PEqualNP.ProofComplexity.Satisfies a G := by
  have hfun : a = b := funext hab
  rw [hfun]
  exact hb

/-- The mixed table of a matching triple is accepted. -/
theorem lm_accept (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
    (code : (Fin n → Bool) → (e : Fin 3) → Fin (k e) → Bool) (priv : Fin 3 → ℕ)
    (F : (p : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause
      (Sum ({r : Fin n // owner r = p} × (Fin (w+1) → Bool))
        (Sum ((e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val)) (Fin (priv p))))))
    (hcode : ∀ x : Fin n → Bool,
      (∀ j, code x 0 j = (C.wires (List.ofFn x)).getD (outA j) false) ∧
      (∀ j, code x 1 j = (C.wires (List.ofFn x)).getD (outB j) false))
    (hpins : ∀ (x : Fin n → Bool) (p : Fin 3), ∃ a : Fin (priv p) → Bool,
      PEqualNP.ProofComplexity.Satisfies
        (Sum.elim (fun h : {i : Fin n // owner i = p} × (Fin (w+1) → Bool) =>
            pins n w hn x h.1.val h.2)
          (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val) =>
            code x bit.1.val bit.2) a)) (↑(F p) : Set _))
    (v : Fin 3 → (Fin n → Bool))
    (hA : ∀ j, (C.wires (List.ofFn (v 0))).getD (outA j) false =
      (C.wires (List.ofFn (v 1))).getD (outA j) false)
    (hB : ∀ j, (C.wires (List.ofFn (v 1))).getD (outB j) false =
      (C.wires (List.ofFn (v 2))).getD (outB j) false)
    (hC : code (v 2) 2 = code (v 0) 2) :
    ∃ y : (e : Fin 3) → Fin (k e) → Bool, ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
      PEqualNP.ProofComplexity.Satisfies
        (Sum.elim (fun h : {i : Fin n // owner i = p} × (Fin (w+1) → Bool) =>
            mix n w hn owner v h.1.val h.2)
          (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val) =>
            y bit.1.val bit.2) a)) (↑(F p) : Set _) := by
  refine ⟨fun e => code (v e) e, fun p => ?_⟩
  obtain ⟨a, ha⟩ := hpins (v p) p
  refine ⟨a, lm_sat_congr _ _ _ ?_ ha⟩
  intro t
  rcases t with ⟨⟨r, hr⟩, pat⟩ | ⟨⟨e, he⟩, j⟩ | q
  · show mix n w hn owner v r pat = pins n w hn (v p) r pat
    unfold mix
    rw [hr]
  · show code (v e) e j = code (v p) e j
    rcases he with rfl | rfl
    · rfl
    · exact lm_code_agree n k C outA outB code hcode v hA hB hC e j
  · rfl

/-- The counting step: a set that maps injectively into `T` off a diagonal, and injectively
into `Z` on the diagonal, has at most `T.card + card Z` elements. -/
theorem lm_count {X Y Z : Type} [Fintype Z]
    (M : Finset X) (T : Finset Y) (f : X → Y) (g : X → Z) (D : X → Prop) (N E : ℕ)
    (hM : N ≤ M.card) (hT : T.card ≤ E)
    (hf : ∀ a ∈ M, ¬ D a → f a ∈ T) (hfinj : ∀ a b, f a = f b → a = b)
    (hg : ∀ a b, D a → D b → g a = g b → a = b) :
    N ≤ E + Fintype.card Z := by
  classical
  have h1 : (M.filter (fun a => ¬ D a)).card ≤ T.card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro a ha
      have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      exact Finset.mem_coe.mpr (hf a ha'.1 ha'.2)
    · intro a _ b _ hab
      exact hfinj a b hab
  have h2 : (M.filter D).card ≤ (Finset.univ : Finset Z).card := by
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro a _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro a ha b hb hab
      have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      exact hg a b ha'.2 hb'.2 hab
  rw [Finset.card_univ] at h2
  have h3 := Finset.card_filter_add_card_filter_not (s := M) D
  omega

/-- The lower bound, from the facts packed inside `Fits` (with the two counted sets taken as
arbitrary finite sets `M` and `T` that have the needed properties). -/
theorem lm_core (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (E N : ℕ)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
    (code : (Fin n → Bool) → (e : Fin 3) → Fin (k e) → Bool) (priv : Fin 3 → ℕ)
    (F : (p : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause
      (Sum ({r : Fin n // owner r = p} × (Fin (w+1) → Bool))
        (Sum ((e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val)) (Fin (priv p))))))
    (hcode : ∀ x : Fin n → Bool,
      (∀ j, code x 0 j = (C.wires (List.ofFn x)).getD (outA j) false) ∧
      (∀ j, code x 1 j = (C.wires (List.ofFn x)).getD (outB j) false))
    (hpins : ∀ (x : Fin n → Bool) (p : Fin 3), ∃ a : Fin (priv p) → Bool,
      PEqualNP.ProofComplexity.Satisfies
        (Sum.elim (fun h : {i : Fin n // owner i = p} × (Fin (w+1) → Bool) =>
            pins n w hn x h.1.val h.2)
          (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val) =>
            code x bit.1.val bit.2) a)) (↑(F p) : Set _))
    (M : Finset (Fin 3 → (Fin n → Bool))) (hM : N ≤ M.card)
    (T : Finset (Fin n → (Fin (w+1) → Bool) → Bool)) (herr : T.card ≤ E)
    (hMdef : ∀ v ∈ M,
      (∀ j, (C.wires (List.ofFn (v 0))).getD (outA j) false =
        (C.wires (List.ofFn (v 1))).getD (outA j) false) ∧
      (∀ j, (C.wires (List.ofFn (v 1))).getD (outB j) false =
        (C.wires (List.ofFn (v 2))).getD (outB j) false) ∧
      code (v 2) 2 = code (v 0) 2)
    (hT : ∀ tab : Fin n → (Fin (w+1) → Bool) → Bool,
      (∃ v, tab = mix n w hn owner v) → ¬ feasible n w hn tab →
      (∃ y : (e : Fin 3) → Fin (k e) → Bool, ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
        PEqualNP.ProofComplexity.Satisfies
          (Sum.elim (fun h : {i : Fin n // owner i = p} × (Fin (w+1) → Bool) =>
              tab h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val) =>
              y bit.1.val bit.2) a)) (↑(F p) : Set _)) → tab ∈ T) :
    N ≤ E + 2 ^ n := by
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := by
    rw [Fintype.card_pi_const, Fintype.card_bool]
  have hfin : N ≤ E + Fintype.card (Fin n → Bool) := by
    refine lm_count M T (mix n w hn owner) (fun v : Fin 3 → (Fin n → Bool) => v 0)
      (fun v : Fin 3 → (Fin n → Bool) => v 0 = v 1 ∧ v 1 = v 2) N E hM herr ?_ ?_ ?_
    · intro v hv hD
      obtain ⟨hA, hB, hC⟩ := hMdef v hv
      refine hT _ ⟨v, rfl⟩ ?_ ?_
      · intro hfe
        exact hD (lm_feasible_diag n w hn owner hcov v hfe)
      · exact lm_accept n w hn owner k C outA outB code priv F hcode hpins v hA hB hC
    · intro a b hab
      exact lm_mix_inj n w hn owner hcov a b hab
    · intro a b ha hb hab
      exact lm_diag_inj n a b ha hb hab
  rw [hcard] at hfin
  exact hfin

theorem lower_main (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (ternary : Bool) (s E : ℕ) (h : Fits n w hn owner k ternary s E) :
    2 ^ (n + excess k (n - s)) ≤ E + 2 ^ n := by
  unfold Fits at h
  obtain ⟨C, outA, outB, code, priv, F, hrb, hshape, hcount, hcode, htern, hcompl, hpins,
    herr⟩ := h
  have hM := triangle_count n s k C outA outB hrb hshape hcount (fun x => code x 2)
  refine lm_core n w hn owner hcov k E _ C outA outB code priv F hcode hpins _ hM _ herr ?_ ?_
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro tab h1 h2 h3
    exact (@Finset.mem_filter _ _ (_) _ _).mpr ⟨Finset.mem_univ _, h1, h2, h3⟩

/-- Where the bits copied by channel `e` start. -/
def up_off (n : ℕ) (k : Fin 3 → ℕ) (e : Fin 3) : ℕ :=
  if e = 0 then 0 else if e = 1 then min n (k 0) else min n (k 0) + min n (k 1)

/-- The coordinate copied by bit `j` of channel `e`. -/
def up_zc (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) (e : Fin 3) (j : ℕ) : Fin n :=
  ⟨(up_off n k e + j) % n, Nat.mod_lt _ hn⟩

/-- The wire read by bit `j` of channel `e`; wire `n` does not exist and reads false. -/
def up_out (n : ℕ) (k : Fin 3 → ℕ) (e : Fin 3) (j : ℕ) : ℕ :=
  if j < n then (up_off n k e + j) % n else n

/-- The messages of a word. -/
def up_code (n : ℕ) (k : Fin 3 → ℕ) (x : Fin n → Bool) (e : Fin 3) (j : Fin (k e)) : Bool :=
  (List.ofFn x).getD (up_out n k e j.val) false

theorem up_off_zero (n : ℕ) (k : Fin 3 → ℕ) : up_off n k 0 = 0 := rfl

theorem up_off_one (n : ℕ) (k : Fin 3 → ℕ) : up_off n k 1 = min n (k 0) := rfl

theorem up_off_two (n : ℕ) (k : Fin 3 → ℕ) : up_off n k 2 = min n (k 0) + min n (k 1) := rfl

theorem up_code_eq (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) (x : Fin n → Bool) (e : Fin 3)
    (j : Fin (k e)) (hj : j.val < n) :
    up_code n k x e j = x (up_zc n hn k e j.val) := by
  unfold up_code up_out up_zc
  rw [ite_eq_left hj]
  have h : (up_off n k e + j.val) % n < n := Nat.mod_lt _ hn
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left h]
  rfl

/-- Index type of the private variables: the bits of a guessed word, and the chain variables. -/
abbrev up_PV (n w : ℕ) : Type := Sum (Fin n) (Fin n × (Fin (w+1) → Bool) × Fin (w+2))

/-- The number of private variables. -/
def up_q (n w : ℕ) : ℕ := Fintype.card (up_PV n w)

/-- The numbering of the private variables. -/
noncomputable def up_en (n w : ℕ) : up_PV n w ≃ Fin (up_q n w) := Fintype.equivFin (up_PV n w)

/-- The variables of party `p`. -/
abbrev up_V (n w : ℕ) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3) : Type :=
  Sum ({r : Fin n // owner r = p} × (Fin (w+1) → Bool))
    (Sum ((e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val)) (Fin (up_q n w)))

/-- A table variable. -/
def up_Tv (n w : ℕ) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (r : {r : Fin n // owner r = p}) (pat : Fin (w+1) → Bool) : up_V n w owner k p :=
  Sum.inl (r, pat)

/-- A message variable. -/
def up_Mv (n w : ℕ) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (e : {t : Fin 3 // t = p ∨ t + 1 = p}) (j : Fin (k e.val)) : up_V n w owner k p :=
  Sum.inr (Sum.inl ⟨e, j⟩)

/-- A private variable. -/
noncomputable def up_Pv (n w : ℕ) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (i : up_PV n w) : up_V n w owner k p :=
  Sum.inr (Sum.inr (up_en n w i))

/-- The clause with the single literal `a`. -/
def up_c1 {V : Type} (a : V × Bool) : PEqualNP.ProofComplexity.Clause V :=
  {a}

/-- The clause with the literals `a`, `b`. -/
def up_c2 {V : Type} [DecidableEq V] (a b : V × Bool) : PEqualNP.ProofComplexity.Clause V :=
  {a, b}

/-- The clause with the literals `a`, `b`, `c`. -/
def up_c3 {V : Type} [DecidableEq V] (a b c : V × Bool) : PEqualNP.ProofComplexity.Clause V :=
  {a, b, c}

theorem up_c1_sat {V : Type} (A : V → Bool) (a : V × Bool) :
    PEqualNP.ProofComplexity.ClauseSat A (up_c1 a) ↔ A a.1 = a.2 := by
  unfold up_c1 PEqualNP.ProofComplexity.ClauseSat
  constructor
  · rintro ⟨l, hl, h⟩
    rw [Finset.mem_singleton] at hl
    subst hl
    exact h
  · intro h
    exact ⟨a, Finset.mem_singleton_self _, h⟩

theorem up_c2_sat {V : Type} [DecidableEq V] (A : V → Bool) (a b : V × Bool) :
    PEqualNP.ProofComplexity.ClauseSat A (up_c2 a b) ↔ A a.1 = a.2 ∨ A b.1 = b.2 := by
  unfold up_c2 PEqualNP.ProofComplexity.ClauseSat
  constructor
  · rintro ⟨l, hl, h⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨a, Finset.mem_insert_self _ _, h⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h⟩

theorem up_c3_sat {V : Type} [DecidableEq V] (A : V → Bool) (a b c : V × Bool) :
    PEqualNP.ProofComplexity.ClauseSat A (up_c3 a b c) ↔
      A a.1 = a.2 ∨ A b.1 = b.2 ∨ A c.1 = c.2 := by
  unfold up_c3 PEqualNP.ProofComplexity.ClauseSat
  constructor
  · rintro ⟨l, hl, h⟩
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact ⟨a, Finset.mem_insert_self _ _, h⟩
    · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨c, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
        h⟩

theorem up_c1_card {V : Type} (a : V × Bool) : (up_c1 a).card ≤ 3 := by
  unfold up_c1
  rw [Finset.card_singleton]
  exact Nat.le_succ_of_le (Nat.le_succ 1)

theorem up_c2_card {V : Type} [DecidableEq V] (a b : V × Bool) : (up_c2 a b).card ≤ 3 := by
  unfold up_c2
  exact le_trans Finset.card_le_two (Nat.le_succ 2)

theorem up_c3_card {V : Type} [DecidableEq V] (a b c : V × Bool) : (up_c3 a b c).card ≤ 3 := by
  unfold up_c3
  exact Finset.card_le_three

/-- The clauses of party `p`. -/
def up_IsCl (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (cl : PEqualNP.ProofComplexity.Clause (up_V n w owner k p)) : Prop :=
  (∃ (e : {t : Fin 3 // t = p ∨ t + 1 = p}) (j : Fin (k e.val)), j.val < n ∧
    (cl = up_c2 (up_Mv n w owner k p e j, false)
        (up_Pv n w owner k p (Sum.inl (up_zc n hn k e.val j.val)), true) ∨
      cl = up_c2 (up_Mv n w owner k p e j, true)
        (up_Pv n w owner k p (Sum.inl (up_zc n hn k e.val j.val)), false))) ∨
  (∃ (r : {r : Fin n // owner r = p}) (pat : Fin (w+1) → Bool),
    cl = up_c1 (up_Pv n w owner k p (Sum.inr (r.val, pat, 0)), true) ∨
    (∃ d : Fin (w+1), cl = up_c3 (up_Pv n w owner k p (Sum.inr (r.val, pat, d.castSucc)), false)
      (up_Pv n w owner k p (Sum.inl (pos n w hn r.val d)), !(pat d))
      (up_Pv n w owner k p (Sum.inr (r.val, pat, d.succ)), true)) ∨
    cl = up_c2 (up_Pv n w owner k p (Sum.inr (r.val, pat, Fin.last (w+1))), false)
      (up_Tv n w owner k p r pat, true))

theorem up_mem_cfilter {X : Type} [Fintype X] (P : X → Prop) (a : X) :
    a ∈ @Finset.filter X P (Classical.decPred P) Finset.univ ↔ P a :=
  (@Finset.mem_filter X P (Classical.decPred P) Finset.univ a).trans
    (and_iff_right (Finset.mem_univ a))

/-- The clause set of party `p`. -/
noncomputable def up_F (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ)
    (p : Fin 3) : Finset (PEqualNP.ProofComplexity.Clause (up_V n w owner k p)) :=
  @Finset.filter _ (up_IsCl n w hn owner k p) (Classical.decPred _) Finset.univ

theorem up_mem_F (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (cl : PEqualNP.ProofComplexity.Clause (up_V n w owner k p)) :
    cl ∈ up_F n w hn owner k p ↔ up_IsCl n w hn owner k p cl :=
  up_mem_cfilter _ cl

/-- The assignment of party `p` built from a table, a message and private bits. -/
def up_asg (n w : ℕ) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) (y : (e : Fin 3) → Fin (k e) → Bool)
    (a : Fin (up_q n w) → Bool) : up_V n w owner k p → Bool :=
  Sum.elim (fun h : {i : Fin n // owner i = p} × (Fin (w+1) → Bool) => tab h.1.val h.2)
    (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ t + 1 = p}) × Fin (k e.val) =>
      y bit.1.val bit.2) a)

/-- Acceptance of a table with a message. -/
def up_acc (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) (y : (e : Fin 3) → Fin (k e) → Bool) : Prop :=
  ∀ p : Fin 3, ∃ a : Fin (up_q n w) → Bool,
    PEqualNP.ProofComplexity.Satisfies (up_asg n w owner k p tab y a)
      (↑(up_F n w hn owner k p) : Set _)

theorem up_card_le (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (cl : PEqualNP.ProofComplexity.Clause (up_V n w owner k p))
    (h : cl ∈ up_F n w hn owner k p) : cl.card ≤ 3 := by
  rw [up_mem_F] at h
  rcases h with ⟨e, j, _, rfl | rfl⟩ | ⟨r, pat, rfl | ⟨d, rfl⟩ | rfl⟩
  · exact up_c2_card _ _
  · exact up_c2_card _ _
  · exact up_c1_card _
  · exact up_c3_card _ _ _
  · exact up_c2_card _ _

theorem up_sat_iff (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ) (p : Fin 3)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) (y : (e : Fin 3) → Fin (k e) → Bool)
    (a : Fin (up_q n w) → Bool) :
    PEqualNP.ProofComplexity.Satisfies (up_asg n w owner k p tab y a)
      (↑(up_F n w hn owner k p) : Set _) ↔
    (∀ (e : {t : Fin 3 // t = p ∨ t + 1 = p}) (j : Fin (k e.val)), j.val < n →
      y e.val j = a (up_en n w (Sum.inl (up_zc n hn k e.val j.val)))) ∧
    (∀ (r : {r : Fin n // owner r = p}) (pat : Fin (w+1) → Bool),
      a (up_en n w (Sum.inr (r.val, pat, 0))) = true ∧
      (∀ d : Fin (w+1), a (up_en n w (Sum.inr (r.val, pat, d.castSucc))) = true →
        a (up_en n w (Sum.inl (pos n w hn r.val d))) = pat d →
        a (up_en n w (Sum.inr (r.val, pat, d.succ))) = true) ∧
      (a (up_en n w (Sum.inr (r.val, pat, Fin.last (w+1)))) = true → tab r.val pat = true)) := by
  constructor
  · intro hs
    have hmem : ∀ cl, up_IsCl n w hn owner k p cl →
        PEqualNP.ProofComplexity.ClauseSat (up_asg n w owner k p tab y a) cl :=
      fun cl hcl => hs cl (Finset.mem_coe.mpr ((up_mem_F n w hn owner k p cl).mpr hcl))
    refine ⟨?_, ?_⟩
    · intro e j hj
      have h1 := (up_c2_sat _ _ _).mp (hmem _ (Or.inl ⟨e, j, hj, Or.inl rfl⟩))
      have h2 := (up_c2_sat _ _ _).mp (hmem _ (Or.inl ⟨e, j, hj, Or.inr rfl⟩))
      change y e.val j = false ∨
        a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) = true at h1
      change y e.val j = true ∨
        a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) = false at h2
      revert h1 h2
      cases y e.val j <;> cases a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) <;> simp
    · intro r pat
      refine ⟨?_, ?_, ?_⟩
      · exact (up_c1_sat _ _).mp (hmem _ (Or.inr ⟨r, pat, Or.inl rfl⟩))
      · intro d h1 h2
        have h3 := (up_c3_sat _ _ _ _).mp
          (hmem _ (Or.inr ⟨r, pat, Or.inr (Or.inl ⟨d, rfl⟩)⟩))
        change a (up_en n w (Sum.inr (r.val, pat, d.castSucc))) = false ∨
          a (up_en n w (Sum.inl (pos n w hn r.val d))) = !(pat d) ∨
          a (up_en n w (Sum.inr (r.val, pat, d.succ))) = true at h3
        rw [h1, h2] at h3
        rcases h3 with h3 | h3 | h3
        · exact absurd h3 (by decide)
        · exact absurd h3 (by cases pat d <;> decide)
        · exact h3
      · intro h1
        have h3 := (up_c2_sat _ _ _).mp (hmem _ (Or.inr ⟨r, pat, Or.inr (Or.inr rfl)⟩))
        change a (up_en n w (Sum.inr (r.val, pat, Fin.last (w+1)))) = false ∨
          tab r.val pat = true at h3
        rw [h1] at h3
        rcases h3 with h3 | h3
        · exact absurd h3 (by decide)
        · exact h3
  · rintro ⟨H1, H2⟩ cl hcl
    have hcl' := (up_mem_F n w hn owner k p cl).mp (Finset.mem_coe.mp hcl)
    rcases hcl' with ⟨e, j, hj, rfl | rfl⟩ | ⟨r, pat, rfl | ⟨d, rfl⟩ | rfl⟩
    · rw [up_c2_sat]
      have h := H1 e j hj
      change y e.val j = false ∨ a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) = true
      rw [h]
      cases a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) <;> simp
    · rw [up_c2_sat]
      have h := H1 e j hj
      change y e.val j = true ∨ a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) = false
      rw [h]
      cases a (up_en n w (Sum.inl (up_zc n hn k e.val j.val))) <;> simp
    · rw [up_c1_sat]
      exact (H2 r pat).1
    · rw [up_c3_sat]
      change a (up_en n w (Sum.inr (r.val, pat, d.castSucc))) = false ∨
        a (up_en n w (Sum.inl (pos n w hn r.val d))) = !(pat d) ∨
        a (up_en n w (Sum.inr (r.val, pat, d.succ))) = true
      by_cases h1 : a (up_en n w (Sum.inr (r.val, pat, d.castSucc))) = true
      · by_cases h2 : a (up_en n w (Sum.inl (pos n w hn r.val d))) = pat d
        · exact Or.inr (Or.inr ((H2 r pat).2.1 d h1 h2))
        · refine Or.inr (Or.inl ?_)
          revert h2
          cases a (up_en n w (Sum.inl (pos n w hn r.val d))) <;> cases pat d <;> simp
      · exact Or.inl (Bool.eq_false_iff.mpr h1)
    · rw [up_c2_sat]
      change a (up_en n w (Sum.inr (r.val, pat, Fin.last (w+1)))) = false ∨
        tab r.val pat = true
      by_cases h1 : a (up_en n w (Sum.inr (r.val, pat, Fin.last (w+1)))) = true
      · exact Or.inr ((H2 r pat).2.2 h1)
      · exact Or.inl (Bool.eq_false_iff.mpr h1)

/-- The private assignment used for completeness: the word itself, and for each chain
variable whether the word agrees with the pattern on the offsets before it. -/
def up_pa (n w : ℕ) (hn : 0 < n) (x : Fin n → Bool) : up_PV n w → Bool :=
  Sum.elim x (fun t => decide (∀ d : Fin (w+1), d.val < t.2.2.val →
    x (pos n w hn t.1 d) = t.2.1 d))

theorem up_pa_inr (n w : ℕ) (hn : 0 < n) (x : Fin n → Bool) (r : Fin n)
    (pat : Fin (w+1) → Bool) (d : Fin (w+2)) :
    up_pa n w hn x (Sum.inr (r, pat, d)) = true ↔
      ∀ d' : Fin (w+1), d'.val < d.val → x (pos n w hn r d') = pat d' :=
  decide_eq_true_iff

theorem up_complete (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) (x : Fin n → Bool)
    (hx : ∀ i, tab i (window n w hn x i) = true) :
    up_acc n w hn owner k tab (up_code n k x) := by
  intro p
  refine ⟨fun i => up_pa n w hn x ((up_en n w).symm i), ?_⟩
  rw [up_sat_iff]
  refine ⟨?_, ?_⟩
  · intro e j hj
    rw [up_code_eq n hn k x e.val j hj]
    show _ = up_pa n w hn x ((up_en n w).symm (up_en n w _))
    rw [Equiv.symm_apply_apply]
    rfl
  · intro r pat
    refine ⟨?_, ?_, ?_⟩
    · show up_pa n w hn x ((up_en n w).symm (up_en n w _)) = true
      rw [Equiv.symm_apply_apply, up_pa_inr]
      intro d hd
      exact absurd hd (Nat.not_lt_zero _)
    · intro d
      show up_pa n w hn x ((up_en n w).symm (up_en n w _)) = true →
        up_pa n w hn x ((up_en n w).symm (up_en n w _)) = pat d →
        up_pa n w hn x ((up_en n w).symm (up_en n w _)) = true
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        up_pa_inr, up_pa_inr]
      intro h1 h2 d' hd'
      have hd2 : d'.val < d.val + 1 := hd'
      by_cases hlt : d'.val < d.val
      · exact h1 d' hlt
      · have hde : d' = d := Fin.ext (by omega)
        rw [hde]
        exact h2
    · show up_pa n w hn x ((up_en n w).symm (up_en n w _)) = true → _
      rw [Equiv.symm_apply_apply, up_pa_inr]
      intro h1
      have hpat : pat = window n w hn x r.val := by
        funext d
        exact (h1 d d.isLt).symm
      rw [hpat]
      exact hx r.val

theorem up_chain (n w : ℕ) (hn : 0 < n) (a : Fin (up_q n w) → Bool) (r : Fin n)
    (pat : Fin (w+1) → Bool)
    (h0 : a (up_en n w (Sum.inr (r, pat, 0))) = true)
    (hstep : ∀ d : Fin (w+1), a (up_en n w (Sum.inr (r, pat, d.castSucc))) = true →
      a (up_en n w (Sum.inl (pos n w hn r d))) = pat d →
      a (up_en n w (Sum.inr (r, pat, d.succ))) = true)
    (hpat : ∀ d : Fin (w+1), a (up_en n w (Sum.inl (pos n w hn r d))) = pat d) :
    a (up_en n w (Sum.inr (r, pat, Fin.last (w+1)))) = true := by
  have key : ∀ (d : ℕ) (hd : d < w + 2),
      a (up_en n w (Sum.inr (r, pat, ⟨d, hd⟩))) = true := by
    intro d
    induction d with
    | zero =>
      intro hd
      exact h0
    | succ d ih =>
      intro hd
      have hd1 : d < w + 1 := Nat.lt_of_succ_lt_succ hd
      exact hstep ⟨d, hd1⟩ (ih (Nat.lt_succ_of_lt hd1)) (hpat ⟨d, hd1⟩)
  exact key (w+1) (Nat.lt_succ_self _)

theorem up_mix_true (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (v : Fin 3 → Fin n → Bool) (r : Fin n) (pat : Fin (w+1) → Bool)
    (h : mix n w hn owner v r pat = true) : pat = window n w hn (v (owner r)) r :=
  of_decide_eq_true h

theorem up_party (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (p : Fin 3) (v : Fin 3 → Fin n → Bool)
    (y : (e : Fin 3) → Fin (k e) → Bool) (a : Fin (up_q n w) → Bool)
    (hs : PEqualNP.ProofComplexity.Satisfies
      (up_asg n w owner k p (mix n w hn owner v) y a) (↑(up_F n w hn owner k p) : Set _))
    (e : Fin 3) (he : e = p ∨ e + 1 = p) (j : Fin (k e)) (hj : j.val < n) :
    y e j = v p (up_zc n hn k e j.val) := by
  rw [up_sat_iff] at hs
  obtain ⟨H1, H2⟩ := hs
  have hu : ∀ z : Fin n, a (up_en n w (Sum.inl z)) = v p z := by
    intro z
    obtain ⟨r, hr, d, hd⟩ := hcov p z
    have hlast := up_chain n w hn a r (fun d' => a (up_en n w (Sum.inl (pos n w hn r d'))))
      (H2 ⟨r, hr⟩ _).1 (H2 ⟨r, hr⟩ _).2.1 (fun d' => rfl)
    have hT := (H2 ⟨r, hr⟩ _).2.2 hlast
    have hw := up_mix_true n w hn owner v r _ hT
    have h2 : a (up_en n w (Sum.inl (pos n w hn r d))) = v (owner r) (pos n w hn r d) :=
      congrFun hw d
    rw [hd, hr] at h2
    exact h2
  rw [← hu]
  exact H1 ⟨e, he⟩ j hj

/-- The triples of words in which neighbouring words agree on the copied coordinates. -/
def up_MM (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) (v : Fin 3 → Fin n → Bool) : Prop :=
  ∀ e : Fin 3, ∀ j : Fin (k e), j.val < n →
    v e (up_zc n hn k e j.val) = v (e + 1) (up_zc n hn k e j.val)

theorem up_sound (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (v : Fin 3 → Fin n → Bool) (y : (e : Fin 3) → Fin (k e) → Bool)
    (hacc : up_acc n w hn owner k (mix n w hn owner v) y) : up_MM n hn k v := by
  intro e j hj
  obtain ⟨a1, h1⟩ := hacc e
  obtain ⟨a2, h2⟩ := hacc (e + 1)
  have e1 := up_party n w hn owner hcov k e v y a1 h1 e (Or.inl rfl) j hj
  have e2 := up_party n w hn owner hcov k (e + 1) v y a2 h2 e (Or.inr rfl) j hj
  exact e1.symm.trans e2

/-- The finite set of the elements with a property. -/
noncomputable def up_cf {X : Type} [Fintype X] (P : X → Prop) : Finset X :=
  @Finset.filter X P (Classical.decPred P) Finset.univ

theorem up_mem_cf {X : Type} [Fintype X] (P : X → Prop) (a : X) : a ∈ up_cf P ↔ P a :=
  up_mem_cfilter P a

theorem up_card4 : ∀ e : Fin 3,
    (Finset.univ.filter (fun b : Fin 3 → Bool => b e = b (e + 1))).card = 4 := by
  decide

theorem up_card2 : ∀ e e' : Fin 3, e ≠ e' →
    (Finset.univ.filter
      (fun b : Fin 3 → Bool => b e = b (e + 1) ∧ b e' = b (e' + 1))).card = 2 := by
  decide

theorem up_card8 : Fintype.card (Fin 3 → Bool) = 8 := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rfl

/-- Every index below the total number of copied bits belongs to one channel. -/
theorem up_idx (n : ℕ) (k : Fin 3 → ℕ) (i : ℕ)
    (hi : i < min n (k 0) + min n (k 1) + min n (k 2)) :
    ∃ e : Fin 3, ∃ j : Fin (k e), j.val < n ∧ up_off n k e + j.val = i := by
  by_cases h0 : i < min n (k 0)
  · refine ⟨0, ⟨i, ?_⟩, ?_, ?_⟩
    · omega
    · show i < n
      omega
    · show up_off n k 0 + i = i
      rw [up_off_zero]
      omega
  · by_cases h1 : i < min n (k 0) + min n (k 1)
    · refine ⟨1, ⟨i - min n (k 0), ?_⟩, ?_, ?_⟩
      · omega
      · show i - min n (k 0) < n
        omega
      · show up_off n k 1 + (i - min n (k 0)) = i
        rw [up_off_one]
        omega
    · refine ⟨2, ⟨i - min n (k 0) - min n (k 1), ?_⟩, ?_, ?_⟩
      · omega
      · show i - min n (k 0) - min n (k 1) < n
        omega
      · show up_off n k 2 + (i - min n (k 0) - min n (k 1)) = i
        rw [up_off_two]
        omega

theorem up_sum_lt (m T : ℕ) :
    ∑ i ∈ Finset.range m, (if i < T then 1 else 0) = min m T := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem up_sum_a (n T : ℕ) :
    ∑ z : Fin n, ((if z.val < T then 1 else 0) + (if z.val + n < T then 1 else 0)) =
      min n T + min n (T - n) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i < T then 1 else 0) + (if i + n < T then 1 else 0)) n,
    Finset.sum_add_distrib, up_sum_lt]
  congr 1
  rw [← up_sum_lt n (T - n)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i + n < T
  · rw [ite_eq_left h, ite_eq_left (by omega : i < T - n)]
  · rw [ite_eq_right h, ite_eq_right (by omega : ¬ i < T - n)]

/-- The condition that the triples of `up_MM` put on the three bits at one position. -/
def up_Q (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) (z : Fin n) (b : Fin 3 → Bool) : Prop :=
  ∀ e : Fin 3, ∀ j : Fin (k e), j.val < n → up_zc n hn k e j.val = z → b e = b (e + 1)

theorem up_count_prod (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) :
    (up_cf (up_MM n hn k)).card ≤ ∏ z : Fin n, (up_cf (up_Q n hn k z)).card := by
  have h1 : (up_cf (up_MM n hn k)).card ≤
      (Fintype.piFinset (fun z : Fin n => up_cf (up_Q n hn k z))).card := by
    refine Finset.card_le_card_of_injOn (fun v z e => v e z) ?_ ?_
    · intro v hv
      have hv' := (up_mem_cf _ v).mp (Finset.mem_coe.mp hv)
      refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr (fun z => (up_mem_cf _ _).mpr ?_))
      intro e j hj hz
      have h2 := hv' e j hj
      rw [hz] at h2
      exact h2
    · intro v1 _ v2 _ h
      funext e z
      exact congrFun (congrFun h z) e
  rw [Fintype.card_piFinset] at h1
  exact h1

theorem up_Q_card (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) (z : Fin n) :
    (up_cf (up_Q n hn k z)).card *
      2 ^ ((if z.val < min n (k 0) + min n (k 1) + min n (k 2) then 1 else 0) +
        (if z.val + n < min n (k 0) + min n (k 1) + min n (k 2) then 1 else 0)) ≤ 8 := by
  by_cases h2 : z.val + n < min n (k 0) + min n (k 1) + min n (k 2)
  · have h1 : z.val < min n (k 0) + min n (k 1) + min n (k 2) := by omega
    rw [ite_eq_left h1, ite_eq_left h2]
    obtain ⟨e, j, hj, hje⟩ := up_idx n k z.val h1
    obtain ⟨e', j', hj', hje'⟩ := up_idx n k (z.val + n) h2
    have hz1 : up_zc n hn k e j.val = z := by
      apply Fin.ext
      show (up_off n k e + j.val) % n = z.val
      rw [hje]
      exact Nat.mod_eq_of_lt z.isLt
    have hz2 : up_zc n hn k e' j'.val = z := by
      apply Fin.ext
      show (up_off n k e' + j'.val) % n = z.val
      rw [hje', Nat.add_mod_right]
      exact Nat.mod_eq_of_lt z.isLt
    have hne : e ≠ e' := by
      intro hee
      subst hee
      omega
    have hsub : up_cf (up_Q n hn k z) ⊆ Finset.univ.filter
        (fun b : Fin 3 → Bool => b e = b (e + 1) ∧ b e' = b (e' + 1)) := by
      intro b hb
      have hb' := (up_mem_cf _ b).mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb' e j hj hz1, hb' e' j' hj' hz2⟩
    have hc := Finset.card_le_card hsub
    rw [up_card2 e e' hne] at hc
    have h4 : (2 : ℕ) ^ (1 + 1) = 4 := rfl
    rw [h4]
    omega
  · by_cases h1 : z.val < min n (k 0) + min n (k 1) + min n (k 2)
    · rw [ite_eq_left h1, ite_eq_right h2]
      obtain ⟨e, j, hj, hje⟩ := up_idx n k z.val h1
      have hz1 : up_zc n hn k e j.val = z := by
        apply Fin.ext
        show (up_off n k e + j.val) % n = z.val
        rw [hje]
        exact Nat.mod_eq_of_lt z.isLt
      have hsub : up_cf (up_Q n hn k z) ⊆ Finset.univ.filter
          (fun b : Fin 3 → Bool => b e = b (e + 1)) := by
        intro b hb
        have hb' := (up_mem_cf _ b).mp hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb' e j hj hz1⟩
      have hc := Finset.card_le_card hsub
      rw [up_card4 e] at hc
      have h4 : (2 : ℕ) ^ (1 + 0) = 2 := rfl
      rw [h4]
      omega
    · rw [ite_eq_right h1, ite_eq_right h2]
      have hc : (up_cf (up_Q n hn k z)).card ≤ Fintype.card (Fin 3 → Bool) :=
        Finset.card_le_univ _
      rw [up_card8] at hc
      have h4 : (2 : ℕ) ^ (0 + 0) = 1 := rfl
      rw [h4]
      omega

theorem up_count (n : ℕ) (hn : 0 < n) (k : Fin 3 → ℕ) :
    (up_cf (up_MM n hn k)).card ≤ 2 ^ (n + excess k n) := by
  have h1 := up_count_prod n hn k
  have h2 : (∏ z : Fin n, (up_cf (up_Q n hn k z)).card) *
      2 ^ (min n (min n (k 0) + min n (k 1) + min n (k 2)) +
        min n (min n (k 0) + min n (k 1) + min n (k 2) - n)) ≤ 8 ^ n := by
    rw [← up_sum_a, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    have h3 := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
      (fun z _ => up_Q_card n hn k z)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h3
    exact h3
  have hex : excess k n = 2 * n - (min n (k 0) + min n (k 1) + min n (k 2)) := by
    unfold excess
    rw [Fin.sum_univ_three]
  have h8 : (8 : ℕ) ^ n = 2 ^ (n + excess k n) *
      2 ^ (min n (min n (k 0) + min n (k 1) + min n (k 2)) +
        min n (min n (k 0) + min n (k 1) + min n (k 2) - n)) := by
    have h23 : (8 : ℕ) = 2 ^ 3 := rfl
    rw [← pow_add, hex, h23, ← pow_mul]
    congr 1
    omega
  rw [h8] at h2
  have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
  exact le_trans h1 h3

/-- A triple of words whose mixed table is the given table, when there is one. -/
noncomputable def up_pick (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) : Fin 3 → Fin n → Bool :=
  if hv : ∃ v, tab = mix n w hn owner v then Classical.choose hv else fun _ _ => false

theorem up_pick_spec (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) (hv : ∃ v, tab = mix n w hn owner v) :
    tab = mix n w hn owner (up_pick n w hn owner tab) := by
  unfold up_pick
  rw [dite_eq_left hv]
  exact Classical.choose_spec hv

/-- The tables counted as errors. -/
def up_Bad (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (k : Fin 3 → ℕ)
    (tab : Fin n → (Fin (w+1) → Bool) → Bool) : Prop :=
  (∃ v, tab = mix n w hn owner v) ∧ ¬ feasible n w hn tab ∧
    ∃ y, up_acc n w hn owner k tab y

theorem up_feas_const (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3) (x : Fin n → Bool) :
    feasible n w hn (mix n w hn owner (fun _ => x)) :=
  ⟨x, fun _ => decide_eq_true rfl⟩

theorem up_err_count (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) :
    (up_cf (up_Bad n w hn owner k)).card + 2 ^ n ≤ (up_cf (up_MM n hn k)).card := by
  have hcard : ((up_cf (up_Bad n w hn owner k)).disjSum
      (Finset.univ : Finset (Fin n → Bool))).card =
      (up_cf (up_Bad n w hn owner k)).card + 2 ^ n := by
    rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (Sum.elim (up_pick n w hn owner) (fun x _ => x)) ?_ ?_
  · intro s hs
    rcases s with tab | x
    · have hb := (up_mem_cf _ tab).mp (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hs))
      obtain ⟨hv, _, y, hy⟩ := hb
      refine Finset.mem_coe.mpr ((up_mem_cf _ _).mpr ?_)
      show up_MM n hn k (up_pick n w hn owner tab)
      have hspec := up_pick_spec n w hn owner tab hv
      rw [hspec] at hy
      exact up_sound n w hn owner hcov k _ y hy
    · refine Finset.mem_coe.mpr ((up_mem_cf _ _).mpr ?_)
      intro e j hj
      rfl
  · intro s1 hs1 s2 hs2 heq
    rcases s1 with t1 | x1 <;> rcases s2 with t2 | x2
    · have hb1 := (up_mem_cf _ t1).mp (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hs1))
      have hb2 := (up_mem_cf _ t2).mp (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hs2))
      have e1 := up_pick_spec n w hn owner t1 hb1.1
      have e2 := up_pick_spec n w hn owner t2 hb2.1
      have heq' : up_pick n w hn owner t1 = up_pick n w hn owner t2 := heq
      rw [heq'] at e1
      exact congrArg Sum.inl (e1.trans e2.symm)
    · have hb1 := (up_mem_cf _ t1).mp (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hs1))
      have e1 := up_pick_spec n w hn owner t1 hb1.1
      have heq' : up_pick n w hn owner t1 = fun _ => x2 := heq
      rw [heq'] at e1
      have hf : feasible n w hn t1 := by
        rw [e1]
        exact up_feas_const n w hn owner x2
      exact absurd hf hb1.2.1
    · have hb2 := (up_mem_cf _ t2).mp (Finset.inl_mem_disjSum.mp (Finset.mem_coe.mp hs2))
      have e2 := up_pick_spec n w hn owner t2 hb2.1
      have heq' : (fun _ => x1) = up_pick n w hn owner t2 := heq
      rw [← heq'] at e2
      have hf : feasible n w hn t2 := by
        rw [e2]
        exact up_feas_const n w hn owner x1
      exact absurd hf hb2.2.1
    · have heq' : (fun _ : Fin 3 => x1) = fun _ => x2 := heq
      exact congrArg Sum.inr (congrFun heq' 0)

theorem up_errors (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (E : ℕ) (h : 2 ^ (n + excess k n) ≤ E + 2 ^ n) :
    (@Finset.filter (Fin n → (Fin (w+1) → Bool) → Bool)
      (fun tab => (∃ v, tab = mix n w hn owner v) ∧ ¬ feasible n w hn tab ∧
        ∃ y, up_acc n w hn owner k tab y)
      (Classical.decPred _) Finset.univ).card ≤ E := by
  have h1 := up_err_count n w hn owner hcov k
  have h2 := up_count n hn k
  have h3 : (up_cf (up_Bad n w hn owner k)).card ≤ E :=
    Nat.le_of_add_le_add_right (le_trans h1 (le_trans h2 h))
  exact h3

theorem upper_main (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w+1), pos n w hn r d = z)
    (k : Fin 3 → ℕ) (ternary : Bool) (E : ℕ) (h : 2 ^ (n + excess k n) ≤ E + 2 ^ n) :
    Fits n w hn owner k ternary 0 E := by
  unfold Fits
  refine ⟨⟨[], 0⟩, fun j => up_out n k 0 j.val, fun j => up_out n k 1 j.val, up_code n k,
    fun _ => up_q n w, up_F n w hn owner k, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  · intro g hg
    exact absurd hg List.not_mem_nil
  · exact Nat.le_refl 0
  · intro x
    exact ⟨fun j => rfl, fun j => rfl⟩
  · intro _ p cl hcl
    exact up_card_le n w hn owner k p cl hcl
  · intro T hT
    obtain ⟨x, hx⟩ := hT
    exact ⟨up_code n k x, up_complete n w hn owner k T x hx⟩
  · intro x
    exact up_complete n w hn owner k (pins n w hn x) x (fun i => decide_eq_true rfl)
  · exact up_errors n w hn owner hcov k E h

end PEqualNP.Outside.L_pcx_250

theorem PEqualNP.Outside.L_pcx_250 : ∀ (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3),
  let Word := Fin n → Bool
  let Pattern := Fin (w+1) → Bool
  let pos := fun (r : Fin n) (d : Fin (w+1)) =>
    (⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let window := fun (x : Word) (r : Fin n) (d : Fin (w+1)) => x (pos r d)
  (∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
    ∃ d : Fin (w+1), pos r d = z) →
  ∀ (k : Fin 3 → ℕ) (ternary : Bool),
    let next := fun e : Fin 3 => e + 1
    let Msg := (e : Fin 3) → Fin (k e) → Bool
    let Table := Fin n → Pattern → Bool
    let pins := fun (word : Word) (row : Fin n) (pat : Pattern) => decide (pat = window word row)
    let V := fun (p : Fin 3) (q : ℕ) =>
      Sum ({r : Fin n // owner r = p} × Pattern)
        (Sum ((e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val)) (Fin q))
    let feasible := fun tableInput : Table => ∃ x : Word, ∀ i, tableInput i (window x i) = true
    let mix := fun (v : Fin 3 → Word) (r : Fin n) (pat : Pattern) => pins (v (owner r)) r pat
    let errors := fun accept : Table → Prop => (@Finset.filter Table
      (fun tab => (∃ v, tab = mix v) ∧ ¬feasible tab ∧ accept tab)
      (Classical.decPred _) Finset.univ).card
    let excess := fun dim : ℕ => 2*dim - ∑ e : Fin 3, min dim (k e)
    let fits := fun (s E : ℕ) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (outA : Fin (k 0) → ℕ) (outB : Fin (k 1) → ℕ)
        (code : Word → Msg) (priv : Fin 3 → ℕ)
        (F : (p : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V p (priv p)))),
        let accepts := fun (tab : Table) (y : Msg) => ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
          PEqualNP.ProofComplexity.Satisfies
            (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => tab h.1.val h.2)
              (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
                y bit.1.val bit.2) a)) (↑(F p) : Set _)
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
        C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ s ∧
        (∀ x : Word,
          (∀ j, code x 0 j = (C.wires (List.ofFn x)).getD (outA j) false) ∧
          (∀ j, code x 1 j = (C.wires (List.ofFn x)).getD (outB j) false)) ∧
        (ternary = true → ∀ p, ∀ cl ∈ F p, cl.card ≤ 3) ∧
        (∀ T : Table, feasible T → ∃ y, accepts T y) ∧
        (∀ x : Word, accepts (pins x) (code x)) ∧ errors (fun queried => ∃ y, accepts queried y) ≤ E
    (∀ s E : ℕ, fits s E → 2^(n + excess (n-s)) ≤ E + 2^n) ∧
      ∀ E : ℕ, fits 0 E ↔ 2^(n + excess n) ≤ E + 2^n := by
  intro n w hn owner Word Pattern pos window hcov k ternary next Msg Table pins V feasible mix
    errors excess fits
  exact ⟨fun s E h => PEqualNP.Outside.L_pcx_250.lower_main n w hn owner hcov k ternary s E h,
    fun E => ⟨fun h => PEqualNP.Outside.L_pcx_250.lower_main n w hn owner hcov k ternary 0 E h,
      fun h => PEqualNP.Outside.L_pcx_250.upper_main n w hn owner hcov k ternary E h⟩⟩
