import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1056_aux

private def symp (u v : ZMod 2 × ZMod 2) : ZMod 2 := u.1 * v.2 + u.2 * v.1

private def colVec : Fin 3 → ZMod 2 × ZMod 2
  | ⟨0, _⟩ => (1, 0)
  | ⟨1, _⟩ => (0, 1)
  | ⟨2, _⟩ => (1, 1)

private def vecCol (v : ZMod 2 × ZMod 2) : Fin 3 :=
  if v = (1, 0) then 0 else if v = (0, 1) then 1 else 2

private lemma vecCol_colVec (c : Fin 3) : vecCol (colVec c) = c := by
  fin_cases c <;> decide

private lemma colVec_vecCol {v : ZMod 2 × ZMod 2} (hv : v ≠ (0, 0)) :
    colVec (vecCol v) = v := by
  rcases v with ⟨a, b⟩
  revert hv
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_eq_zero_of_decide_eq_false {z : ZMod 2} (h : decide (z = 1) = false) :
    z = 0 := by
  fin_cases z
  · rfl
  · exact absurd h (by decide)

private lemma colVec_ne_zero (c : Fin 3) : colVec c ≠ (0, 0) := by
  fin_cases c <;> decide

private lemma symp_colVec (c₁ c₂ : Fin 3) :
    decide (symp (colVec c₁) (colVec c₂) = 1) = decide (c₁ ≠ c₂) := by
  fin_cases c₁ <;> fin_cases c₂ <;> decide

private lemma symp_eq_zero_iff (u v : ZMod 2 × ZMod 2) :
    symp u v = 0 ↔ u = (0, 0) ∨ v = (0, 0) ∨ u = v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private lemma symp_eq_one_iff (u v : ZMod 2 × ZMod 2) :
    symp u v = 1 ↔ u ≠ (0, 0) ∧ v ≠ (0, 0) ∧ u ≠ v := by
  rcases u with ⟨a, b⟩
  rcases v with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

private lemma symp_zero_left (v : ZMod 2 × ZMod 2) : symp (0, 0) v = 0 := by
  simp [symp]

private lemma symp_zero_right (u : ZMod 2 × ZMod 2) : symp u (0, 0) = 0 := by
  simp [symp]

private lemma rank_symp_le_two {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : ι → ZMod 2 × ZMod 2) (V : κ → ZMod 2 × ZMod 2) :
    Matrix.rank (Matrix.of (fun x y => symp (U x) (V y))) ≤ 2 := by
  classical
  let A : Matrix ι κ (ZMod 2) := Matrix.of (fun x y => symp (U x) (V y))
  let u1 : ι → ZMod 2 := fun x => (U x).1
  let u2 : ι → ZMod 2 := fun x => (U x).2
  let f : (Fin 2 → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) :=
    { toFun := fun c => c 0 • u1 + c 1 • u2
      map_add' := fun c₁ c₂ => by funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      map_smul' := fun r c => by funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.range f := by
    rintro _ ⟨w, rfl⟩
    refine ⟨fun i => if i = 0 then ∑ y : κ, (V y).2 * w y else ∑ y : κ, (V y).1 * w y, ?_⟩
    funext x
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      A, Matrix.of_apply, symp, Pi.add_apply, Pi.smul_apply, smul_eq_mul, u1, u2, Finset.sum_mul,
      ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => by ring)
  have h1 : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) ≤
      Module.finrank (ZMod 2) (LinearMap.range f) := Submodule.finrank_mono hle
  have h2 : Module.finrank (ZMod 2) (LinearMap.range f) ≤ Module.finrank (ZMod 2) (Fin 2 → ZMod 2) :=
    LinearMap.finrank_range_le f
  have h3 : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp [Module.finrank_fin_fun]
  exact le_trans (le_trans h1 h2) (le_of_eq h3)

private lemma exists_symp_factor {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ (ZMod 2)) (hA : Matrix.rank A ≤ 2) :
    ∃ (U : ι → ZMod 2 × ZMod 2) (V : κ → ZMod 2 × ZMod 2),
      ∀ x y, A x y = symp (U x) (V y) := by
  classical
  let R := LinearMap.range A.mulVecLin
  set d := Module.finrank (ZMod 2) R
  have hd : d ≤ 2 := hA
  let B : Module.Basis (Fin d) (ZMod 2) R := Module.finBasis (ZMod 2) R
  let col : κ → R := fun y => ⟨A.mulVecLin (Pi.single y 1), LinearMap.mem_range_self _ _⟩
  have hcol_apply : ∀ x y, (col y : ι → ZMod 2) x = A x y := by
    intro x y
    change (A.mulVec (Pi.single y 1)) x = A x y
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdecomp : ∀ x y, A x y = ∑ t : Fin d, ((B t : ι → ZMod 2) x) * (B.repr (col y) t) := by
    intro x y
    have hsum := (B.sum_repr (col y)).symm
    have hx := congrFun (congrArg Subtype.val hsum) x
    rw [hcol_apply x y] at hx
    rw [hx]
    simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul,
      Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun t _ => mul_comm _ _)
  let u0 : ι → ZMod 2 := fun x => if h : 0 < d then (B ⟨0, h⟩ : ι → ZMod 2) x else 0
  let u1 : ι → ZMod 2 := fun x => if h : 1 < d then (B ⟨1, h⟩ : ι → ZMod 2) x else 0
  let v0 : κ → ZMod 2 := fun y => if h : 0 < d then B.repr (col y) ⟨0, h⟩ else 0
  let v1 : κ → ZMod 2 := fun y => if h : 1 < d then B.repr (col y) ⟨1, h⟩ else 0
  refine ⟨fun x => (u0 x, u1 x), fun y => (v1 y, v0 y), fun x y => ?_⟩
  rw [hdecomp x y]
  have hsum : ∀ (m : ℕ) (hm : m ≤ 2) (g : Fin m → ZMod 2),
      ∑ t : Fin m, g t =
        (if h : 0 < m then g ⟨0, h⟩ else 0) + (if h : 1 < m then g ⟨1, h⟩ else 0) := by
    intro m hm g
    match m, hm, g with
    | 0, _, _ => simp
    | 1, _, g => simp [Fin.sum_univ_one]
    | 2, _, g => simp [Fin.sum_univ_two]
  rw [hsum d hd]
  dsimp only [symp, u0, u1, v0, v1]
  split_ifs <;> ring

private abbrev GridIdx (k : ℕ) := Fin k × Fin k × Fin k × Fin 3
private abbrev PairIdx (k : ℕ) := Fin k × Fin k
private abbrev SideIdx (k : ℕ) := Sum (GridIdx k) (PairIdx k)

private instance instDecEqSideIdx (k : ℕ) : DecidableEq (SideIdx k) := by
  unfold SideIdx GridIdx PairIdx; infer_instance

private instance instFintypeSideIdx (k : ℕ) : Fintype (SideIdx k) := by
  unfold SideIdx GridIdx PairIdx; infer_instance

private def fin3Add (c p : Fin 3) : Fin 3 := ⟨(c.val + p.val) % 3, Nat.mod_lt _ (by omega)⟩

private lemma fin3Add_ne_iff (c p q : Fin 3) : fin3Add c p ≠ fin3Add c q ↔ p ≠ q := by
  fin_cases c <;> fin_cases p <;> fin_cases q <;> decide

private lemma fin3Add_zero (c : Fin 3) : fin3Add c 0 = c := by
  fin_cases c <;> decide

private def intEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 3 × Fin 3)).image
    (fun t => (Sum.inl (t.1, t.2.1, t.2.2.1, t.2.2.2.1),
               Sum.inl (t.1, t.2.1, t.2.2.1, t.2.2.2.2)))

private def horizEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  let s : Finset (Fin k × Fin k × Fin k × Fin 2) :=
    Finset.univ.filter (fun t => t.2.2.1.val + 1 < k)
  s.attach.image (fun (t : {x // x ∈ s}) =>
    let hlt : t.1.2.2.1.val + 1 < k := (Finset.mem_filter.mp t.2).2
    (Sum.inl (t.1.1, t.1.2.1, t.1.2.2.1, 0),
     Sum.inl (t.1.1, t.1.2.1, ⟨t.1.2.2.1.val + 1, hlt⟩, ⟨t.1.2.2.2.val, by omega⟩)))

private def vertEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  let s : Finset (Fin k × Fin k × Fin k × Fin 2) :=
    Finset.univ.filter (fun t => t.2.1.val + 1 < k)
  s.attach.image (fun (t : {x // x ∈ s}) =>
    let hlt : t.1.2.1.val + 1 < k := (Finset.mem_filter.mp t.2).2
    (Sum.inl (t.1.1, t.1.2.1, t.1.2.2.1, 0),
     Sum.inl (t.1.1, ⟨t.1.2.1.val + 1, hlt⟩, t.1.2.2.1, ⟨t.1.2.2.2.val, by omega⟩)))

private def pairAskEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).image
    (fun p => (Sum.inr p, Sum.inr p))

private def pairLEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).attach.image
    (fun p =>
      let hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) p.1.2.isLt
      (Sum.inr p.1, Sum.inl (p.1.1, ⟨0, hpos⟩, p.1.2, 0)))

private def pairREdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).attach.image
    (fun p =>
      let hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) p.1.2.isLt
      (Sum.inl (p.1.2, ⟨0, hpos⟩, p.1.1, 0), Sum.inr p.1))

private def allEdges (k : ℕ) : Finset (SideIdx k × SideIdx k) :=
  intEdges k ∪ horizEdges k ∪ vertEdges k ∪ pairAskEdges k ∪ pairLEdges k ∪ pairREdges k

private def baseFun (k : ℕ) : SideIdx k × SideIdx k → Bool
  | (Sum.inl (_, _, _, p), Sum.inl (_, _, _, q)) => decide (p ≠ q)
  | _ => false

private def askFun (k : ℕ) : SideIdx k × SideIdx k → Option (Fin k × Fin k)
  | (Sum.inr p, Sum.inr _) => if p.1 < p.2 then some p else none
  | _ => none

private lemma mem_intEdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ intEdges k ↔ ∃ u a b p q, e = (Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)) := by
  simp only [intEdges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨u, a, b, p, q⟩, rfl⟩; exact ⟨u, a, b, p, q, rfl⟩
  · rintro ⟨u, a, b, p, q, rfl⟩; exact ⟨(u, a, b, p, q), rfl⟩

private lemma mem_horizEdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ horizEdges k ↔
      ∃ (u a b : Fin k) (hlt : b.val + 1 < k) (q : Fin 2),
        e = (Sum.inl (u, a, b, 0), Sum.inl (u, a, ⟨b.val + 1, hlt⟩, ⟨q.val, by omega⟩)) := by
  simp only [horizEdges, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨⟨u, a, b, q⟩, hlt, rfl⟩; exact ⟨u, a, b, hlt, q, rfl⟩
  · rintro ⟨u, a, b, hlt, q, rfl⟩; exact ⟨(u, a, b, q), hlt, rfl⟩

private lemma mem_vertEdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ vertEdges k ↔
      ∃ (u a b : Fin k) (hlt : a.val + 1 < k) (q : Fin 2),
        e = (Sum.inl (u, a, b, 0), Sum.inl (u, ⟨a.val + 1, hlt⟩, b, ⟨q.val, by omega⟩)) := by
  simp only [vertEdges, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨⟨u, a, b, q⟩, hlt, rfl⟩; exact ⟨u, a, b, hlt, q, rfl⟩
  · rintro ⟨u, a, b, hlt, q, rfl⟩; exact ⟨(u, a, b, q), hlt, rfl⟩

private lemma mem_pairAskEdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ pairAskEdges k ↔ ∃ (i j : Fin k), i < j ∧ e = (Sum.inr (i, j), Sum.inr (i, j)) := by
  simp only [pairAskEdges, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩; exact ⟨i, j, hij, rfl⟩
  · rintro ⟨i, j, hij, rfl⟩; exact ⟨(i, j), hij, rfl⟩

private lemma mem_pairLEdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ pairLEdges k ↔
      ∃ (i j : Fin k) (hpos : 0 < k), i < j ∧
        e = (Sum.inr (i, j), Sum.inl (i, ⟨0, hpos⟩, j, 0)) := by
  simp only [pairLEdges, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    exact ⟨i, j, lt_of_le_of_lt (Nat.zero_le _) j.isLt, hij, rfl⟩
  · rintro ⟨i, j, _, hij, rfl⟩
    exact ⟨(i, j), hij, rfl⟩

private lemma mem_pairREdges {k : ℕ} {e : SideIdx k × SideIdx k} :
    e ∈ pairREdges k ↔
      ∃ (i j : Fin k) (hpos : 0 < k), i < j ∧
        e = (Sum.inl (j, ⟨0, hpos⟩, i, 0), Sum.inr (i, j)) := by
  simp only [pairREdges, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
    Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    exact ⟨i, j, lt_of_le_of_lt (Nat.zero_le _) j.isLt, hij, rfl⟩
  · rintro ⟨i, j, _, hij, rfl⟩
    exact ⟨(i, j), hij, rfl⟩

private lemma card_allEdges_le (k : ℕ) : (allEdges k).card ≤ 32 * (k + 1) ^ 3 := by
  have h1 : (intEdges k).card ≤ 9 * k ^ 3 := by
    calc (intEdges k).card ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 3 × Fin 3)).card :=
          Finset.card_image_le
      _ = 9 * k ^ 3 := by simp; ring
  have h2 : (horizEdges k).card ≤ 2 * k ^ 3 := by
    dsimp only [horizEdges]
    calc (Finset.image _ _).card ≤ ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).filter
          (fun t => t.2.2.1.val + 1 < k)).attach.card := Finset.card_image_le
      _ = ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).filter
          (fun t => t.2.2.1.val + 1 < k)).card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).card := Finset.card_filter_le _ _
      _ = 2 * k ^ 3 := by simp; ring
  have h3 : (vertEdges k).card ≤ 2 * k ^ 3 := by
    dsimp only [vertEdges]
    calc (Finset.image _ _).card ≤ ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).filter
          (fun t => t.2.1.val + 1 < k)).attach.card := Finset.card_image_le
      _ = ((Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).filter
          (fun t => t.2.1.val + 1 < k)).card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (Fin k × Fin k × Fin k × Fin 2)).card := Finset.card_filter_le _ _
      _ = 2 * k ^ 3 := by simp; ring
  have h4 : (pairAskEdges k).card ≤ k ^ 2 := by
    dsimp only [pairAskEdges]
    calc (Finset.image _ _).card ≤ ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
      _ = k ^ 2 := by simp; ring
  have h5 : (pairLEdges k).card ≤ k ^ 2 := by
    dsimp only [pairLEdges]
    calc (Finset.image _ _).card ≤ ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).attach.card :=
          Finset.card_image_le
      _ = ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
      _ = k ^ 2 := by simp; ring
  have h6 : (pairREdges k).card ≤ k ^ 2 := by
    dsimp only [pairREdges]
    calc (Finset.image _ _).card ≤ ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).attach.card :=
          Finset.card_image_le
      _ = ((Finset.univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)).card := Finset.card_attach
      _ ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
      _ = k ^ 2 := by simp; ring
  have hu : (allEdges k).card ≤ (intEdges k).card + (horizEdges k).card + (vertEdges k).card +
      (pairAskEdges k).card + (pairLEdges k).card + (pairREdges k).card := by
    dsimp only [allEdges]
    calc (intEdges k ∪ horizEdges k ∪ vertEdges k ∪ pairAskEdges k ∪ pairLEdges k ∪ pairREdges k).card
        ≤ (intEdges k ∪ horizEdges k ∪ vertEdges k ∪ pairAskEdges k ∪ pairLEdges k).card + (pairREdges k).card :=
          Finset.card_union_le _ _
      _ ≤ (intEdges k ∪ horizEdges k ∪ vertEdges k ∪ pairAskEdges k).card + (pairLEdges k).card + (pairREdges k).card := by
          have := Finset.card_union_le (intEdges k ∪ horizEdges k ∪ vertEdges k ∪ pairAskEdges k) (pairLEdges k); omega
      _ ≤ (intEdges k ∪ horizEdges k ∪ vertEdges k).card + (pairAskEdges k).card + (pairLEdges k).card + (pairREdges k).card := by
          have := Finset.card_union_le (intEdges k ∪ horizEdges k ∪ vertEdges k) (pairAskEdges k); omega
      _ ≤ (intEdges k ∪ horizEdges k).card + (vertEdges k).card + (pairAskEdges k).card + (pairLEdges k).card + (pairREdges k).card := by
          have := Finset.card_union_le (intEdges k ∪ horizEdges k) (vertEdges k); omega
      _ ≤ (intEdges k).card + (horizEdges k).card + (vertEdges k).card + (pairAskEdges k).card + (pairLEdges k).card + (pairREdges k).card := by
          have := Finset.card_union_le (intEdges k) (horizEdges k); omega
  have hpoly : 9 * k ^ 3 + 2 * k ^ 3 + 2 * k ^ 3 + k ^ 2 + k ^ 2 + k ^ 2 ≤ 32 * (k + 1) ^ 3 := by
    nlinarith
  omega

private lemma row_deg_le (k : ℕ) (x : SideIdx k) :
    ((allEdges k).filter (fun e => e.1 = x)).card ≤ 18 := by
  classical
  cases x with
  | inl g =>
    rcases g with ⟨u, a, b, p⟩
    let S1 : Finset (SideIdx k) := (Finset.univ : Finset (Fin 3)).image (fun q => Sum.inl (u, a, b, q))
    let S2 : Finset (SideIdx k) :=
      if hb : b.val + 1 < k then
        (Finset.univ : Finset (Fin 2)).image (fun q => Sum.inl (u, a, ⟨b.val + 1, hb⟩, ⟨q.val, by omega⟩))
      else ∅
    let S3 : Finset (SideIdx k) :=
      if ha : a.val + 1 < k then
        (Finset.univ : Finset (Fin 2)).image (fun q => Sum.inl (u, ⟨a.val + 1, ha⟩, b, ⟨q.val, by omega⟩))
      else ∅
    let S4 : Finset (SideIdx k) := {Sum.inr (b, u)}
    let S : Finset (SideIdx k) := S1 ∪ S2 ∪ S3 ∪ S4
    have hsub : ((allEdges k).filter (fun e => e.1 = Sum.inl (u, a, b, p))).image Prod.snd ⊆ S := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heA, hx⟩
      dsimp only [allEdges] at heA
      simp only [Finset.mem_union] at heA
      rcases heA with ((((h | h) | h) | h) | h) | h
      · rcases mem_intEdges.mp h with ⟨u', a', b', p', q', rfl⟩
        simp only [Prod.fst] at hx
        injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, rfl⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_univ q'))))
      · rcases mem_horizEdges.mp h with ⟨u', a', b', hlt, q', rfl⟩
        simp only [Prod.fst] at hx
        injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, _⟩
        refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        simp only [S2, hlt, ↓reduceDIte]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ q')
      · rcases mem_vertEdges.mp h with ⟨u', a', b', hlt, q', rfl⟩
        simp only [Prod.fst] at hx
        injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, _⟩
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [S3, hlt, ↓reduceDIte]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ q')
      · rcases mem_pairAskEdges.mp h with ⟨i', j', _, rfl⟩
        simp at hx
      · rcases mem_pairLEdges.mp h with ⟨i', j', _, _, rfl⟩
        simp at hx
      · rcases mem_pairREdges.mp h with ⟨i', j', _, _, rfl⟩
        simp only [Prod.fst] at hx
        injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨_, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, _⟩
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hinj : Set.InjOn (Prod.snd : SideIdx k × SideIdx k → SideIdx k) ↑((allEdges k).filter (fun e => e.1 = Sum.inl (u, a, b, p))) := by
      intro e₁ h1 e₂ h2 hEq
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      exact Prod.ext (h1'.trans h2'.symm) hEq
    have hcard_eq : ((allEdges k).filter (fun e => e.1 = Sum.inl (u, a, b, p))).card =
        (((allEdges k).filter (fun e => e.1 = Sum.inl (u, a, b, p))).image Prod.snd).card :=
      (Finset.card_image_of_injOn hinj).symm
    have hS1 : S1.card ≤ 3 := le_trans Finset.card_image_le (by simp)
    have hS2 : S2.card ≤ 2 := by
      dsimp only [S2]; split_ifs
      · exact le_trans Finset.card_image_le (by simp)
      · simp
    have hS3 : S3.card ≤ 2 := by
      dsimp only [S3]; split_ifs
      · exact le_trans Finset.card_image_le (by simp)
      · simp
    have hS4 : S4.card ≤ 1 := by simp [S4]
    have hScard : S.card ≤ 8 := by
      dsimp only [S]
      have := Finset.card_union_le (S1 ∪ S2 ∪ S3) S4
      have := Finset.card_union_le (S1 ∪ S2) S3
      have := Finset.card_union_le S1 S2
      omega
    rw [hcard_eq]
    exact le_trans (Finset.card_le_card hsub) (by omega)
  | inr p =>
    rcases p with ⟨i, j⟩
    have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    let S : Finset (SideIdx k) := {Sum.inr (i, j), Sum.inl (i, ⟨0, hpos⟩, j, 0)}
    have hsub : ((allEdges k).filter (fun e => e.1 = Sum.inr (i, j))).image Prod.snd ⊆ S := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heA, hx⟩
      dsimp only [allEdges] at heA
      simp only [Finset.mem_union] at heA
      rcases heA with ((((h | h) | h) | h) | h) | h
      · rcases mem_intEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hx
      · rcases mem_horizEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hx
      · rcases mem_vertEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hx
      · rcases mem_pairAskEdges.mp h with ⟨i', j', _, rfl⟩
        simp only [Prod.fst] at hx; injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, rfl⟩
        exact Finset.mem_insert_self _ _
      · rcases mem_pairLEdges.mp h with ⟨i', j', _, _, rfl⟩
        simp only [Prod.fst] at hx; injection hx with hx'
        rcases Prod.mk.inj hx' with ⟨rfl, rfl⟩
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rcases mem_pairREdges.mp h with ⟨_, _, _, _, rfl⟩; simp at hx
    have hinj : Set.InjOn (Prod.snd : SideIdx k × SideIdx k → SideIdx k) ↑((allEdges k).filter (fun e => e.1 = Sum.inr (i, j))) := by
      intro e₁ h1 e₂ h2 hEq
      exact Prod.ext ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm) hEq
    rw [← Finset.card_image_of_injOn hinj]
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_le_two (by omega))

private lemma col_deg_le (k : ℕ) (y : SideIdx k) :
    ((allEdges k).filter (fun e => e.2 = y)).card ≤ 18 := by
  classical
  cases y with
  | inl g =>
    rcases g with ⟨u, a, b, q⟩
    let S1 : Finset (SideIdx k) := (Finset.univ : Finset (Fin 3)).image (fun p => Sum.inl (u, a, b, p))
    let S2 : Finset (SideIdx k) :=
      if hb : 0 < b.val then {Sum.inl (u, a, ⟨b.val - 1, by omega⟩, 0)} else ∅
    let S3 : Finset (SideIdx k) :=
      if ha : 0 < a.val then {Sum.inl (u, ⟨a.val - 1, by omega⟩, b, 0)} else ∅
    let S4 : Finset (SideIdx k) := {Sum.inr (u, b)}
    let S : Finset (SideIdx k) := S1 ∪ S2 ∪ S3 ∪ S4
    have hsub : ((allEdges k).filter (fun e => e.2 = Sum.inl (u, a, b, q))).image Prod.fst ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heA, hy⟩
      dsimp only [allEdges] at heA
      simp only [Finset.mem_union] at heA
      rcases heA with ((((h | h) | h) | h) | h) | h
      · rcases mem_intEdges.mp h with ⟨u', a', b', p', q', rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, rfl⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem _ (Finset.mem_univ p'))))
      · rcases mem_horizEdges.mp h with ⟨u', a', b', hlt, q', rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨rfl, h3⟩
        rcases Prod.mk.inj h3 with ⟨hbEq, _⟩
        have hbval : b.val = b'.val + 1 := (congrArg Fin.val hbEq).symm
        have hbpos : 0 < b.val := by omega
        have hb' : (⟨b.val - 1, by omega⟩ : Fin k) = b' := Fin.ext (by dsimp only; omega)
        refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        simp only [S2, hbpos, ↓reduceDIte, hb', Finset.mem_singleton]
      · rcases mem_vertEdges.mp h with ⟨u', a', b', hlt, q', rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨haEq, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, _⟩
        have haval : a.val = a'.val + 1 := (congrArg Fin.val haEq).symm
        have hapos : 0 < a.val := by omega
        have ha' : (⟨a.val - 1, by omega⟩ : Fin k) = a' := Fin.ext (by dsimp only; omega)
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [S3, hapos, ↓reduceDIte, ha', Finset.mem_singleton]
      · rcases mem_pairAskEdges.mp h with ⟨_, _, _, rfl⟩; simp at hy
      · rcases mem_pairLEdges.mp h with ⟨i', j', _, _, rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨_, h3⟩
        rcases Prod.mk.inj h3 with ⟨rfl, _⟩
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
      · rcases mem_pairREdges.mp h with ⟨_, _, _, _, rfl⟩; simp at hy
    have hinj : Set.InjOn (Prod.fst : SideIdx k × SideIdx k → SideIdx k) ↑((allEdges k).filter (fun e => e.2 = Sum.inl (u, a, b, q))) := by
      intro e₁ h1 e₂ h2 hEq
      exact Prod.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
    have hS1 : S1.card ≤ 3 := le_trans Finset.card_image_le (by simp)
    have hS2 : S2.card ≤ 1 := by dsimp only [S2]; split_ifs <;> simp
    have hS3 : S3.card ≤ 1 := by dsimp only [S3]; split_ifs <;> simp
    have hS4 : S4.card ≤ 1 := by simp [S4]
    have hScard : S.card ≤ 6 := by
      dsimp only [S]
      have := Finset.card_union_le (S1 ∪ S2 ∪ S3) S4
      have := Finset.card_union_le (S1 ∪ S2) S3
      have := Finset.card_union_le S1 S2
      omega
    rw [← Finset.card_image_of_injOn hinj]
    exact le_trans (Finset.card_le_card hsub) (by omega)
  | inr p =>
    rcases p with ⟨i, j⟩
    have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    let S : Finset (SideIdx k) := {Sum.inr (i, j), Sum.inl (j, ⟨0, hpos⟩, i, 0)}
    have hsub : ((allEdges k).filter (fun e => e.2 = Sum.inr (i, j))).image Prod.fst ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      rcases Finset.mem_filter.mp he with ⟨heA, hy⟩
      dsimp only [allEdges] at heA
      simp only [Finset.mem_union] at heA
      rcases heA with ((((h | h) | h) | h) | h) | h
      · rcases mem_intEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hy
      · rcases mem_horizEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hy
      · rcases mem_vertEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp at hy
      · rcases mem_pairAskEdges.mp h with ⟨i', j', _, rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, rfl⟩
        exact Finset.mem_insert_self _ _
      · rcases mem_pairLEdges.mp h with ⟨_, _, _, _, rfl⟩; simp at hy
      · rcases mem_pairREdges.mp h with ⟨i', j', _, _, rfl⟩
        simp only [Prod.snd] at hy; injection hy with hy'
        rcases Prod.mk.inj hy' with ⟨rfl, rfl⟩
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hinj : Set.InjOn (Prod.fst : SideIdx k × SideIdx k → SideIdx k) ↑((allEdges k).filter (fun e => e.2 = Sum.inr (i, j))) := by
      intro e₁ h1 e₂ h2 hEq
      exact Prod.ext hEq ((Finset.mem_filter.mp h1).2.trans (Finset.mem_filter.mp h2).2.symm)
    rw [← Finset.card_image_of_injOn hinj]
    exact le_trans (Finset.card_le_card hsub) (le_trans Finset.card_le_two (by omega))

private def cellOK (k : ℕ) (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (u a b : Fin k) : Prop :=
  ∀ p q : Fin 3, decide (A (Sum.inl (u, a, b, p)) (Sum.inl (u, a, b, q)) = 1) = decide (p ≠ q)

private def rowClean (k : ℕ) (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (u a : Fin k) : Prop :=
  (∀ b : Fin k, cellOK k A u a b) ∧
  (∀ (b : Fin k) (hlt : b.val + 1 < k) (q : Fin 2),
    decide (A (Sum.inl (u, a, b, 0)) (Sum.inl (u, a, ⟨b.val + 1, hlt⟩, ⟨q.val, by omega⟩)) = 1) =
      decide ((0 : Fin 3) ≠ ⟨q.val, by omega⟩))

private def colClean (k : ℕ) (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (u b : Fin k) : Prop :=
  (∀ a : Fin k, cellOK k A u a b) ∧
  (∀ (a : Fin k) (hlt : a.val + 1 < k) (q : Fin 2),
    decide (A (Sum.inl (u, a, b, 0)) (Sum.inl (u, ⟨a.val + 1, hlt⟩, b, ⟨q.val, by omega⟩)) = 1) =
      decide ((0 : Fin 3) ≠ ⟨q.val, by omega⟩))

private lemma cellOK_implies {k : ℕ} (U V : SideIdx k → ZMod 2 × ZMod 2)
    (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (hA : ∀ x y, A x y = symp (U x) (V y))
    (u a b : Fin k) (hok : cellOK k A u a b) :
    (∀ p : Fin 3, U (Sum.inl (u, a, b, p)) ≠ (0, 0) ∧
      V (Sum.inl (u, a, b, p)) = U (Sum.inl (u, a, b, p))) ∧
    (∀ p q : Fin 3, p ≠ q → U (Sum.inl (u, a, b, p)) ≠ U (Sum.inl (u, a, b, q))) := by
  have hne : ∀ p q : Fin 3, p ≠ q →
      U (Sum.inl (u, a, b, p)) ≠ (0, 0) ∧ V (Sum.inl (u, a, b, q)) ≠ (0, 0) ∧
      U (Sum.inl (u, a, b, p)) ≠ V (Sum.inl (u, a, b, q)) := by
    intro p q hpq
    have h1 := hok p q
    rw [hA] at h1
    have htrue : decide (p ≠ q) = true := decide_eq_true hpq
    rw [htrue] at h1
    exact (symp_eq_one_iff _ _).mp (of_decide_eq_true h1)
  have heq : ∀ p : Fin 3,
      U (Sum.inl (u, a, b, p)) ≠ (0, 0) ∧ V (Sum.inl (u, a, b, p)) = U (Sum.inl (u, a, b, p)) := by
    intro p
    have hother : ∃ q : Fin 3, p ≠ q := by
      fin_cases p
      · exact ⟨1, by decide⟩
      · exact ⟨0, by decide⟩
      · exact ⟨0, by decide⟩
    rcases hother with ⟨q, hpq⟩
    have hu := (hne p q hpq).1
    have hv := (hne q p hpq.symm).2.1
    have h0 := hok p p
    rw [hA] at h0
    have hfalse : decide (p ≠ p) = false := decide_eq_false (not_not.mpr rfl)
    rw [hfalse] at h0
    have hsym0 : symp (U (Sum.inl (u, a, b, p))) (V (Sum.inl (u, a, b, p))) = 0 :=
      zmod2_eq_zero_of_decide_eq_false h0
    rcases (symp_eq_zero_iff _ _).mp hsym0 with h | h | h
    · exact absurd h hu
    · exact absurd h hv
    · exact ⟨hu, h.symm⟩
  refine ⟨heq, fun p q hpq => ?_⟩
  rw [← (heq q).2]
  exact (hne p q hpq).2.2

private lemma link_eq_of_clean {k : ℕ} (U V : SideIdx k → ZMod 2 × ZMod 2)
    (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (hA : ∀ x y, A x y = symp (U x) (V y))
    (u a b a' b' : Fin k) (hok' : cellOK k A u a' b')
    (hl0 : decide (A (Sum.inl (u, a, b, 0)) (Sum.inl (u, a', b', 0)) = 1) = false)
    (hl1 : decide (A (Sum.inl (u, a, b, 0)) (Sum.inl (u, a', b', 1)) = 1) = true) :
    U (Sum.inl (u, a, b, 0)) = U (Sum.inl (u, a', b', 0)) := by
  obtain ⟨heq', _⟩ := cellOK_implies U V A hA u a' b' hok'
  rw [hA] at hl0 hl1
  have hu_nz : U (Sum.inl (u, a, b, 0)) ≠ (0, 0) :=
    ((symp_eq_one_iff _ _).mp (of_decide_eq_true hl1)).1
  have hsym0 : symp (U (Sum.inl (u, a, b, 0))) (V (Sum.inl (u, a', b', 0))) = 0 :=
    zmod2_eq_zero_of_decide_eq_false hl0
  rcases (symp_eq_zero_iff _ _).mp hsym0 with h | h | h
  · exact absurd h hu_nz
  · rw [(heq' 0).2] at h; exact absurd h (heq' 0).1
  · rw [h, (heq' 0).2]

private lemma rowClean_const {k : ℕ} (U V : SideIdx k → ZMod 2 × ZMod 2)
    (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (hA : ∀ x y, A x y = symp (U x) (V y))
    (u a : Fin k) (hrc : rowClean k A u a) :
    ∀ b₁ b₂ : Fin k, U (Sum.inl (u, a, b₁, 0)) = U (Sum.inl (u, a, b₂, 0)) := by
  have hstep : ∀ (b : Fin k) (hlt : b.val + 1 < k),
      U (Sum.inl (u, a, b, 0)) = U (Sum.inl (u, a, ⟨b.val + 1, hlt⟩, 0)) := by
    intro b hlt
    exact link_eq_of_clean U V A hA u a b a ⟨b.val + 1, hlt⟩ (hrc.1 ⟨b.val + 1, hlt⟩)
      (hrc.2 b hlt 0) (hrc.2 b hlt 1)
  have hzero : ∀ (m : ℕ) (hm : m < k),
      U (Sum.inl (u, a, ⟨0, lt_of_le_of_lt (Nat.zero_le _) hm⟩, 0)) =
      U (Sum.inl (u, a, ⟨m, hm⟩, 0)) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hm' : m < k := Nat.lt_of_succ_lt hm
      exact (ih hm').trans (hstep ⟨m, hm'⟩ hm)
  intro b₁ b₂
  exact (hzero b₁.val b₁.isLt).symm.trans (hzero b₂.val b₂.isLt)

private lemma colClean_const {k : ℕ} (U V : SideIdx k → ZMod 2 × ZMod 2)
    (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2))
    (hA : ∀ x y, A x y = symp (U x) (V y))
    (u b : Fin k) (hcc : colClean k A u b) :
    ∀ a₁ a₂ : Fin k, U (Sum.inl (u, a₁, b, 0)) = U (Sum.inl (u, a₂, b, 0)) := by
  have hstep : ∀ (a : Fin k) (hlt : a.val + 1 < k),
      U (Sum.inl (u, a, b, 0)) = U (Sum.inl (u, ⟨a.val + 1, hlt⟩, b, 0)) := by
    intro a hlt
    exact link_eq_of_clean U V A hA u a b ⟨a.val + 1, hlt⟩ b (hcc.1 ⟨a.val + 1, hlt⟩)
      (hcc.2 a hlt 0) (hcc.2 a hlt 1)
  have hzero : ∀ (m : ℕ) (hm : m < k),
      U (Sum.inl (u, ⟨0, lt_of_le_of_lt (Nat.zero_le _) hm⟩, b, 0)) =
      U (Sum.inl (u, ⟨m, hm⟩, b, 0)) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have hm' : m < k := Nat.lt_of_succ_lt hm
      exact (ih hm').trans (hstep ⟨m, hm'⟩ hm)
  intro a₁ a₂
  exact (hzero a₁.val a₁.isLt).symm.trans (hzero a₂.val a₂.isLt)

private lemma rank_le_two_decode_side (k : ℕ) :
    ∃ decodeS : Matrix (SideIdx k) (SideIdx k) (ZMod 2) → Fin k → Fin 3,
      ∀ (g : Fin k → Fin k → Bool),
        let val := fun e => (askFun k e).elim (baseFun k e) (fun p => g p.1 p.2)
        let err := fun (A : Matrix (SideIdx k) (SideIdx k) (ZMod 2)) =>
          ((allEdges k).filter (fun e => decide (A e.1 e.2 = 1) ≠ val e)).card
        let defect := fun (c : Fin k → Fin 3) =>
          ((Finset.univ : Finset (Fin k × Fin k)).filter
            (fun p => p.1 < p.2 ∧ g p.1 p.2 = true ∧ c p.1 = c p.2)).card
        (∀ A, Matrix.rank A ≤ 2 → defect (decodeS A) ≤ err A) ∧
        (∀ c : Fin k → Fin 3, ∃ A, Matrix.rank A ≤ 2 ∧ err A = defect c) := by
  classical
  let decodeS : Matrix (SideIdx k) (SideIdx k) (ZMod 2) → Fin k → Fin 3 := fun A u =>
    if h : Matrix.rank A ≤ 2 ∧ ∃ a : Fin k, rowClean k A u a then
      let U := Classical.choose (exists_symp_factor A h.1)
      let a₀ := Classical.choose h.2
      vecCol (U (Sum.inl (u, a₀, a₀, 0)))
    else 0
  refine ⟨decodeS, fun g => ?_⟩
  dsimp only
  let val : SideIdx k × SideIdx k → Bool :=
    fun e => (askFun k e).elim (baseFun k e) (fun p => g p.1 p.2)
  have hval_int : ∀ e ∈ intEdges k, val e = baseFun k e := by
    intro e he
    rcases mem_intEdges.mp he with ⟨_, _, _, _, _, rfl⟩; rfl
  have hval_horiz : ∀ e ∈ horizEdges k, val e = baseFun k e := by
    intro e he
    rcases mem_horizEdges.mp he with ⟨_, _, _, _, _, rfl⟩; rfl
  have hval_vert : ∀ e ∈ vertEdges k, val e = baseFun k e := by
    intro e he
    rcases mem_vertEdges.mp he with ⟨_, _, _, _, _, rfl⟩; rfl
  have hval_pairL : ∀ e ∈ pairLEdges k, val e = false := by
    intro e he
    rcases mem_pairLEdges.mp he with ⟨_, _, _, _, rfl⟩; rfl
  have hval_pairR : ∀ e ∈ pairREdges k, val e = false := by
    intro e he
    rcases mem_pairREdges.mp he with ⟨_, _, _, _, rfl⟩; rfl
  have hval_pairAsk : ∀ (i j : Fin k), i < j → val (Sum.inr (i, j), Sum.inr (i, j)) = g i j := by
    intro i j hij
    simp [val, askFun, hij]
  constructor
  · intro A hrank
    let U := Classical.choose (exists_symp_factor A hrank)
    have hVex := Classical.choose_spec (exists_symp_factor A hrank)
    let V := Classical.choose hVex
    have hA : ∀ x y, A x y = symp (U x) (V y) := Classical.choose_spec hVex
    let errSet : Finset (SideIdx k × SideIdx k) :=
      (allEdges k).filter (fun e => decide (A e.1 e.2 = 1) ≠ val e)
    let gridErr : Fin k → Finset (SideIdx k × SideIdx k) := fun u =>
      errSet.filter (fun e => match e with
        | (Sum.inl (u', _, _, _), Sum.inl _) => u' = u
        | _ => False)
    let pairErr : (Fin k × Fin k) → Finset (SideIdx k × SideIdx k) := fun p =>
      errSet.filter (fun e => match e with
        | (Sum.inr p', Sum.inr _) => p' = p
        | (Sum.inr p', Sum.inl _) => p' = p
        | (Sum.inl _, Sum.inr p') => p' = p
        | _ => False)
    have hrow_err_pos : ∀ u a, ¬ rowClean k A u a →
        ∃ e ∈ gridErr u,
          match e with
          | (Sum.inl (_, a', _, _), Sum.inl _) => a' = a
          | _ => False := by
      intro u a hnot
      simp only [rowClean, not_and_or, Classical.not_forall] at hnot
      rcases hnot with ⟨b, hb⟩ | ⟨b, hlt, q, hq⟩
      · simp only [cellOK, Classical.not_forall] at hb
        rcases hb with ⟨p, q, hpq⟩
        have heI : (Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)) ∈ intEdges k :=
          mem_intEdges.mpr ⟨u, a, b, p, q, rfl⟩
        have heA : (Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)) ∈ allEdges k := by
          dsimp only [allEdges]; simp [heI]
        refine ⟨(Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heA, ?_⟩, rfl⟩
        rw [hval_int _ heI]
        exact hpq
      · have heH : (Sum.inl (u, a, b, 0),
            Sum.inl (u, a, ⟨b.val + 1, hlt⟩, ⟨q.val, by omega⟩)) ∈ horizEdges k :=
          mem_horizEdges.mpr ⟨u, a, b, hlt, q, rfl⟩
        have heA : (Sum.inl (u, a, b, 0),
            Sum.inl (u, a, ⟨b.val + 1, hlt⟩, ⟨q.val, by omega⟩)) ∈ allEdges k := by
          dsimp only [allEdges]; simp [heH]
        refine ⟨(Sum.inl (u, a, b, 0), Sum.inl (u, a, ⟨b.val + 1, hlt⟩, ⟨q.val, by omega⟩)), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heA, ?_⟩, rfl⟩
        rw [hval_horiz _ heH]
        exact hq
    have hcol_err_pos : ∀ u b, ¬ colClean k A u b →
        ∃ e ∈ gridErr u,
          match e with
          | (Sum.inl (_, _, b', _), Sum.inl _) => b' = b
          | _ => False := by
      intro u b hnot
      simp only [colClean, not_and_or, Classical.not_forall] at hnot
      rcases hnot with ⟨a, ha⟩ | ⟨a, hlt, q, hq⟩
      · simp only [cellOK, Classical.not_forall] at ha
        rcases ha with ⟨p, q, hpq⟩
        have heI : (Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)) ∈ intEdges k :=
          mem_intEdges.mpr ⟨u, a, b, p, q, rfl⟩
        have heA : (Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)) ∈ allEdges k := by
          dsimp only [allEdges]; simp [heI]
        refine ⟨(Sum.inl (u, a, b, p), Sum.inl (u, a, b, q)), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heA, ?_⟩, rfl⟩
        rw [hval_int _ heI]
        exact hpq
      · have heV : (Sum.inl (u, a, b, 0),
            Sum.inl (u, ⟨a.val + 1, hlt⟩, b, ⟨q.val, by omega⟩)) ∈ vertEdges k :=
          mem_vertEdges.mpr ⟨u, a, b, hlt, q, rfl⟩
        have heA : (Sum.inl (u, a, b, 0),
            Sum.inl (u, ⟨a.val + 1, hlt⟩, b, ⟨q.val, by omega⟩)) ∈ allEdges k := by
          dsimp only [allEdges]; simp [heV]
        refine ⟨(Sum.inl (u, a, b, 0), Sum.inl (u, ⟨a.val + 1, hlt⟩, b, ⟨q.val, by omega⟩)), ?_, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heA, ?_⟩, rfl⟩
        rw [hval_vert _ heV]
        exact hq
    let badSlot : Fin k → Finset (Fin k) := fun u =>
      if ∃ a : Fin k, rowClean k A u a then
        Finset.univ.filter (fun b => ¬ colClean k A u b)
      else Finset.univ
    have hbad_le_grid : ∀ u : Fin k, (badSlot u).card ≤ (gridErr u).card := by
      intro u
      by_cases hex : ∃ a : Fin k, rowClean k A u a
      · simp only [badSlot, hex, ↓reduceIte]
        have hf : ∀ b ∈ Finset.univ.filter (fun b : Fin k => ¬ colClean k A u b),
            ∃ e ∈ gridErr u, match e with | (Sum.inl (_, _, b', _), Sum.inl _) => b' = b | _ => False :=
          fun b hb => hcol_err_pos u b (Finset.mem_filter.mp hb).2
        let fcol : Fin k → SideIdx k × SideIdx k := fun b =>
          if hb : ¬ colClean k A u b then Classical.choose (hcol_err_pos u b hb) else (Sum.inr (u, u), Sum.inr (u, u))
        have hmap : (Finset.univ.filter (fun b : Fin k => ¬ colClean k A u b)).image fcol ⊆ gridErr u := by
          intro e he
          rcases Finset.mem_image.mp he with ⟨b, hb, rfl⟩
          have hnb : ¬ colClean k A u b := (Finset.mem_filter.mp hb).2
          simp only [fcol, hnb, ↓reduceDIte]
          exact (Classical.choose_spec (hcol_err_pos u b hnb)).1
        have hinj : Set.InjOn fcol (Finset.univ.filter (fun b : Fin k => ¬ colClean k A u b) : Set (Fin k)) := by
          intro b₁ h1 b₂ h2 heq
          have hn1 : ¬ colClean k A u b₁ := (Finset.mem_filter.mp h1).2
          have hn2 : ¬ colClean k A u b₂ := (Finset.mem_filter.mp h2).2
          have hf1 : fcol b₁ = Classical.choose (hcol_err_pos u b₁ hn1) := dif_pos hn1
          have hf2 : fcol b₂ = Classical.choose (hcol_err_pos u b₂ hn2) := dif_pos hn2
          rw [hf1, hf2] at heq
          have hp1 := (Classical.choose_spec (hcol_err_pos u b₁ hn1)).2
          have hp2 := (Classical.choose_spec (hcol_err_pos u b₂ hn2)).2
          rw [heq] at hp1
          cases he2 : Classical.choose (hcol_err_pos u b₂ hn2) with
          | mk x y =>
            cases x with
            | inl gx =>
              rcases gx with ⟨_, _, b', _⟩
              cases y with
              | inl gy =>
                rw [he2] at hp1 hp2
                exact hp1.symm.trans hp2
              | inr _ => rw [he2] at hp1; exact False.elim hp1
            | inr _ => rw [he2] at hp1; exact False.elim hp1
        rw [← Finset.card_image_of_injOn hinj]
        exact Finset.card_le_card hmap
      · simp only [badSlot, hex, ↓reduceIte]
        have hno : ∀ a : Fin k, ¬ rowClean k A u a := fun a ha => hex ⟨a, ha⟩
        let frow : Fin k → SideIdx k × SideIdx k := fun a => Classical.choose (hrow_err_pos u a (hno a))
        have hmap : Finset.univ.image frow ⊆ gridErr u := by
          intro e he
          rcases Finset.mem_image.mp he with ⟨a, _, rfl⟩
          exact (Classical.choose_spec (hrow_err_pos u a (hno a))).1
        have hinj : Set.InjOn frow ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
          intro a₁ _ a₂ _ heq
          have hp1 := (Classical.choose_spec (hrow_err_pos u a₁ (hno a₁))).2
          have hp2 := (Classical.choose_spec (hrow_err_pos u a₂ (hno a₂))).2
          dsimp only [frow] at heq
          rw [heq] at hp1
          cases he2 : Classical.choose (hrow_err_pos u a₂ (hno a₂)) with
          | mk x y =>
            cases x with
            | inl gx =>
              rcases gx with ⟨_, a', _, _⟩
              cases y with
              | inl gy =>
                rw [he2] at hp1 hp2
                exact hp1.symm.trans hp2
              | inr _ => rw [he2] at hp1; exact False.elim hp1
            | inr _ => rw [he2] at hp1; exact False.elim hp1
        rw [← Finset.card_image_of_injOn hinj]
        exact Finset.card_le_card hmap
    have hgood_vec : ∀ (u b : Fin k) (hpos : 0 < k), b ∉ badSlot u →
        U (Sum.inl (u, ⟨0, hpos⟩, b, 0)) = colVec (decodeS A u) ∧
        V (Sum.inl (u, ⟨0, hpos⟩, b, 0)) = colVec (decodeS A u) := by
      intro u b hpos hnot
      by_cases hex : ∃ a : Fin k, rowClean k A u a
      · have hcc : colClean k A u b := by
          simp only [badSlot, hex, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
          exact hnot
        have hdec : decodeS A u = vecCol (U (Sum.inl (u, Classical.choose hex, Classical.choose hex, 0))) := by
          dsimp only [decodeS]
          have hh : Matrix.rank A ≤ 2 ∧ ∃ a : Fin k, rowClean k A u a := ⟨hrank, hex⟩
          rw [dif_pos hh]
        have ha₀ := Classical.choose_spec hex
        set a₀ := Classical.choose hex
        have h1 : U (Sum.inl (u, ⟨0, hpos⟩, b, 0)) = U (Sum.inl (u, a₀, b, 0)) :=
          colClean_const U V A hA u b hcc ⟨0, hpos⟩ a₀
        have h2 : U (Sum.inl (u, a₀, b, 0)) = U (Sum.inl (u, a₀, a₀, 0)) :=
          rowClean_const U V A hA u a₀ ha₀ b a₀
        have hcell0 := cellOK_implies U V A hA u ⟨0, hpos⟩ b (hcc.1 ⟨0, hpos⟩)
        have hcell_a := cellOK_implies U V A hA u a₀ a₀ (ha₀.1 a₀)
        have hcol : colVec (decodeS A u) = U (Sum.inl (u, a₀, a₀, 0)) := by
          rw [hdec]
          exact colVec_vecCol (hcell_a.1 0).1
        rw [hcol, h1, h2]
        refine ⟨rfl, ?_⟩
        rw [(hcell0.1 0).2, h1, h2]
      · simp only [badSlot, hex, ↓reduceIte, Finset.mem_univ, not_true_eq_false] at hnot
    let Dset : Finset (Fin k × Fin k) :=
      Finset.univ.filter (fun p => p.1 < p.2 ∧ g p.1 p.2 = true ∧ decodeS A p.1 = decodeS A p.2)
    let D_badL : Finset (Fin k × Fin k) := Dset.filter (fun p => p.2 ∈ badSlot p.1)
    let D_badR : Finset (Fin k × Fin k) := Dset.filter (fun p => p.2 ∉ badSlot p.1 ∧ p.1 ∈ badSlot p.2)
    let D_good : Finset (Fin k × Fin k) := Dset.filter (fun p => p.2 ∉ badSlot p.1 ∧ p.1 ∉ badSlot p.2)
    have hD_cov : Dset ⊆ D_badL ∪ D_badR ∪ D_good := by
      intro p hp
      by_cases h1 : p.2 ∈ badSlot p.1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h1⟩))
      · by_cases h2 : p.1 ∈ badSlot p.2
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h1, h2⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h1, h2⟩)
    have hpair_good : ∀ p ∈ D_good, 1 ≤ (pairErr p).card := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpD, hnb1, hnb2⟩
      rcases Finset.mem_filter.mp hpD with ⟨_, hlt, hg, hceq⟩
      have hpos : 0 < k := lt_of_le_of_lt (Nat.zero_le _) p.2.isLt
      have hv1 := (hgood_vec p.1 p.2 hpos hnb1).2
      have hu2 := (hgood_vec p.2 p.1 hpos hnb2).1
      rw [← hceq] at hu2
      have hne0 : colVec (decodeS A p.1) ≠ (0, 0) := colVec_ne_zero _
      by_contra h0
      have hemp : pairErr p = ∅ := Finset.card_eq_zero.mp (by omega)
      have heAsk : (Sum.inr p, Sum.inr p) ∈ allEdges k := by
        simp only [allEdges, Finset.mem_union]
        left; left; right; exact mem_pairAskEdges.mpr ⟨p.1, p.2, hlt, rfl⟩
      have heL : (Sum.inr p, Sum.inl (p.1, ⟨0, hpos⟩, p.2, 0)) ∈ allEdges k := by
        simp only [allEdges, Finset.mem_union]
        left; right; exact mem_pairLEdges.mpr ⟨p.1, p.2, hpos, hlt, rfl⟩
      have heR : (Sum.inl (p.2, ⟨0, hpos⟩, p.1, 0), Sum.inr p) ∈ allEdges k := by
        simp only [allEdges, Finset.mem_union]
        right; exact mem_pairREdges.mpr ⟨p.1, p.2, hpos, hlt, rfl⟩
      have hokAsk : decide (A (Sum.inr p) (Sum.inr p) = 1) = true := by
        by_contra hne
        have hmem : (Sum.inr p, Sum.inr p) ∈ pairErr p := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heAsk, ?_⟩, rfl⟩
          rw [hval_pairAsk p.1 p.2 hlt, hg]; exact hne
        rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
      have hokL : decide (A (Sum.inr p) (Sum.inl (p.1, ⟨0, hpos⟩, p.2, 0)) = 1) = false := by
        by_contra hne
        have hmem : (Sum.inr p, Sum.inl (p.1, ⟨0, hpos⟩, p.2, 0)) ∈ pairErr p := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heL, ?_⟩, rfl⟩
          rw [hval_pairL _ (mem_pairLEdges.mpr ⟨p.1, p.2, hpos, hlt, rfl⟩)]; exact hne
        rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
      have hokR : decide (A (Sum.inl (p.2, ⟨0, hpos⟩, p.1, 0)) (Sum.inr p) = 1) = false := by
        by_contra hne
        have hmem : (Sum.inl (p.2, ⟨0, hpos⟩, p.1, 0), Sum.inr p) ∈ pairErr p := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨heR, ?_⟩, rfl⟩
          rw [hval_pairR _ (mem_pairREdges.mpr ⟨p.1, p.2, hpos, hlt, rfl⟩)]; exact hne
        rw [hemp] at hmem; exact Finset.notMem_empty _ hmem
      rw [hA] at hokAsk hokL hokR
      have h1 := (symp_eq_one_iff _ _).mp (of_decide_eq_true hokAsk)
      have hL0 : symp (U (Sum.inr p)) (V (Sum.inl (p.1, ⟨0, hpos⟩, p.2, 0))) = 0 :=
        zmod2_eq_zero_of_decide_eq_false hokL
      have hR0 : symp (U (Sum.inl (p.2, ⟨0, hpos⟩, p.1, 0))) (V (Sum.inr p)) = 0 :=
        zmod2_eq_zero_of_decide_eq_false hokR
      rw [hv1] at hL0
      rw [hu2] at hR0
      rcases (symp_eq_zero_iff _ _).mp hL0 with h | h | hUL
      · exact h1.1 h
      · exact hne0 h
      · rcases (symp_eq_zero_iff _ _).mp hR0 with h | h | hVR
        · exact hne0 h
        · exact h1.2.1 h
        · exact h1.2.2 (hUL.trans hVR)
    let badAll : Finset (Fin k × Fin k) :=
      Finset.univ.biUnion (fun u : Fin k => (badSlot u).image (fun b => (u, b)))
    have hbad_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin k))
        (fun u : Fin k => (badSlot u).image (fun b => (u, b))) := by
      intro u₁ _ u₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q h1 h2
      rcases Finset.mem_image.mp h1 with ⟨b₁, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨b₂, _, heq⟩
      exact hne (Prod.mk.inj heq).1.symm
    have hbadAll_card : badAll.card = ∑ u : Fin k, (badSlot u).card := by
      dsimp only [badAll]
      rw [Finset.card_biUnion hbad_disj]
      refine Finset.sum_congr rfl (fun u _ => Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2))
    have hD_bad_le : D_badL.card + D_badR.card ≤ badAll.card := by
      let swapR : Finset (Fin k × Fin k) := D_badR.image Prod.swap
      have hdisj_LR : Disjoint D_badL swapR := by
        rw [Finset.disjoint_left]
        intro q hL hR
        have hltL : q.1 < q.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hL).1).2.1
        rcases Finset.mem_image.mp hR with ⟨p, hp, rfl⟩
        have hltR : p.1 < p.2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1
        exact lt_asymm hltL hltR
      have hsub_LR : D_badL ∪ swapR ⊆ badAll := by
        intro q hq
        rcases Finset.mem_union.mp hq with hL | hR
        · have hb := (Finset.mem_filter.mp hL).2
          exact Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨q.2, hb, rfl⟩⟩
        · rcases Finset.mem_image.mp hR with ⟨p, hp, rfl⟩
          have hb := (Finset.mem_filter.mp hp).2.2
          exact Finset.mem_biUnion.mpr ⟨p.2, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.1, hb, rfl⟩⟩
      have hswap_card : swapR.card = D_badR.card :=
        Finset.card_image_of_injective _ Prod.swap_injective
      rw [← hswap_card, ← Finset.card_union_of_disjoint hdisj_LR]
      exact Finset.card_le_card hsub_LR
    have hgrid_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin k)) gridErr := by
      intro u₁ _ u₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e h1 h2
      have hp1 := (Finset.mem_filter.mp h1).2
      have hp2 := (Finset.mem_filter.mp h2).2
      cases e with
      | mk x y =>
        cases x with
        | inl gx =>
          rcases gx with ⟨u', _, _, _⟩
          cases y with
          | inl _ => exact hne (hp1.symm.trans hp2)
          | inr _ => exact False.elim hp1
        | inr _ => exact False.elim hp1
    have hpair_disj : Set.PairwiseDisjoint D_good pairErr := by
      intro p₁ _ p₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e h1 h2
      have hp1 := (Finset.mem_filter.mp h1).2
      have hp2 := (Finset.mem_filter.mp h2).2
      cases e with
      | mk x y =>
        cases x with
        | inl _ =>
          cases y with
          | inl _ => exact False.elim hp1
          | inr _ => exact hne (hp1.symm.trans hp2)
        | inr _ =>
          cases y with
          | inl _ => exact hne (hp1.symm.trans hp2)
          | inr _ => exact hne (hp1.symm.trans hp2)
    have hgp_disj : Disjoint (Finset.univ.biUnion gridErr) (D_good.biUnion pairErr) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      rcases Finset.mem_biUnion.mp h1 with ⟨u, _, hu⟩
      rcases Finset.mem_biUnion.mp h2 with ⟨p, _, hp⟩
      have hgu := (Finset.mem_filter.mp hu).2
      have hpp := (Finset.mem_filter.mp hp).2
      cases e with
      | mk x y =>
        cases x with
        | inl _ =>
          cases y with
          | inl _ => exact False.elim hpp
          | inr _ => exact False.elim hgu
        | inr _ => exact False.elim hgu
    have hsub_err : (Finset.univ.biUnion gridErr) ∪ (D_good.biUnion pairErr) ⊆ errSet := by
      intro e he
      rcases Finset.mem_union.mp he with h1 | h2
      · rcases Finset.mem_biUnion.mp h1 with ⟨u, _, hu⟩
        exact (Finset.mem_filter.mp hu).1
      · rcases Finset.mem_biUnion.mp h2 with ⟨p, _, hp⟩
        exact (Finset.mem_filter.mp hp).1
    have hDgood_le : D_good.card ≤ (D_good.biUnion pairErr).card := by
      rw [Finset.card_biUnion hpair_disj]
      calc D_good.card = ∑ _p ∈ D_good, 1 := by simp
        _ ≤ ∑ p ∈ D_good, (pairErr p).card := Finset.sum_le_sum hpair_good
    have hD_le_sum : Dset.card ≤ D_badL.card + D_badR.card + D_good.card := by
      calc Dset.card ≤ (D_badL ∪ D_badR ∪ D_good).card := Finset.card_le_card hD_cov
        _ ≤ (D_badL ∪ D_badR).card + D_good.card := Finset.card_union_le _ _
        _ ≤ D_badL.card + D_badR.card + D_good.card := by
            have := Finset.card_union_le D_badL D_badR; omega
    calc Dset.card ≤ D_badL.card + D_badR.card + D_good.card := hD_le_sum
      _ ≤ (∑ u : Fin k, (badSlot u).card) + (D_good.biUnion pairErr).card := by omega
      _ ≤ (∑ u : Fin k, (gridErr u).card) + (D_good.biUnion pairErr).card := by
          have := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hbad_le_grid u); omega
      _ = (Finset.univ.biUnion gridErr).card + (D_good.biUnion pairErr).card := by
          rw [Finset.card_biUnion hgrid_disj]
      _ = ((Finset.univ.biUnion gridErr) ∪ (D_good.biUnion pairErr)).card :=
          (Finset.card_union_of_disjoint hgp_disj).symm
      _ ≤ errSet.card := Finset.card_le_card hsub_err
  · intro c
    let U : SideIdx k → ZMod 2 × ZMod 2
      | Sum.inl (u, _, _, p) => colVec (fin3Add (c u) p)
      | Sum.inr (i, j) => if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0)
    let V : SideIdx k → ZMod 2 × ZMod 2
      | Sum.inl (u, _, _, q) => colVec (fin3Add (c u) q)
      | Sum.inr (i, j) => if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)
    let A : Matrix (SideIdx k) (SideIdx k) (ZMod 2) := Matrix.of (fun x y => symp (U x) (V y))
    refine ⟨A, rank_symp_le_two U V, ?_⟩
    have hfilt_eq : (allEdges k).filter (fun e => decide (A e.1 e.2 = 1) ≠ val e) =
        ((Finset.univ : Finset (Fin k × Fin k)).filter
          (fun p => p.1 < p.2 ∧ g p.1 p.2 = true ∧ c p.1 = c p.2)).image
          (fun p => (Sum.inr p, Sum.inr p)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨heA, hne⟩
        dsimp only [allEdges] at heA
        simp only [Finset.mem_union] at heA
        rcases heA with ((((h | h) | h) | h) | h) | h
        · exfalso; apply hne
          rw [hval_int _ h]
          rcases mem_intEdges.mp h with ⟨u, a, b, p, q, rfl⟩
          change decide (symp (colVec (fin3Add (c u) p)) (colVec (fin3Add (c u) q)) = 1) = decide (p ≠ q)
          rw [symp_colVec, decide_eq_decide]
          exact fin3Add_ne_iff (c u) p q
        · exfalso; apply hne
          rw [hval_horiz _ h]
          rcases mem_horizEdges.mp h with ⟨u, a, b, hlt, q, rfl⟩
          change decide (symp (colVec (fin3Add (c u) 0)) (colVec (fin3Add (c u) ⟨q.val, by omega⟩)) = 1) =
            decide ((0 : Fin 3) ≠ ⟨q.val, by omega⟩)
          rw [symp_colVec, decide_eq_decide]
          exact fin3Add_ne_iff (c u) 0 ⟨q.val, by omega⟩
        · exfalso; apply hne
          rw [hval_vert _ h]
          rcases mem_vertEdges.mp h with ⟨u, a, b, hlt, q, rfl⟩
          change decide (symp (colVec (fin3Add (c u) 0)) (colVec (fin3Add (c u) ⟨q.val, by omega⟩)) = 1) =
            decide ((0 : Fin 3) ≠ ⟨q.val, by omega⟩)
          rw [symp_colVec, decide_eq_decide]
          exact fin3Add_ne_iff (c u) 0 ⟨q.val, by omega⟩
        · rcases mem_pairAskEdges.mp h with ⟨i, j, hij, rfl⟩
          rw [hval_pairAsk i j hij] at hne
          refine ⟨(i, j), ⟨hij, ?_, ?_⟩, rfl⟩
          · by_contra hgf
            have hgf' : g i j = false := Bool.eq_false_iff.mpr hgf
            apply hne
            change decide (symp (if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0))
              (if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)) = 1) = g i j
            simp [hgf', symp]
          · by_contra hcne
            apply hne
            by_cases hgt : g i j = true
            · change decide (symp (if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0))
                (if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)) = 1) = g i j
              simp only [hgt, hcne, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
              rw [symp_colVec]
              exact decide_eq_true hcne
            · have hgf' : g i j = false := Bool.eq_false_iff.mpr hgt
              change decide (symp (if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0))
                (if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)) = 1) = g i j
              simp [hgf', symp]
        · exfalso; apply hne
          rw [hval_pairL _ h]
          rcases mem_pairLEdges.mp h with ⟨i, j, hpos, hij, rfl⟩
          change decide (symp (if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0))
            (colVec (fin3Add (c i) 0)) = 1) = false
          rw [fin3Add_zero]
          split_ifs
          · rw [symp_colVec]; simp
          · simp [symp]
        · exfalso; apply hne
          rw [hval_pairR _ h]
          rcases mem_pairREdges.mp h with ⟨i, j, hpos, hij, rfl⟩
          change decide (symp (colVec (fin3Add (c j) 0))
            (if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)) = 1) = false
          rw [fin3Add_zero]
          split_ifs
          · rw [symp_colVec]; simp
          · simp [symp]
      · rintro ⟨⟨i, j⟩, ⟨hij, hgt, hceq⟩, rfl⟩
        refine ⟨?_, ?_⟩
        · dsimp only [allEdges]; simp [mem_pairAskEdges.mpr ⟨i, j, hij, rfl⟩]
        · rw [hval_pairAsk i j hij, hgt]
          change decide (symp (if g i j = true ∧ c i ≠ c j then colVec (c i) else (0, 0))
            (if g i j = true ∧ c i ≠ c j then colVec (c j) else (0, 0)) = 1) ≠ true
          simp [hceq, symp]
    rw [hfilt_eq]
    exact Finset.card_image_of_injective _ (fun _ _ h => Sum.inr.inj (Prod.mk.inj h).1)

private lemma main_proof (k : ℕ) :
    let K := Fin k
    let defect := fun (g : K → K → Bool) (c : K → Fin 3) =>
      ((Finset.univ : Finset (K × K)).filter
        (fun p => p.1 < p.2 ∧ g p.1 p.2 = true ∧ c p.1 = c p.2)).card
    ∃ l r : ℕ, l + r ≤ 32 * (k + 1) ^ 3 ∧
      ∃ (E : Finset (Fin l × Fin r)) (base : Fin l × Fin r → Bool)
        (ask : Fin l × Fin r → Option (K × K))
        (decode : Matrix (Fin l) (Fin r) (ZMod 2) → K → Fin 3),
        E.card ≤ 32 * (k + 1) ^ 3 ∧
        (∀ i, (E.filter (fun e => e.1 = i)).card ≤ 18) ∧
        (∀ j, (E.filter (fun e => e.2 = j)).card ≤ 18) ∧
        (∀ e ∈ E, ∀ i j, ask e = some (i, j) → i < j) ∧
        (∀ i j : K, i < j → ∃! e : Fin l × Fin r, e ∈ E ∧ ask e = some (i, j)) ∧
        ∀ g : K → K → Bool,
          let val := fun e => (ask e).elim (base e) (fun p => g p.1 p.2)
          let err := fun (A : Matrix (Fin l) (Fin r) (ZMod 2)) =>
            (E.filter (fun e => decide (A e.1 e.2 = 1) ≠ val e)).card
          (∀ A, Matrix.rank A ≤ 2 → defect g (decode A) ≤ err A) ∧
          ∀ c : K → Fin 3, ∃ A, Matrix.rank A ≤ 2 ∧ err A = defect g c := by
  classical
  dsimp only
  let m := 3 * k ^ 3 + k ^ 2
  have hcardS : Fintype.card (SideIdx k) = m := by
    simp only [SideIdx, GridIdx, PairIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, m]
    ring
  let eS : SideIdx k ≃ Fin m := Fintype.equivOfCardEq (by rw [hcardS, Fintype.card_fin])
  let eProd : (SideIdx k × SideIdx k) ≃ (Fin m × Fin m) := Equiv.prodCongr eS eS
  obtain ⟨decodeS, hdecodeS⟩ := rank_le_two_decode_side k
  refine ⟨m, m, by have : (k + 1) ^ 3 = k ^ 3 + 3 * k ^ 2 + 3 * k + 1 := (by ring); dsimp only [m]; omega,
    (allEdges k).map eProd.toEmbedding,
    fun e => baseFun k (eProd.symm e),
    fun e => askFun k (eProd.symm e),
    fun A => decodeS (Matrix.of (fun x y => A (eS x) (eS y))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    exact card_allEdges_le k
  · intro i
    have hbij : (((allEdges k).map eProd.toEmbedding).filter (fun e => e.1 = i)).card =
        ((allEdges k).filter (fun e => e.1 = eS.symm i)).card := by
      refine Finset.card_bij (fun e _ => eProd.symm e) ?_ ?_ ?_
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨hm, h1⟩
        rcases Finset.mem_map.mp hm with ⟨e₀, he₀, rfl⟩
        refine Finset.mem_filter.mpr ⟨by simpa using he₀, ?_⟩
        simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
        have h1' : eS e₀.1 = i := h1
        exact eS.injective (h1'.trans (eS.apply_symm_apply i).symm)
      · intro _ _ _ _ h; exact eProd.symm.injective h
      · intro e₀ he₀
        rcases Finset.mem_filter.mp he₀ with ⟨hm, h1⟩
        refine ⟨eProd e₀, Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨e₀, hm, rfl⟩, ?_⟩,
          eProd.symm_apply_apply e₀⟩
        change eS e₀.1 = i
        rw [h1, eS.apply_symm_apply]
    rw [hbij]
    exact row_deg_le k (eS.symm i)
  · intro j
    have hbij : (((allEdges k).map eProd.toEmbedding).filter (fun e => e.2 = j)).card =
        ((allEdges k).filter (fun e => e.2 = eS.symm j)).card := by
      refine Finset.card_bij (fun e _ => eProd.symm e) ?_ ?_ ?_
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨hm, h2⟩
        rcases Finset.mem_map.mp hm with ⟨e₀, he₀, rfl⟩
        refine Finset.mem_filter.mpr ⟨by simpa using he₀, ?_⟩
        simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
        have h2' : eS e₀.2 = j := h2
        exact eS.injective (h2'.trans (eS.apply_symm_apply j).symm)
      · intro _ _ _ _ h; exact eProd.symm.injective h
      · intro e₀ he₀
        rcases Finset.mem_filter.mp he₀ with ⟨hm, h2⟩
        refine ⟨eProd e₀, Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨e₀, hm, rfl⟩, ?_⟩,
          eProd.symm_apply_apply e₀⟩
        change eS e₀.2 = j
        rw [h2, eS.apply_symm_apply]
    rw [hbij]
    exact col_deg_le k (eS.symm j)
  · intro e _ i j hask
    dsimp only at hask
    cases he : eProd.symm e with
    | mk x y =>
      rw [he] at hask
      cases x with
      | inl _ => simp [askFun] at hask
      | inr p =>
        cases y with
        | inl _ => simp [askFun] at hask
        | inr _ =>
          simp only [askFun] at hask
          split_ifs at hask with hlt
          · injection hask with hp
            rcases Prod.mk.inj hp with ⟨rfl, rfl⟩
            exact hlt
  · intro i j hij
    refine ⟨eProd (Sum.inr (i, j), Sum.inr (i, j)), ?_, ?_⟩
    · refine ⟨Finset.mem_map.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · simp only [allEdges, Finset.mem_union]
        left; left; right; exact mem_pairAskEdges.mpr ⟨i, j, hij, rfl⟩
      · simp [askFun, hij]
    · intro e ⟨heM, hask⟩
      rcases Finset.mem_map.mp heM with ⟨e₀, he₀, rfl⟩
      dsimp only at hask
      rw [Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at hask
      dsimp only [allEdges] at he₀
      simp only [Finset.mem_union] at he₀
      rcases he₀ with ((((h | h) | h) | h) | h) | h
      · rcases mem_intEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp [askFun] at hask
      · rcases mem_horizEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp [askFun] at hask
      · rcases mem_vertEdges.mp h with ⟨_, _, _, _, _, rfl⟩; simp [askFun] at hask
      · rcases mem_pairAskEdges.mp h with ⟨i', j', hij', rfl⟩
        simp only [askFun, hij', ↓reduceIte, Option.some.injEq] at hask
        rcases Prod.mk.inj hask with ⟨rfl, rfl⟩
        rfl
      · rcases mem_pairLEdges.mp h with ⟨_, _, _, _, rfl⟩; simp [askFun] at hask
      · rcases mem_pairREdges.mp h with ⟨_, _, _, _, rfl⟩; simp [askFun] at hask
  · intro g
    obtain ⟨hlo, hhi⟩ := hdecodeS g
    have hrank_eq : ∀ (A : Matrix (Fin m) (Fin m) (ZMod 2)),
        Matrix.rank (Matrix.of (fun x y => A (eS x) (eS y))) = Matrix.rank A := by
      intro A
      let B : Matrix (SideIdx k) (SideIdx k) (ZMod 2) := Matrix.of (fun x y => A (eS x) (eS y))
      let fL : (SideIdx k → ZMod 2) ≃ₗ[ZMod 2] (Fin m → ZMod 2) :=
        LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) eS.symm
      have hmap : Submodule.map fL.toLinearMap (LinearMap.range B.mulVecLin) =
          LinearMap.range A.mulVecLin := by
        ext v
        simp only [Submodule.mem_map, LinearMap.mem_range]
        constructor
        · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
          refine ⟨fun j => w (eS.symm j), ?_⟩
          funext i
          change ∑ j : Fin m, A i j * w (eS.symm j) = ∑ y : SideIdx k, A (eS (eS.symm i)) (eS y) * w y
          rw [eS.apply_symm_apply, ← Equiv.sum_comp eS.symm]
          refine Finset.sum_congr rfl (fun j _ => by simp)
        · rintro ⟨w, rfl⟩
          refine ⟨B.mulVecLin (fun y => w (eS y)), ⟨fun y => w (eS y), rfl⟩, ?_⟩
          funext i
          change ∑ y : SideIdx k, A (eS (eS.symm i)) (eS y) * w (eS y) = ∑ j : Fin m, A i j * w j
          rw [eS.apply_symm_apply]
          exact Equiv.sum_comp eS (fun j => A i j * w j)
      change Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) =
        Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin)
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq fL _).symm
    have herr_eq : ∀ (A : Matrix (Fin m) (Fin m) (ZMod 2)),
        (((allEdges k).map eProd.toEmbedding).filter (fun e =>
          decide (A e.1 e.2 = 1) ≠ (askFun k (eProd.symm e)).elim (baseFun k (eProd.symm e)) (fun p => g p.1 p.2))).card =
        ((allEdges k).filter (fun e =>
          decide ((Matrix.of (fun x y => A (eS x) (eS y))) e.1 e.2 = 1) ≠
            (askFun k e).elim (baseFun k e) (fun p => g p.1 p.2))).card := by
      intro A
      refine Finset.card_bij (fun e _ => eProd.symm e) ?_ ?_ ?_
      · intro e he
        rcases Finset.mem_filter.mp he with ⟨hm, hne⟩
        rcases Finset.mem_map.mp hm with ⟨e₀, he₀, rfl⟩
        simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at hne ⊢
        exact Finset.mem_filter.mpr ⟨he₀, hne⟩
      · intro _ _ _ _ h; exact eProd.symm.injective h
      · intro e₀ he₀
        rcases Finset.mem_filter.mp he₀ with ⟨hm, hne⟩
        refine ⟨eProd e₀, Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨e₀, hm, rfl⟩, ?_⟩,
          eProd.symm_apply_apply e₀⟩
        simp only [Equiv.symm_apply_apply]
        exact hne
    constructor
    · intro A hA
      rw [herr_eq A]
      exact hlo (Matrix.of (fun x y => A (eS x) (eS y))) (by rw [hrank_eq A]; exact hA)
    · intro c
      obtain ⟨B, hBr, hBerr⟩ := hhi c
      let A : Matrix (Fin m) (Fin m) (ZMod 2) := Matrix.of (fun i j => B (eS.symm i) (eS.symm j))
      have hBA : Matrix.of (fun x y => A (eS x) (eS y)) = B := by
        ext x y; change B (eS.symm (eS x)) (eS.symm (eS y)) = B x y; simp
      refine ⟨A, ?_, ?_⟩
      · rw [← hrank_eq A, hBA]; exact hBr
      · rw [herr_eq A, hBA]; exact hBerr

end PEqualNP.Outside.L_lib_1056_aux

theorem PEqualNP.Outside.L_lib_1056 :
  ∀ k : ℕ,
    let K := Fin k
    let defect := fun (g : K → K → Bool) (c : K → Fin 3) =>
      ((Finset.univ : Finset (K × K)).filter
        (fun p => p.1 < p.2 ∧ g p.1 p.2 = true ∧ c p.1 = c p.2)).card
    ∃ l r : ℕ, l+r ≤ 32*(k+1)^3 ∧
      ∃ (E : Finset (Fin l × Fin r)) (base : Fin l × Fin r → Bool)
        (ask : Fin l × Fin r → Option (K × K))
        (decode : Matrix (Fin l) (Fin r) (ZMod 2) → K → Fin 3),
        E.card ≤ 32*(k+1)^3 ∧
        (∀ i, (E.filter (fun e => e.1 = i)).card ≤ 18) ∧
        (∀ j, (E.filter (fun e => e.2 = j)).card ≤ 18) ∧
        (∀ e ∈ E, ∀ i j, ask e = some (i,j) → i < j) ∧
        (∀ i j : K, i < j → ∃! e : Fin l × Fin r, e ∈ E ∧ ask e = some (i,j)) ∧
        ∀ g : K → K → Bool,
          let val := fun e => (ask e).elim (base e) (fun p => g p.1 p.2)
          let err := fun (A : Matrix (Fin l) (Fin r) (ZMod 2)) =>
            (E.filter (fun e => decide (A e.1 e.2 = 1) ≠ val e)).card
          (∀ A, Matrix.rank A ≤ 2 → defect g (decode A) ≤ err A) ∧
          ∀ c : K → Fin 3, ∃ A, Matrix.rank A ≤ 2 ∧ err A = defect g c := by
  exact PEqualNP.Outside.L_lib_1056_aux.main_proof
