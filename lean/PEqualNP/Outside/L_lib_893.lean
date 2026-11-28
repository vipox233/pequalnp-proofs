import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_893

def pol {n : ℕ} (g : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (x y : Fin n → ZMod 2) :
    Fin n → ZMod 2 :=
  g (x + y) - g x - g y + g 0

def unitv {n : ℕ} (i : Fin n) : Fin n → ZMod 2 := fun h => if h = i then 1 else 0

def preS {n m : ℕ} (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inj : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (Q : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)) :=
  {s | (s.1, g s.2 - g 0 + inj s.1) ∈ Q ∧ ∀ i : Fin n, ((0 : Fin m → ZMod 2), pol g (unitv i) s.2) ∈ Q}

section round

variable {n m : ℕ} (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
  (inj : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
  (hg : ∀ x y z, pol g (x + y) z = pol g x z + pol g y z)

theorem pol_zero_left (y : Fin n → ZMod 2) : pol g 0 y = 0 := by
  unfold pol; simp

theorem pol_symm (x y : Fin n → ZMod 2) : pol g x y = pol g y x := by
  unfold pol; rw [add_comm x y]; abel

include hg in
theorem pol_add_right (x y z : Fin n → ZMod 2) : pol g x (y + z) = pol g x y + pol g x z := by
  rw [pol_symm g x (y + z), hg, pol_symm g y x, pol_symm g z x]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem single_eq (i : Fin n) (a : ZMod 2) :
    Pi.single i a = (if a = 0 then (0 : Fin n → ZMod 2) else unitv i) := by
  rcases zmod2_cases a with h | h
  · subst h; simp
  · subst h; funext h'; simp [unitv, Pi.single_apply]

theorem zero_pair_sum {ι : Type} (s : Finset ι) (v : ι → Fin n → ZMod 2) :
    ((0 : Fin m → ZMod 2), ∑ i ∈ s, v i) = ∑ i ∈ s, ((0 : Fin m → ZMod 2), v i) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

include hg in
theorem polar_mem_all (Q : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)))
    (d : Fin n → ZMod 2) (h : ∀ i, ((0 : Fin m → ZMod 2), pol g (unitv i) d) ∈ Q) :
    ∀ x, ((0 : Fin m → ZMod 2), pol g x d) ∈ Q := by
  intro x
  let φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) :=
    { toFun := fun x => pol g x d
      map_zero' := pol_zero_left g d
      map_add' := fun x y => hg x y d }
  have hx : x = ∑ i, Pi.single i (x i) := (Finset.univ_sum_single x).symm
  have : pol g x d = ∑ i, φ (Pi.single i (x i)) := by
    rw [← map_sum]; conv_lhs => rw [hx]
    rfl
  rw [this, zero_pair_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [single_eq]
  split_ifs
  · simp only [map_zero]; exact Q.zero_mem
  · exact h i

include hg in
theorem preS_submodule (Q : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    ∃ L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)),
      (L : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) = preS g inj Q := by
  have zero_in : (0 : (Fin m → ZMod 2) × (Fin n → ZMod 2)) ∈ preS g inj Q := by
    refine ⟨?_, fun i => ?_⟩
    · simp only [Prod.fst_zero, Prod.snd_zero, sub_self, map_zero, add_zero]
      exact Q.zero_mem
    · rw [Prod.snd_zero, pol_symm, pol_zero_left]; exact Q.zero_mem
  have add_in : ∀ s t, s ∈ preS g inj Q → t ∈ preS g inj Q → s + t ∈ preS g inj Q := by
    intro s t hs ht
    refine ⟨?_, fun i => ?_⟩
    · have e : ((s + t).1, g (s + t).2 - g 0 + inj (s + t).1) =
          (s.1, g s.2 - g 0 + inj s.1) + (t.1, g t.2 - g 0 + inj t.1) +
            ((0 : Fin m → ZMod 2), pol g s.2 t.2) := by
        ext1
        · simp
        · simp only [Prod.fst_add, Prod.snd_add, map_add, pol]; abel
      rw [e]
      exact Q.add_mem (Q.add_mem hs.1 ht.1) (polar_mem_all g hg Q t.2 ht.2 s.2)
    · have e : ((0 : Fin m → ZMod 2), pol g (unitv i) (s + t).2) =
          ((0 : Fin m → ZMod 2), pol g (unitv i) s.2) + ((0 : Fin m → ZMod 2), pol g (unitv i) t.2) := by
        rw [Prod.snd_add, pol_add_right g hg]; ext1 <;> simp
      rw [e]; exact Q.add_mem (hs.2 i) (ht.2 i)
  refine ⟨{ carrier := preS g inj Q, zero_mem' := zero_in, add_mem' := fun {a b} ha hb => add_in a b ha hb, smul_mem' := fun c x hx => ?_ }, rfl⟩
  rcases zmod2_cases c with h | h
  · subst h; rw [zero_smul]; exact zero_in
  · subst h; rw [one_smul]; exact hx

theorem round_eq (p : Fin m → ZMod 2) (d b : Fin n → ZMod 2) :
    (p, g (b + d) - g b + inj p) = (p, g d - g 0 + inj p) + ((0 : Fin m → ZMod 2), pol g b d) := by
  ext1
  · simp
  · simp only [Prod.snd_add, pol]; abel

include hg in
theorem preS_iff (Q : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) :
    (p, d) ∈ preS g inj Q ↔ ∀ b, (p, g (b + d) - g b + inj p) ∈ Q := by
  constructor
  · rintro ⟨h1, h2⟩ b
    rw [round_eq]
    exact Q.add_mem h1 (polar_mem_all g hg Q d h2 b)
  · intro h
    have h0 : (p, g d - g 0 + inj p) ∈ Q := by simpa using h 0
    refine ⟨h0, fun i => ?_⟩
    have e : ((0 : Fin m → ZMod 2), pol g (unitv i) d) =
        (p, g (unitv i + d) - g (unitv i) + inj p) - (p, g d - g 0 + inj p) := by
      rw [round_eq]; simp
    rw [e]; exact Q.sub_mem (h _) h0

theorem card_W : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
  simp [ZMod.card]

include hg in
theorem preS_count (Q : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) (hn : (p, d) ∉ preS g inj Q) :
    2 ^ n ≤ 2 * Nat.card {b : Fin n → ZMod 2 // (p, g (b + d) - g b + inj p) ∉ Q} := by
  classical
  set Good : (Fin n → ZMod 2) → Prop := fun b => (p, g (b + d) - g b + inj p) ∈ Q with hGood
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → ZMod 2))) Good
  rw [Finset.card_univ, card_W] at hsplit
  by_cases hc : ∃ c, ((0 : Fin m → ZMod 2), pol g c d) ∉ Q
  · obtain ⟨c, hc⟩ := hc
    have hle : (Finset.univ.filter Good).card ≤ (Finset.univ.filter fun b => ¬ Good b).card := by
      refine Finset.card_le_card_of_injOn (fun b => b + c) (fun b hb => ?_) (fun a _ b _ h => by simpa using h)
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      intro hb2
      apply hc
      have e : ((0 : Fin m → ZMod 2), pol g c d) =
          (p, g (b + c + d) - g (b + c) + inj p) - (p, g (b + d) - g b + inj p) := by
        rw [round_eq g inj p d (b + c), round_eq g inj p d b, hg]; ext1 <;> simp
      rw [e]; exact Q.sub_mem hb2 hb
    have : (Finset.univ.filter fun b => ¬ (p, g (b + d) - g b + inj p) ∈ Q) =
        Finset.univ.filter fun b => ¬ Good b := rfl
    rw [this]; omega
  · push Not at hc
    have hall : ∀ b, ¬ Good b := by
      intro b hb
      apply hn
      refine ⟨?_, fun i => hc _⟩
      have e : (p, g d - g 0 + inj p) = (p, g (b + d) - g b + inj p) - ((0 : Fin m → ZMod 2), pol g b d) := by
        rw [round_eq]; simp
      rw [e]; exact Q.sub_mem hb (hc b)
    have : (Finset.univ.filter Good).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun b _ => hall b
    have h2 : (Finset.univ.filter fun b => ¬ (p, g (b + d) - g b + inj p) ∈ Q) =
        Finset.univ.filter fun b => ¬ Good b := rfl
    rw [h2]; omega

end round

def startS {n m : ℕ} (r : ℕ) (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (T : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)) :=
  (List.finRange r).foldr (fun j Q => preS (f j) (inject j) Q) T

def finishS {n m : ℕ} (r : ℕ) (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) (base : Fin r → (Fin n → ZMod 2)) : Fin n → ZMod 2 :=
  (List.finRange r).foldl (fun v j => f j (base j + v) - f j (base j) + inject j p) d

theorem startS_zero {n m : ℕ} (f : Fin 0 → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin 0 → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) (T) :
    startS 0 f inject T = T := by
  simp [startS]

theorem finishS_zero {n m : ℕ} (f : Fin 0 → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin 0 → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) (p d base) :
    finishS 0 f inject p d base = d := by
  simp [finishS]

theorem startS_succ {n m r : ℕ} (f : Fin (r + 1) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin (r + 1) → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) (T) :
    startS (r + 1) f inject T =
      preS (f 0) (inject 0) (startS r (fun j => f j.succ) (fun j => inject j.succ) T) := by
  simp only [startS, List.finRange_succ, List.foldr_cons, List.foldr_map]

theorem finishS_succ {n m r : ℕ} (f : Fin (r + 1) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin (r + 1) → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))) (p d base) :
    finishS (r + 1) f inject p d base =
      finishS r (fun j => f j.succ) (fun j => inject j.succ) p
        (f 0 (base 0 + d) - f 0 (base 0) + inject 0 p) (fun j => base j.succ) := by
  simp only [finishS, List.finRange_succ, List.foldl_cons, List.foldl_map]

theorem card_split {n r : ℕ} (P : (Fin (r + 1) → (Fin n → ZMod 2)) → Prop) [DecidablePred P] :
    Nat.card {base // P base} =
      ∑ b : Fin n → ZMod 2, Nat.card {rest : Fin r → (Fin n → ZMod 2) // P (Fin.cons b rest)} := by
  classical
  simp only [Nat.card_eq_fintype_card]
  rw [← Fintype.card_congr ((Fin.consEquiv (fun _ : Fin (r + 1) => Fin n → ZMod 2)).subtypeEquiv
        (p := fun x : (Fin n → ZMod 2) × (Fin r → Fin n → ZMod 2) => P (Fin.cons x.1 x.2)) (q := P)
        (fun a => Iff.rfl))]
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.card_subtype, Finset.card_filter]

theorem main (n m : ℕ) : ∀ (r : ℕ) (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (_hf : ∀ j x y z, pol (f j) (x + y) z = pol (f j) x z + pol (f j) y z)
    (T : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))),
    (∃ L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)),
        (L : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) = startS r f inject T) ∧
    ∀ (p : Fin m → ZMod 2) (d : Fin n → ZMod 2),
      ((p, d) ∈ startS r f inject T ↔ ∀ base, (p, finishS r f inject p d base) ∈ T) ∧
      ((p, d) ∉ startS r f inject T → 2 ^ (n * r) ≤ 2 ^ r *
        Nat.card {base : Fin r → (Fin n → ZMod 2) // (p, finishS r f inject p d base) ∉ T}) := by
  intro r
  induction r with
  | zero =>
    intro f inject _ T
    refine ⟨⟨T, by rw [startS_zero]⟩, fun p d => ⟨?_, ?_⟩⟩
    · rw [startS_zero]; simp only [finishS_zero]
      exact ⟨fun h _ => h, fun h => h fun i => i.elim0⟩
    · intro h
      rw [startS_zero] at h
      simp only [finishS_zero, Nat.mul_zero, pow_zero, one_mul]
      have : Nonempty {base : Fin 0 → (Fin n → ZMod 2) // (p, d) ∉ T} := ⟨⟨fun i => i.elim0, h⟩⟩
      exact Nat.card_pos
  | succ r ih =>
    intro f inject hf T
    obtain ⟨⟨L, hL⟩, hrest⟩ := ih (fun j => f j.succ) (fun j => inject j.succ) (fun j => hf j.succ) T
    refine ⟨?_, fun p d => ⟨?_, ?_⟩⟩
    · rw [startS_succ, ← hL]; exact preS_submodule (f 0) (inject 0) (hf 0) L
    · rw [startS_succ, ← hL, preS_iff (f 0) (inject 0) (hf 0)]
      constructor
      · intro h base
        rw [finishS_succ]
        have h1 : (p, f 0 (base 0 + d) - f 0 (base 0) + inject 0 p) ∈
            startS r (fun j => f j.succ) (fun j => inject j.succ) T := by
          rw [← hL]; exact h (base 0)
        exact ((hrest p _).1.1 h1) _
      · intro h b
        show (p, f 0 (b + d) - f 0 b + inject 0 p) ∈ (L : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)))
        rw [hL, (hrest p _).1]
        intro rest
        have := h (Fin.cons b rest)
        rw [finishS_succ] at this
        simpa using this
    · intro hn
      rw [startS_succ, ← hL] at hn
      have h0 := preS_count (f 0) (inject 0) (hf 0) L p d hn
      classical
      rw [card_split]
      set c : (Fin n → ZMod 2) → ℕ := fun b => Nat.card {rest : Fin r → (Fin n → ZMod 2) //
        (p, finishS (r + 1) f inject p d (Fin.cons b rest)) ∉ T} with hc
      set B := Finset.univ.filter fun b : Fin n → ZMod 2 => (p, f 0 (b + d) - f 0 b + inject 0 p) ∉ L
      have hB : Nat.card {b : Fin n → ZMod 2 // (p, f 0 (b + d) - f 0 b + inject 0 p) ∉ L} = B.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hcb : ∀ b ∈ B, 2 ^ (n * r) ≤ 2 ^ r * c b := by
        intro b hb
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hb' : (p, f 0 (b + d) - f 0 b + inject 0 p) ∉ startS r (fun j => f j.succ) (fun j => inject j.succ) T := by
          rw [← hL]; exact hb
        have := (hrest p _).2 hb'
        simp only [hc, finishS_succ]
        simpa using this
      have hsum : B.card * 2 ^ (n * r) ≤ 2 ^ r * ∑ b, c b := by
        calc B.card * 2 ^ (n * r) = ∑ b ∈ B, 2 ^ (n * r) := by simp
          _ ≤ ∑ b ∈ B, 2 ^ r * c b := Finset.sum_le_sum hcb
          _ = 2 ^ r * ∑ b ∈ B, c b := by rw [Finset.mul_sum]
          _ ≤ 2 ^ r * ∑ b, c b := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      rw [hB] at h0
      calc 2 ^ (n * (r + 1)) = 2 ^ n * 2 ^ (n * r) := by rw [Nat.mul_succ, pow_add, mul_comm]
        _ ≤ (2 * B.card) * 2 ^ (n * r) := Nat.mul_le_mul_right _ h0
        _ = 2 * (B.card * 2 ^ (n * r)) := by ring
        _ ≤ 2 * (2 ^ r * ∑ b, c b) := Nat.mul_le_mul_left _ hsum
        _ = 2 ^ (r + 1) * ∑ b, c b := by ring

end PEqualNP.Outside.L_lib_893

theorem PEqualNP.Outside.L_lib_893 : (∀ (n m r : ℕ),
  let F := ZMod 2
  let W := Fin n → F
  let P := Fin m → F
  ∀ (f : Fin r → W → W) (inject : Fin r → (P →ₗ[F] W))
    (target : Submodule F (P × W)),
    let polar := fun (j : Fin r) (x y : W) =>
      f j (x+y) - f j x - f j y + f j 0
    (∀ j x y z, polar j (x+y) z = polar j x z + polar j y z) →
    let unit := fun (i h : Fin n) => (if h=i then 1 else 0 : F)
    let pre := fun (j : Fin r) (Q : Set (P × W)) =>
      {s : P × W | (s.1, f j s.2 - f j 0 + inject j s.1) ∈ Q ∧
        ∀ i : Fin n, ((0 : P), polar j (unit i) s.2) ∈ Q}
    let start := (List.finRange r).foldr pre (target : Set (P × W))
    let finish := fun (p : P) (d : W) (base : Fin r → W) =>
      (List.finRange r).foldl (fun (v : W) (j : Fin r) =>
        f j (base j + v) - f j (base j) + inject j p) d
    (∃ L : Submodule F (P × W), (L : Set (P × W)) = start) ∧
    ∀ (p : P) (d : W),
      ((p,d) ∈ start ↔ ∀ base : Fin r → W, (p,finish p d base) ∈ target) ∧
      ((p,d) ∉ start → 2^(n*r) ≤ 2^r *
        Nat.card {base : Fin r → W // (p,finish p d base) ∉ target})) := by
  intro n m r F W P f inject target polar hpol unit pre start finish
  exact PEqualNP.Outside.L_lib_893.main n m r f inject hpol target
