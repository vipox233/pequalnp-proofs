import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1083_aux

open Finset

lemma pow_two_le_factorial (j : ℕ) (hj : 1 ≤ j) : 2 ^ (j - 1) ≤ j.factorial := by
  induction j with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      have h1 := ih (by omega)
      rw [Nat.factorial_succ, Nat.succ_sub_one]
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
      rw [h2]
      exact Nat.mul_le_mul (by omega) h1

lemma factorial_mul_choose_le_pow (q j : ℕ) : j.factorial * q.choose j ≤ q ^ j := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow q j

lemma add_one_pow_le_three_mul (q : ℕ) (hq : 0 < q) : (q + 1) ^ q ≤ 3 * q ^ q := by
  rw [add_comm, add_pow]
  have h0 : 0 ∈ Finset.range (q + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h0]
  simp only [Nat.choose_zero_right, pow_zero, one_pow, one_mul, Nat.sub_zero, Nat.cast_id]
  have hrest : ∑ j ∈ (Finset.range (q + 1)).erase 0, q ^ (q - j) * q.choose j ≤ 2 * q ^ q := by
    have hmul : 2 ^ (q - 1) * ∑ j ∈ (Finset.range (q + 1)).erase 0, q ^ (q - j) * q.choose j ≤
        2 ^ (q - 1) * (2 * q ^ q) := by
      rw [Finset.mul_sum]
      have hterm : ∀ j ∈ (Finset.range (q + 1)).erase 0,
          2 ^ (q - 1) * (q ^ (q - j) * q.choose j) ≤ 2 ^ (q - j) * q ^ q := by
        intro j hj
        have hj_pos : 1 ≤ j := by
          have := (Finset.mem_erase.mp hj).1
          omega
        have hj_le : j ≤ q := by
          have := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
          omega
        have h2split : 2 ^ (q - 1) = 2 ^ (q - j) * 2 ^ (j - 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hqsplit : q ^ (q - j) * q ^ j = q ^ q := by
          rw [← pow_add, Nat.sub_add_cancel hj_le]
        calc 2 ^ (q - 1) * (q ^ (q - j) * q.choose j)
            = 2 ^ (q - j) * (q ^ (q - j) * (2 ^ (j - 1) * q.choose j)) := by rw [h2split]; ring
          _ ≤ 2 ^ (q - j) * (q ^ (q - j) * (j.factorial * q.choose j)) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (pow_two_le_factorial j hj_pos)))
          _ ≤ 2 ^ (q - j) * (q ^ (q - j) * q ^ j) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (factorial_mul_choose_le_pow q j))
          _ = 2 ^ (q - j) * q ^ q := by rw [hqsplit]
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hgeom : ∑ j ∈ (Finset.range (q + 1)).erase 0, 2 ^ (q - j) ≤ 2 ^ q := by
        have hbij : ∑ j ∈ (Finset.range (q + 1)).erase 0, 2 ^ (q - j) =
            ∑ i ∈ Finset.range q, 2 ^ i := by
          apply Finset.sum_bij (fun j _ => q - j)
          · intro j hj
            have h1 := (Finset.mem_erase.mp hj).1
            have h2 := Finset.mem_range.mp (Finset.mem_erase.mp hj).2
            exact Finset.mem_range.mpr (by omega)
          · intro a ha b hb heq
            have ha2 := Finset.mem_range.mp (Finset.mem_erase.mp ha).2
            have hb2 := Finset.mem_range.mp (Finset.mem_erase.mp hb).2
            omega
          · intro i hi
            have hi' := Finset.mem_range.mp hi
            refine ⟨q - i, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩, by omega⟩
          · intro _ _; rfl
        rw [hbij]
        have hsum2 : ∀ m : ℕ, ∑ i ∈ Finset.range m, 2 ^ i + 1 = 2 ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm => rw [Finset.sum_range_succ, pow_succ]; omega
        have := hsum2 q
        omega
      have h2q : 2 ^ q = 2 ^ (q - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel hq]
        rw [pow_succ]
      calc (∑ j ∈ (Finset.range (q + 1)).erase 0, 2 ^ (q - j)) * q ^ q
          ≤ 2 ^ q * q ^ q := Nat.mul_le_mul_right _ hgeom
        _ = 2 ^ (q - 1) * (2 * q ^ q) := by rw [h2q]; ring
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  omega

lemma sum_two_pow_coll (t q a : ℕ) (hq : 0 < q) (u v : Fin t) (huv : u ≠ v) :
    ∑ hash : Fin a → Fin t → Fin q,
      2 ^ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i u = hash i v)).card =
      (q + 1) ^ a * q ^ (a * (t - 1)) := by
  have hterm : ∀ hash : Fin a → Fin t → Fin q,
      2 ^ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i u = hash i v)).card =
      ∏ i : Fin a, (if hash i u = hash i v then 2 else 1) := by
    intro hash
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (_ : Fin a) (f : Fin t → Fin q) => if f u = f v then 2 else 1)]
  have hsingle : ∑ f : Fin t → Fin q, (if f u = f v then 2 else 1) = (q + 1) * q ^ (t - 1) := by
    have hsplit : ∑ f : Fin t → Fin q, (if f u = f v then 2 else 1) =
        ∑ f : Fin t → Fin q, (1 + if f u = f v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> rfl
    rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hcard_eq : (∑ f : Fin t → Fin q, if f u = f v then 1 else 0) = q ^ (t - 1) := by
      rw [← Finset.card_filter]
      let S := (Finset.univ : Finset (Fin t)).erase v
      have hScard : S.card = t - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
      have huS : u ∈ S := Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩
      let e : {f : Fin t → Fin q // f u = f v} ≃ (S → Fin q) :=
        { toFun := fun f x => f.1 x.1
          invFun := fun g =>
            ⟨fun x => if h : x ∈ S then g ⟨x, h⟩ else g ⟨u, huS⟩, by
              have hvS : v ∉ S := Finset.notMem_erase v _
              simp [huS, hvS]⟩
          left_inv := fun f => by
            ext x
            by_cases hx : x ∈ S
            · simp [hx]
            · have hxv : x = v := by
                by_contra hne
                exact hx (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
              subst hxv
              simp [hx, f.2]
          right_inv := fun g => by
            ext x
            simp [x.2] }
      have h1 : ((Finset.univ : Finset (Fin t → Fin q)).filter (fun f => f u = f v)).card =
          Fintype.card {f : Fin t → Fin q // f u = f v} := by
        rw [Fintype.card_subtype]
      rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, hScard]
    rw [hcard_eq]
    have ht1 : 1 ≤ t := by
      have := u.isLt
      omega
    have hpow : q ^ t = q * q ^ (t - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel ht1]
      rw [pow_succ, mul_comm]
    rw [hpow]
    ring
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hsingle, mul_pow, ← pow_mul]
  ring

lemma exists_good_hash (t q : ℕ) (ht : 2 ≤ t) (hq : 0 < q) :
    let L := 1 + Nat.log 2 t
    let a := 8 * q * L
    let M := 16 * L
    ∃ hash : Fin a → Fin t → Fin q,
      ∀ u v : Fin t, u ≠ v →
        ((Finset.univ : Finset (Fin a)).filter (fun i => hash i u = hash i v)).card ≤ M := by
  intro L a M
  by_contra hall
  push_neg at hall
  let badPair : Fin t × Fin t → Finset (Fin a → Fin t → Fin q) := fun p =>
    (Finset.univ : Finset (Fin a → Fin t → Fin q)).filter (fun hash =>
      M < ((Finset.univ : Finset (Fin a)).filter (fun i => hash i p.1 = hash i p.2)).card)
  have hcov : (Finset.univ : Finset (Fin a → Fin t → Fin q)) ⊆
      ((Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2)).biUnion badPair := by
    intro hash _
    obtain ⟨u, v, huv, hgt⟩ := hall hash
    exact Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩⟩
  have hcard_le : (Finset.univ : Finset (Fin a → Fin t → Fin q)).card ≤
      ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2), (badPair p).card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have hpair_bd : ∀ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2),
      2 ^ (M + 1) * (badPair p).card ≤ 3 ^ (8 * L) * q ^ (a * t) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hmarkov : 2 ^ (M + 1) * (badPair p).card ≤
        ∑ hash : Fin a → Fin t → Fin q,
          2 ^ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i p.1 = hash i p.2)).card := by
      calc 2 ^ (M + 1) * (badPair p).card
          = ∑ _hash ∈ badPair p, 2 ^ (M + 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ hash ∈ badPair p,
              2 ^ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i p.1 = hash i p.2)).card := by
            apply Finset.sum_le_sum
            intro hash hhash
            have hgt : M + 1 ≤ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i p.1 = hash i p.2)).card :=
              (Finset.mem_filter.mp hhash).2
            exact Nat.pow_le_pow_right (by decide : 0 < 2) hgt
        _ ≤ ∑ hash : Fin a → Fin t → Fin q,
              2 ^ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i p.1 = hash i p.2)).card :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [sum_two_pow_coll t q a hq p.1 p.2 hne] at hmarkov
    have hqpow : (q + 1) ^ a ≤ 3 ^ (8 * L) * q ^ a := by
      have h1 := add_one_pow_le_three_mul q hq
      have h2 := Nat.pow_le_pow_left h1 (8 * L)
      rw [mul_pow, ← pow_mul, ← pow_mul] at h2
      have ha : q * (8 * L) = a := by dsimp [a]; ring
      rwa [ha] at h2
    have ht1 : 1 ≤ t := by omega
    have hmerge : q ^ a * q ^ (a * (t - 1)) = q ^ (a * t) := by
      rw [← pow_add]
      congr 1
      have : a + a * (t - 1) = a * (1 + (t - 1)) := by ring
      rw [this, Nat.add_sub_of_le ht1]
    calc 2 ^ (M + 1) * (badPair p).card
        ≤ (q + 1) ^ a * q ^ (a * (t - 1)) := hmarkov
      _ ≤ (3 ^ (8 * L) * q ^ a) * q ^ (a * (t - 1)) := Nat.mul_le_mul_right _ hqpow
      _ = 3 ^ (8 * L) * (q ^ a * q ^ (a * (t - 1))) := by ring
      _ = 3 ^ (8 * L) * q ^ (a * t) := by rw [hmerge]
  have hmul_sum : 2 ^ (M + 1) * q ^ (a * t) ≤
      (t * t) * (3 ^ (8 * L) * q ^ (a * t)) := by
    have huniv_card : (Finset.univ : Finset (Fin a → Fin t → Fin q)).card = q ^ (a * t) := by
      simp [Fintype.card_fun, ← pow_mul, mul_comm]
    calc 2 ^ (M + 1) * q ^ (a * t)
        = 2 ^ (M + 1) * (Finset.univ : Finset (Fin a → Fin t → Fin q)).card := by rw [huniv_card]
      _ ≤ 2 ^ (M + 1) * ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2), (badPair p).card :=
          Nat.mul_le_mul_left _ hcard_le
      _ = ∑ p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2), 2 ^ (M + 1) * (badPair p).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2), 3 ^ (8 * L) * q ^ (a * t) :=
          Finset.sum_le_sum hpair_bd
      _ = ((Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2)).card * (3 ^ (8 * L) * q ^ (a * t)) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (t * t) * (3 ^ (8 * L) * q ^ (a * t)) := by
          apply Nat.mul_le_mul_right
          calc ((Finset.univ : Finset (Fin t × Fin t)).filter (fun p => p.1 ≠ p.2)).card
              ≤ (Finset.univ : Finset (Fin t × Fin t)).card := Finset.card_filter_le _ _
            _ = t * t := by simp
  have hlt : t * t * 3 ^ (8 * L) < 2 ^ (M + 1) := by
    have ht_lt : t < 2 ^ L := by
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
      rw [Nat.succ_eq_add_one] at h
      have hL : Nat.log 2 t + 1 = L := by dsimp [L]; omega
      rwa [hL] at h
    have ht2 : t * t < 4 ^ L := by
      calc t * t < 2 ^ L * 2 ^ L := Nat.mul_lt_mul'' ht_lt ht_lt
        _ = (2 * 2) ^ L := (mul_pow 2 2 L).symm
        _ = 4 ^ L := rfl
    have h38 : 3 ^ (8 * L) ≤ 4 ^ (7 * L) := by
      rw [pow_mul, pow_mul]
      exact Nat.pow_le_pow_left (by decide : 3 ^ 8 ≤ 4 ^ 7) L
    have h48 : 4 ^ L * 4 ^ (7 * L) = 2 ^ M := by
      rw [← pow_add]
      have h1 : L + 7 * L = 8 * L := by ring
      rw [h1]
      have h4 : (4 : ℕ) = 2 ^ 2 := rfl
      rw [h4, ← pow_mul]
      congr 1
      dsimp [M]
      ring
    have hpos3 : 0 < 3 ^ (8 * L) := by positivity
    calc t * t * 3 ^ (8 * L)
        < 4 ^ L * 3 ^ (8 * L) := Nat.mul_lt_mul_of_pos_right ht2 hpos3
      _ ≤ 4 ^ L * 4 ^ (7 * L) := Nat.mul_le_mul_left _ h38
      _ = 2 ^ M := h48
      _ < 2 ^ (M + 1) := Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self M)
  have hqpos : 0 < q ^ (a * t) := Nat.pos_of_ne_zero (pow_ne_zero _ (Nat.pos_iff_ne_zero.mp hq))
  have hlt_mul : (t * t) * (3 ^ (8 * L) * q ^ (a * t)) < 2 ^ (M + 1) * q ^ (a * t) := by
    have : (t * t) * (3 ^ (8 * L) * q ^ (a * t)) = (t * t * 3 ^ (8 * L)) * q ^ (a * t) := by ring
    rw [this]
    exact Nat.mul_lt_mul_of_pos_right hlt hqpos
  omega

end PEqualNP.Outside.L_lib_1083_aux

theorem PEqualNP.Outside.L_lib_1083 : ∃ C : ℕ, 0 < C ∧ ∀ t k s : ℕ, 2 ≤ t → 0 < k → 0 < s →
  let q := 16*(k+1)*s
  let T := Fin t
  let Q := Fin q
  let Local := Fin k → Option (Q × Q)
  let mult := fun (P : Local) (x z : Q) =>
    (Finset.univ.filter (fun l => P l = some (x,z) ∨ P l = some (z,x))).card
  let clean := fun (P : Local) (x z : Q) =>
    ∀ l, P l ≠ some (x,x) ∧ P l ≠ some (z,z)
  ∃ (a : ℕ) (hash : Fin a → T → Q), 0 < a ∧ a ≤ C*q*(1+Nat.log 2 t) ∧
    ∀ (b D : ℕ) (enc : Local → Fin b → ℕ), D ≤ b →
      (∀ (P R : Local) (x z : Q), x ≠ z → clean P x z → clean R x z →
        mult P x z ≠ mult R x z →
        D ≤ (Finset.univ.filter (fun j => enc P j ≠ enc R j)).card) →
      ∀ (G : Fin k → Option (T × T)), (∀ l u, G l ≠ some (u,u)) →
      ∀ (y : Fin a → Fin b → Option ℕ),
        let proj := fun i l => (G l).map (fun e => (hash i e.1,hash i e.2))
        let err := ∑ i, (Finset.univ.filter (fun j => y i j ≠ none ∧
          y i j ≠ some (enc (proj i) j))).card
        let lost := ∑ i, (Finset.univ.filter (fun j => y i j = none)).card
        s*(2*err+lost)+2*a*b < s*a*D →
        ∀ (u v : T), u ≠ v →
          let truth := (Finset.univ.filter (fun l => G l = some (u,v) ∨ G l = some (v,u))).card
          let score := fun (m : ℕ) => ∑ i : Fin a,
            (Finset.univ : Finset Local).inf' Finset.univ_nonempty (fun P =>
              if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
                mult P (hash i u) (hash i v) = m then
                (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
              else b)
          ∀ m : Fin (k+1), m.val ≠ truth → score truth < score m.val := by
  refine ⟨8, by decide, ?_⟩
  intro t k s ht hk hs q T Q Local mult clean
  have hq : 0 < q := by dsimp [q]; positivity
  let L := 1 + Nat.log 2 t
  let a := 8 * q * L
  let M := 16 * L
  obtain ⟨hash, hhash⟩ := PEqualNP.Outside.L_lib_1083_aux.exists_good_hash t q ht hq
  refine ⟨a, hash, by dsimp [a, L]; positivity, by dsimp [a, L]; omega, ?_⟩
  intro b D enc hDb hdist G hGloop y proj err lost hbudget u v huv truth score m hm
  let good : Fin a → Prop := fun i =>
    hash i u ≠ hash i v ∧
    ∀ l : Fin k, ∀ e : T × T, G l = some e →
      (e.1 ≠ u → hash i e.1 ≠ hash i u) ∧
      (e.1 ≠ v → hash i e.1 ≠ hash i v) ∧
      (e.2 ≠ u → hash i e.2 ≠ hash i u) ∧
      (e.2 ≠ v → hash i e.2 ≠ hash i v)
  letI : DecidablePred good := Classical.decPred good
  let badSet : Finset (Fin a) := (Finset.univ : Finset (Fin a)).filter (fun i => ¬good i)
  have hbad_card : badSet.card ≤ (1 + 4 * k) * M := by
    let B0 := (Finset.univ : Finset (Fin a)).filter (fun i => hash i u = hash i v)
    let Bl : Fin k → Finset (Fin a) := fun l =>
      match G l with
      | none => ∅
      | some e =>
        ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ u ∧ hash i e.1 = hash i u)) ∪
        ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ v ∧ hash i e.1 = hash i v)) ∪
        ((Finset.univ : Finset (Fin a)).filter (fun i => e.2 ≠ u ∧ hash i e.2 = hash i u)) ∪
        ((Finset.univ : Finset (Fin a)).filter (fun i => e.2 ≠ v ∧ hash i e.2 = hash i v))
    have hsub : badSet ⊆ B0 ∪ (Finset.univ : Finset (Fin k)).biUnion Bl := by
      intro i hi
      have hng : ¬good i := (Finset.mem_filter.mp hi).2
      rw [Finset.mem_union]
      by_cases h0 : hash i u = hash i v
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h0⟩)
      · right
        have hex : ∃ l : Fin k, ∃ e : T × T, G l = some e ∧
            ((e.1 ≠ u ∧ hash i e.1 = hash i u) ∨
             (e.1 ≠ v ∧ hash i e.1 = hash i v) ∨
             (e.2 ≠ u ∧ hash i e.2 = hash i u) ∨
             (e.2 ≠ v ∧ hash i e.2 = hash i v)) := by
          by_contra hall
          apply hng
          refine ⟨h0, fun l e hGl => ?_⟩
          have h := not_exists.mp hall l
          have h' := not_exists.mp h e
          push_neg at h'
          have h'' := h' hGl
          exact ⟨fun h1 h2 => h''.1 h1 h2, fun h1 h2 => h''.2.1 h1 h2,
            fun h1 h2 => h''.2.2.1 h1 h2, fun h1 h2 => h''.2.2.2 h1 h2⟩
        obtain ⟨l, e, hGl, hor⟩ := hex
        refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, ?_⟩
        simp only [Bl, hGl]
        rcases hor with h1 | h2 | h3 | h4
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2⟩)))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h3⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h4⟩)
    have hB0 : B0.card ≤ M := hhash u v huv
    have hBl : ∀ l : Fin k, (Bl l).card ≤ 4 * M := by
      intro l
      cases hGl : G l with
      | none => simp [Bl, hGl]
      | some e =>
        simp only [Bl, hGl]
        have hf : ∀ (w1 w2 : T), ((Finset.univ : Finset (Fin a)).filter (fun i => w1 ≠ w2 ∧ hash i w1 = hash i w2)).card ≤ M := by
          intro w1 w2
          by_cases hne : w1 = w2
          · subst hne; simp
          · calc ((Finset.univ : Finset (Fin a)).filter (fun i => w1 ≠ w2 ∧ hash i w1 = hash i w2)).card
                ≤ ((Finset.univ : Finset (Fin a)).filter (fun i => hash i w1 = hash i w2)).card :=
                  Finset.card_le_card (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2.2⟩)
              _ ≤ M := hhash w1 w2 hne
        have h12 := Finset.card_union_le
          ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ u ∧ hash i e.1 = hash i u))
          ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ v ∧ hash i e.1 = hash i v))
        have h123 := Finset.card_union_le
          (((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ u ∧ hash i e.1 = hash i u)) ∪
           ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ v ∧ hash i e.1 = hash i v)))
          ((Finset.univ : Finset (Fin a)).filter (fun i => e.2 ≠ u ∧ hash i e.2 = hash i u))
        have h1234 := Finset.card_union_le
          (((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ u ∧ hash i e.1 = hash i u)) ∪
           ((Finset.univ : Finset (Fin a)).filter (fun i => e.1 ≠ v ∧ hash i e.1 = hash i v)) ∪
           ((Finset.univ : Finset (Fin a)).filter (fun i => e.2 ≠ u ∧ hash i e.2 = hash i u)))
          ((Finset.univ : Finset (Fin a)).filter (fun i => e.2 ≠ v ∧ hash i e.2 = hash i v))
        have ha1 := hf e.1 u
        have ha2 := hf e.1 v
        have ha3 := hf e.2 u
        have ha4 := hf e.2 v
        linarith
    calc badSet.card
        ≤ (B0 ∪ (Finset.univ : Finset (Fin k)).biUnion Bl).card := Finset.card_le_card hsub
      _ ≤ B0.card + ((Finset.univ : Finset (Fin k)).biUnion Bl).card := Finset.card_union_le _ _
      _ ≤ B0.card + ∑ l : Fin k, (Bl l).card := Nat.add_le_add_left Finset.card_biUnion_le _
      _ ≤ M + ∑ _l : Fin k, 4 * M := Nat.add_le_add hB0 (Finset.sum_le_sum (fun l _ => hBl l))
      _ = (1 + 4 * k) * M := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  have hbad_s : s * (2 * badSet.card) ≤ a := by
    have hqM : q * M = 2 * a := by dsimp [a, M]; ring
    have h1 : 4 * s * (1 + 4 * k) ≤ q := by dsimp [q]; nlinarith
    have h2 : 4 * s * badSet.card ≤ 2 * a := by
      calc 4 * s * badSet.card
          ≤ 4 * s * ((1 + 4 * k) * M) := Nat.mul_le_mul_left _ hbad_card
        _ = (4 * s * (1 + 4 * k)) * M := by ring
        _ ≤ q * M := Nat.mul_le_mul_right M h1
        _ = 2 * a := hqM
    have h2' : 2 * (s * (2 * badSet.card)) ≤ 2 * a := by
      have : 2 * (s * (2 * badSet.card)) = 4 * s * badSet.card := by ring
      rw [this]
      exact h2
    omega
  let term : ℕ → Fin a → ℕ := fun m0 i =>
    (Finset.univ : Finset Local).inf' Finset.univ_nonempty (fun P =>
      if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
        mult P (hash i u) (hash i v) = m0 then
        (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
      else b)
  let errI : Fin a → ℕ := fun i =>
    (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc (proj i) j))).card
  let lostI : Fin a → ℕ := fun i =>
    (Finset.univ.filter (fun j => y i j = none)).card
  have hpoint : ∀ i : Fin a,
      term truth i + D ≤ term m.val i + 2 * errI i + lostI i + if i ∈ badSet then 2 * b else 0 := by
    intro i
    by_cases hgi : good i
    · have hnb : i ∉ badSet := by simp [badSet, hgi]
      rw [if_neg hnb, add_zero]
      have hclean_proj : clean (proj i) (hash i u) (hash i v) := by
        intro l
        cases hGl : G l with
        | none => simp [proj, hGl]
        | some e =>
          simp only [proj, hGl, Option.map_some, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
          constructor
          · intro h1 h2
            have he1 : e.1 = u := by
              by_contra hne; exact (hgi.2 l e hGl).1 hne h1
            have he2 : e.2 = u := by
              by_contra hne; exact (hgi.2 l e hGl).2.2.1 hne h2
            have heq : e = (u, u) := Prod.ext he1 he2
            exact hGloop l u (by rw [hGl, heq])
          · intro h1 h2
            have he1 : e.1 = v := by
              by_contra hne; exact (hgi.2 l e hGl).2.1 hne h1
            have he2 : e.2 = v := by
              by_contra hne; exact (hgi.2 l e hGl).2.2.2 hne h2
            have heq : e = (v, v) := Prod.ext he1 he2
            exact hGloop l v (by rw [hGl, heq])
      have hmult_proj : mult (proj i) (hash i u) (hash i v) = truth := by
        dsimp [mult, truth]
        congr 1
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, proj]
        cases hGl : G l with
        | none => simp
        | some e =>
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · left
              have he1 : e.1 = u := by by_contra hne; exact (hgi.2 l e hGl).1 hne h1
              have he2 : e.2 = v := by by_contra hne; exact (hgi.2 l e hGl).2.2.2 hne h2
              exact Prod.ext he1 he2
            · right
              have he1 : e.1 = v := by by_contra hne; exact (hgi.2 l e hGl).2.1 hne h1
              have he2 : e.2 = u := by by_contra hne; exact (hgi.2 l e hGl).2.2.1 hne h2
              exact Prod.ext he1 he2
          · rintro (rfl | rfl)
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
      have hti : term truth i ≤ errI i := by
        have hle := Finset.inf'_le (f := fun P =>
          if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
            mult P (hash i u) (hash i v) = truth then
            (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
          else b) (Finset.mem_univ (proj i))
        rw [if_pos ⟨hgi.1, hclean_proj, hmult_proj⟩] at hle
        exact hle
      have hfi : D ≤ term m.val i + errI i + lostI i := by
        have hle_all : ∀ P ∈ (Finset.univ : Finset Local),
            D ≤ (if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
                mult P (hash i u) (hash i v) = m.val then
              (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
            else b) + errI i + lostI i := by
          intro P _
          by_cases hcond : hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
              mult P (hash i u) (hash i v) = m.val
          · rw [if_pos hcond]
            have hDle : D ≤ (Finset.univ.filter (fun j => enc (proj i) j ≠ enc P j)).card :=
              hdist (proj i) P (hash i u) (hash i v) hgi.1 hclean_proj hcond.2.1
                (by rw [hmult_proj, hcond.2.2]; exact hm.symm)
            have hsub : (Finset.univ.filter (fun j => enc (proj i) j ≠ enc P j)) ⊆
                (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))) ∪
                ((Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc (proj i) j))) ∪
                 (Finset.univ.filter (fun j => y i j = none))) := by
              intro j hj
              have hne : enc (proj i) j ≠ enc P j := (Finset.mem_filter.mp hj).2
              rw [Finset.mem_union, Finset.mem_union]
              cases hy : y i j with
              | none => exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hy⟩))
              | some val =>
                by_cases hv : val = enc (proj i) j
                · left
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simp [hy], ?_⟩
                  intro heq
                  rw [hy, Option.some.injEq] at heq
                  exact hne (hv.symm.trans heq)
                · right; left
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ j, by simp [hy], ?_⟩
                  intro heq
                  rw [hy, Option.some.injEq] at heq
                  exact hv heq
            have hc1 := Finset.card_le_card hsub
            have hc2 := Finset.card_union_le
              (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j)))
              ((Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc (proj i) j))) ∪
               (Finset.univ.filter (fun j => y i j = none)))
            have hc3 := Finset.card_union_le
              (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc (proj i) j)))
              (Finset.univ.filter (fun j => y i j = none))
            dsimp only [errI, lostI]
            omega
          · rw [if_neg hcond]
            omega
        obtain ⟨P0, hP0_mem, hP0_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
          (fun P : Local =>
            if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
              mult P (hash i u) (hash i v) = m.val then
              (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
            else b)
        have hP0 := hle_all P0 hP0_mem
        change D ≤ (Finset.univ : Finset Local).inf' Finset.univ_nonempty _ + errI i + lostI i
        rw [hP0_eq]
        exact hP0
      omega
    · have hb_mem : i ∈ badSet := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgi⟩
      rw [if_pos hb_mem]
      have hti : term truth i ≤ b := by
        have hle := Finset.inf'_le (f := fun P =>
          if hash i u ≠ hash i v ∧ clean P (hash i u) (hash i v) ∧
            mult P (hash i u) (hash i v) = truth then
            (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc P j))).card
          else b) (Finset.mem_univ (proj i))
        refine hle.trans ?_
        split_ifs
        · calc (Finset.univ.filter (fun j => y i j ≠ none ∧ y i j ≠ some (enc (proj i) j))).card
              ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_filter_le _ _
            _ = b := Fintype.card_fin b
        · exact le_refl b
      omega
  have hsum_all := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin a))) (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← Finset.mul_sum, ← Finset.sum_filter] at hsum_all
  have hfilt_bad : (Finset.univ : Finset (Fin a)).filter (fun i => i ∈ badSet) = badSet := by
    ext i; simp
  rw [hfilt_bad] at hsum_all
  have hmul_s := Nat.mul_le_mul_left s hsum_all
  have hbad_b : s * (badSet.card * (2 * b)) ≤ a * b := by
    have : s * (badSet.card * (2 * b)) = (s * (2 * badSet.card)) * b := by ring
    rw [this]
    exact Nat.mul_le_mul_right b hbad_s
  have hlt_s : s * score truth < s * score m.val := by
    change s * (∑ i : Fin a, term truth i) < s * (∑ i : Fin a, term m.val i)
    have herr_eq : (∑ i : Fin a, errI i) = err := rfl
    have hlost_eq : (∑ i : Fin a, lostI i) = lost := rfl
    rw [herr_eq, hlost_eq] at hmul_s
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left hlt_s
