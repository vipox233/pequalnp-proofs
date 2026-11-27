import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25878_aux

section Field
variable {F : Type*} [Field F] [CharP F 2]

theorem cube_collision {x y h : F} (hn : h ≠ 0)
    (same : (x+h)^3 + x^3 = (y+h)^3 + y^3) : x = y ∨ x = y + h := by
  have fact : h*(x+y)*(x+y+h) = ((x+h)^3+x^3) - ((y+h)^3+y^3) := by
    have two : (2 : F) = 0 := CharTwo.two_eq_zero
    have three : (3 : F) = 1 := by rw [show (3 : F) = 2+1 by norm_num,two,zero_add]
    ring_nf
    simp only [two,three,mul_zero,mul_one,CharTwo.sub_eq_add,add_zero,zero_add]
  rw [same,sub_self] at fact
  rcases mul_eq_zero.mp fact with hy | hy
  · have hxy := (mul_eq_zero.mp hy).resolve_left hn
    left
    calc
      x = x + (y + y) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = y := by rw [←add_assoc,hxy,zero_add]
  · right
    calc
      x = x + ((y+h) + (y+h)) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = y+h := by rw [←add_assoc,←add_assoc x y h,hy,zero_add]

theorem cube_fibre [DecidableEq F] (A : Finset F) (h b : F) (hn : h ≠ 0) :
    (A.filter (fun x => (x+h)^3+x^3=b)).card ≤ 2 := by
  classical
  by_cases H : (A.filter fun x => (x+h)^3+x^3=b).Nonempty
  · obtain ⟨y,hy⟩ := H
    have target : A.filter (fun x => (x+h)^3+x^3=b) ⊆ {y,y+h} := by
      intro x hx
      have test := cube_collision hn ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      simpa using test
    exact (Finset.card_le_card target).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp H]
    simp
end Field

def shift (n : ℕ) (u x : Fin (2^n)) : Fin (2^n) :=
  ⟨u.val ^^^ x.val,Nat.xor_lt_two_pow u.isLt x.isLt⟩

theorem shift_invol (n : ℕ) (u x : Fin (2^n)) : shift n u (shift n u x) = x := by
  apply Fin.ext
  change u.val ^^^ (u.val ^^^ x.val) = x.val
  rw [← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

def shiftEquiv (n : ℕ) (u : Fin (2^n)) : Fin (2^n) ≃ Fin (2^n) :=
  ⟨shift n u,shift n u,shift_invol n u,shift_invol n u⟩

theorem shifted_card (n : ℕ) (u : Fin (2^n)) (s : Finset (Fin (2^n))) :
    (s.map (shiftEquiv n u).toEmbedding).card = s.card := Finset.card_map _

theorem prefix_size {Q N : ℕ} (enc : Fin Q ↪ Fin N) {t : ℕ} (ht : t ≤ Q) :
    (((Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t)).image (fun i => (enc i).val)).card=t := by
  have hcard : ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t)).card=t := by
    let incl : Fin t ↪ Fin Q := Fin.castLEEmb ht
    have heq : (Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t) =
        (Finset.univ : Finset (Fin t)).map incl := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
      · rintro ⟨j,rfl⟩
        exact j.isLt
    simp [heq]
  exact (Finset.card_image_of_injective _ (show Function.Injective (fun i : Fin Q => (enc i).val) from Fin.val_injective.comp enc.injective)).trans hcard

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

def bitField (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitField_inj : Function.Injective bitField := by decide +kernel

theorem bitField_xor (x y : Bool) : bitField (xor x y) = bitField x + bitField y := by
  cases x <;> cases y <;> decide

def coords (m : ℕ) (u : Fin (2^m)) (i : Fin m) : ZMod 2 := bitField (u.val.testBit i.val)

theorem coords_inj (m : ℕ) : Function.Injective (coords m) := by
  intro x y eq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitField_inj (congrFun eq ⟨i,hi⟩)
  · have le : 2^m ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le le),Nat.testBit_lt_two_pow (y.isLt.trans_le le)]

noncomputable def wordIso (m : ℕ) : Fin (2^m) ≃ (Fin m → ZMod 2) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card (coords m)).mpr ⟨coords_inj m,by simp⟩)

section Field
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

noncomputable def fieldWord (B : Module.Basis (Fin m) (ZMod 2) F) : Fin (2^m) ≃ F :=
  (wordIso m).trans B.equivFun.toEquiv.symm

omit [CharP F 2] in
theorem fieldWord_xor (B : Module.Basis (Fin m) (ZMod 2) F) (x y : Fin (2^m)) :
    fieldWord B (shift m x y) = fieldWord B x + fieldWord B y := by
  apply B.equivFun.injective
  rw [map_add]
  change B.equivFun (B.equivFun.symm _) = B.equivFun (B.equivFun.symm _) + B.equivFun (B.equivFun.symm _)
  simp only [LinearEquiv.apply_symm_apply]
  funext i
  change bitField ((x.val ^^^ y.val).testBit i.val) = bitField (x.val.testBit i.val) + bitField (y.val.testBit i.val)
  rw [Nat.testBit_xor]
  exact bitField_xor _ _

noncomputable def cubeWord (B : Module.Basis (Fin m) (ZMod 2) F) (x : Fin (2^m)) : Fin (2^m) :=
  (fieldWord B).symm ((fieldWord B x)^3)

omit [CharP F 2] in
theorem word_zero (B : Module.Basis (Fin m) (ZMod 2) F) :
    fieldWord B ⟨0,by positivity⟩ = 0 := by
  apply B.equivFun.injective
  rw [map_zero]
  change B.equivFun (B.equivFun.symm _) = 0
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp [wordIso,coords,bitField]

theorem word_collisions (B : Module.Basis (Fin m) (ZMod 2) F)
    (h x y : Fin (2^m)) (hn : h.val ≠ 0)
    (same : shift m (cubeWord B (shift m x h)) (cubeWord B x) =
      shift m (cubeWord B (shift m y h)) (cubeWord B y)) :
    x = y ∨ x = shift m y h := by
  have shifted := congrArg (fieldWord B) same
  simp only [fieldWord_xor,cubeWord,Equiv.apply_symm_apply] at shifted
  have nonzero : fieldWord B h ≠ 0 := by
    intro z
    exact hn (congrArg Fin.val ((fieldWord B).injective (z.trans (word_zero B).symm)))
  rcases cube_collision nonzero shifted with e|e
  · exact Or.inl ((fieldWord B).injective e)
  · exact Or.inr ((fieldWord B).injective (e.trans (fieldWord_xor B y h).symm))

end Field
end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

def pack {m : ℕ} (lo hi : Fin (2^m)) : ℕ := lo.val+2^m*hi.val

theorem pack_low {m} (lo hi : Fin (2^m)) : pack lo hi % 2^m = lo.val := by
  simp [pack,Nat.mod_eq_of_lt lo.isLt]

theorem pack_high {m} (lo hi : Fin (2^m)) : pack lo hi / 2^m = hi.val := by
  unfold pack
  rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt lo.isLt,Nat.zero_add]

theorem pack_bound {k m : ℕ} (bound : 2*m ≤ k) (lo hi : Fin (2^m)) : pack lo hi < 2^k := by
  have next : lo.val+2^m*hi.val < 2^m*(hi.val+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have upper := Nat.mul_le_mul_left (2^m) hi.isLt
  have power : 2^m*2^m ≤ 2^k := by
    rw [←Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  exact next.trans_le (upper.trans power)

section Field
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

noncomputable def encoded (B : Module.Basis (Fin m) (ZMod 2) F) (x : Fin (2^m)) : ℕ :=
  pack x (cubeWord B x)

noncomputable def prefixEmbedding (B : Module.Basis (Fin m) (ZMod 2) F) (k : ℕ) (hk : 2*m ≤ k) :
    Fin (2^m) ↪ Fin (2^k) :=
  ⟨fun x => ⟨encoded B x,pack_bound hk _ _⟩,by
    intro x y eq
    apply Fin.ext
    have low := congrArg (fun z : Fin (2^k) => z.val % 2^m) eq
    dsimp [encoded] at low
    simpa only [pack_low] using low⟩

theorem shift_cancel {m} (u v : Fin (2^m)) : shift m u (shift m u v) = v := shift_invol m u v

theorem encoded_pair (B : Module.Basis (Fin m) (ZMod 2) F) (u v x y : Fin (2^m)) (neq : u ≠ v)
    (same : encoded B u ^^^ encoded B v = encoded B x ^^^ encoded B y) : u=x ∨ u=y := by
  have low := congrArg (fun z : ℕ => z % 2^m) same
  have high := congrArg (fun z : ℕ => z / 2^m) same
  simp only [encoded,Nat.xor_mod_two_pow,pack_low] at low
  simp only [encoded,Nat.xor_div_two_pow,pack_high] at high
  let h := shift m u v
  have hu : shift m u h = v := shift_cancel _ _
  have hx : shift m x h = y := by
    have e : h = shift m x y := Fin.ext low
    rw [e,shift_cancel]
  have nonzero : h.val ≠ 0 := by
    intro eq
    apply neq
    have valid := congrArg Fin.val hu
    change u.val ^^^ h.val = v.val at valid
    rw [eq,Nat.xor_zero] at valid
    exact Fin.ext valid
  apply (word_collisions B h u x nonzero ?_).imp_right (fun e => e.trans hx)
  rw [hu,hx]
  apply Fin.ext
  exact (Nat.xor_comm _ _).trans (high.trans (Nat.xor_comm _ _))

theorem pair_fibre [DecidableEq F] (B : Module.Basis (Fin m) (ZMod 2) F)
    (A : Finset (Fin (2^m))) (d : ℕ) (nonzero : d ≠ 0) :
    (A.filter fun x => ∃ y ∈ A, encoded B x ^^^ encoded B y = d).card ≤ 2 := by
  classical
  let S := A.filter fun x => ∃ y ∈ A, encoded B x ^^^ encoded B y = d
  change S.card ≤ 2
  by_cases H : S.Nonempty
  · obtain ⟨u,hu⟩ := H
    obtain ⟨v,_,hv⟩ := (Finset.mem_filter.mp hu).2
    have ne : u ≠ v := by
      rintro rfl
      exact nonzero (hv.symm.trans (Nat.xor_self _))
    apply (Finset.card_le_card (t := {u,v}) ?_).trans Finset.card_le_two
    intro x hx
    obtain ⟨y,_,hy⟩ := (Finset.mem_filter.mp hx).2
    have nx : x ≠ y := by
      rintro rfl
      exact nonzero (hy.symm.trans (Nat.xor_self _))
    simpa using encoded_pair B x y u v nx (hy.trans hv.symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp H]
    simp

end Field

theorem binary_power_basis (m : ℕ) (hm : m ≠ 0) :
    ∃ (B : Module.Basis (Fin m) (ZMod 2) (GaloisField 2 m)) (g : GaloisField 2 m),
      ∀ i : Fin m, B i = g ^ i.val := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod 2) (GaloisField 2 m)
  have eq : pb.dim = m := pb.finrank.symm.trans (GaloisField.finrank 2 hm)
  refine ⟨pb.basis.reindex (finCongr eq),pb.gen,?_⟩
  intro i
  simp [Module.Basis.reindex_apply,pb.basis_eq_pow]
end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

section Hamming
variable {α : Type*} [Fintype α] [DecidableEq α]

def countValue (p : α → Bool) (v : Bool) : ℕ := (Finset.univ.filter fun x => p x = v).card

theorem perturb (p e : α → Bool) (v : Bool) :
    countValue p v ≤ countValue (fun x => xor (p x) (e x)) v + countValue e true := by
  let A := Finset.univ.filter fun x => p x = v
  let B := Finset.univ.filter fun x => xor (p x) (e x) = v
  let E := Finset.univ.filter fun x => e x = true
  have inc : A ⊆ B ∪ E := by
    intro x hx
    obtain ⟨_,hv⟩ := Finset.mem_filter.mp hx
    cases he : e x with
    | false => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [he] using hv⟩)
    | true => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  exact (Finset.card_le_card inc).trans (Finset.card_union_le B E)

theorem balanced_perturb (p e : α → Bool) (d : ℕ)
    (hp : ∀ v, d+countValue e true ≤ countValue p v) :
    ∀ v, d ≤ countValue (fun x => xor (p x) (e x)) v := by
  intro v
  have h := perturb p e v
  have b := hp v
  omega

def marksDiff (A B : Finset α) (x : α) : Bool := xor (decide (x∈A)) (decide (x∈B))

theorem diff_count (A B : Finset α) :
    countValue (marksDiff A B) true + 2*(A ∩ B).card = A.card+B.card := by
  have support : (Finset.univ.filter fun x => marksDiff A B x = true) = (A \ B) ∪ (B \ A) := by
    ext x
    by_cases a : x∈A <;> by_cases b : x∈B <;> simp [marksDiff,a,b]
  have disj : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  unfold countValue
  rw [support,Finset.card_union_of_disjoint disj]
  have one := Finset.card_sdiff_add_card_inter A B
  have two := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at two
  omega

omit [DecidableEq α] in
theorem count_complement (p : α → Bool) :
    countValue p false + countValue p true = Fintype.card α := by
  have eq := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (fun x => p x = false)
  simpa [countValue] using eq

theorem constant_perturb (A B : Finset α) (t c : ℕ) (hA : A.card=t) (hB : B.card=t)
    (hi : (A ∩ B).card≤c) (big : 4*t ≤ Fintype.card α) :
    ∀ v, 2*(t-c) ≤ countValue (marksDiff A B) v := by
  have d := diff_count A B
  have total := count_complement (marksDiff A B)
  intro v
  cases v <;> omega

theorem common_gauge (a b u v w : Bool) :
    decide (xor a (xor u w) ≠ xor b (xor v w)) = xor (xor a b) (xor u v) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases w <;> decide

end Hamming
end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

theorem xor_cross {a b c d : ℕ} (eq : a ^^^ b = c ^^^ d) : b ^^^ d = a ^^^ c := by
  calc
    b ^^^ d = (a ^^^ (a ^^^ b)) ^^^ d := by rw [←Nat.xor_assoc a a,Nat.xor_self,Nat.zero_xor]
    _ = (a ^^^ (c ^^^ d)) ^^^ d := by rw [eq]
    _ = a ^^^ c := by rw [Nat.xor_assoc,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem xor_nonzero {a b : ℕ} (hne : a ≠ b) : a ^^^ b ≠ 0 := by
  intro eq
  apply hne
  calc
    a = a ^^^ (a ^^^ b) := by rw [eq,Nat.xor_zero]
    _ = b := by rw [←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

variable {k Q : ℕ}

def translated (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x : Fin (2^k)) :
    Finset (Fin (2^k)) := A.image fun u => shift k x (enc u)

theorem translated_card (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x : Fin (2^k)) :
    (translated enc A x).card = A.card :=
  Finset.card_image_of_injective _ ((shiftEquiv k x).injective.comp enc.injective)

theorem translated_member (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x z : Fin (2^k)) :
    z ∈ translated enc A x ↔ x.val ^^^ z.val ∈ A.image (fun u => (enc u).val) := by
  constructor
  · rintro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨u,hu,?_⟩
    exact (congrArg Fin.val (shift_invol k x (enc u))).symm
  · intro hz
    obtain ⟨u,hu,hv⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨u,hu,?_⟩
    have eq : enc u = shift k x z := Fin.ext hv
    rw [eq,shift_invol]

theorem overlap_image (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x y : Fin (2^k)) :
    translated enc A x ∩ translated enc A y ⊆
      (A.filter (fun u => ∃ v ∈ A, (enc u).val ^^^ (enc v).val = x.val ^^^ y.val)).image
        (fun u => shift k x (enc u)) := by
  intro z hz
  obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hz
  obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,v,hv,?_⟩,eq⟩
  exact xor_cross (congrArg Fin.val (eq.trans ev.symm))

theorem overlap_at_most (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x y : Fin (2^k)) (c : ℕ)
    (bound : (A.filter (fun u => ∃ v ∈ A, (enc u).val ^^^ (enc v).val = x.val ^^^ y.val)).card ≤ c) :
    (translated enc A x ∩ translated enc A y).card ≤ c :=
  (Finset.card_le_card (overlap_image enc A x y)).trans (Finset.card_image_le.trans bound)

theorem address_room (a k : ℕ) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) :
    4*2^(k/2) ≤ 2^(k-a) := by
  have grow : ∀ j : ℕ, 2 ≤ j → j+2 ≤ 2^j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj
      by_cases low : 2 ≤ j
      · have old := ih low
        rw [pow_succ]
        omega
      · have eq : j=1 := by omega
        subst j
        decide
  have enough := grow a ha
  have step : 2 + k/2 ≤ k-a := by omega
  calc
    4*2^(k/2) = 2^(2+k/2) := by rw [pow_add]; norm_num
    _ ≤ 2^(k-a) := Nat.pow_le_pow_right (by decide) step

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

theorem perturb_selector {α : Type*} [Fintype α] [DecidableEq α] (p : α → Bool) (A B : Finset α)
    (t r : ℕ) (v : Bool) (sizeA : A.card=t) (sizeB : B.card=t) (overlap : (A ∩ B).card ≤ 2)
    (large : (∃ z, p z=v) → 4*t ≤ countValue p v)
    (small : t ≤ r → (A ∩ B).Nonempty → ∃ z, p z=v) :
    2*(if t ≤ r then t else t-2) ≤ countValue (fun z => xor (p z) (marksDiff A B z)) v := by
  have d := diff_count A B
  by_cases yes : ∃ z, p z=v
  · have many := large yes
    have loss := perturb p (marksDiff A B) v
    split <;> omega
  · have equal : countValue (fun z => xor (p z) (marksDiff A B z)) v = countValue (marksDiff A B) true := by
      unfold countValue
      congr 1
      ext z
      have no : p z ≠ v := fun e => yes ⟨_,e⟩
      cases v <;> cases hp : p z <;> cases hn : marksDiff A B z <;> simp_all
    rw [equal]
    split
    · rename_i ht
      have empty := Finset.not_nonempty_iff_eq_empty.mp (fun hit => yes (small ht hit))
      rw [empty,Finset.card_empty] at d
      omega
    · omega

theorem residue_count {k a : ℕ} (ha : a ≤ k) (bit : ℕ → Bool) (v : Bool)
    (j : Fin (2^a)) (hv : bit j.val = v) :
    2^(k-a) ≤ countValue (fun z : Fin (2^k) => bit (z.val % 2^a)) v := by
  have pow : 2^a*2^(k-a)=2^k := by rw [←pow_add];congr 1;omega
  let incl : Fin (2^(k-a)) ↪ Fin (2^k) :=
    ⟨fun u => ⟨j.val+2^a*u.val,by
      rw [←pow]
      calc
        j.val+2^a*u.val < 2^a*(u.val+1) := by rw [Nat.mul_add,Nat.mul_one];omega
        _ ≤ 2^a*2^(k-a) := Nat.mul_le_mul_left _ u.isLt⟩,by
      intro u w eq
      have val := congrArg (fun z : Fin (2^k) => z.val / 2^a) eq
      dsimp only at val
      rw [Nat.add_mul_div_left _ _ (by positivity),Nat.add_mul_div_left _ _ (by positivity)] at val
      exact Fin.ext (Nat.add_left_cancel val)⟩
  have subset : (Finset.univ.map incl) ⊆ (Finset.univ.filter fun z : Fin (2^k) => bit (z.val % 2^a)=v) := by
    intro z hz
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change bit ((j.val+2^a*u.val) % 2^a) = v
    simpa [Nat.mod_eq_of_lt j.isLt] using hv
  simpa [countValue] using Finset.card_le_card subset

theorem two_bit_balance {k i j : ℕ} (hi : i < k) (neq : i ≠ j) (v : Bool) :
    2*countValue (fun z : Fin (2^k) => xor (z.val.testBit i) (z.val.testBit j)) v = 2^k := by
  let p := fun z : Fin (2^k) => xor (z.val.testBit i) (z.val.testBit j)
  let w : Fin (2^k) := ⟨2^i,Nat.pow_lt_pow_right (by decide) hi⟩
  have flip (z : Fin (2^k)) : p (shift k w z) = !(p z) := by
    change xor (((2^i) ^^^ z.val).testBit i) (((2^i) ^^^ z.val).testBit j) = !(p z)
    simp only [Nat.testBit_xor,Nat.testBit_two_pow_self,Nat.testBit_two_pow_of_ne neq]
    unfold p
    cases z.val.testBit i <;> cases z.val.testBit j <;> decide
  have eq : countValue p false = countValue p true := by
    apply Finset.card_equiv (shiftEquiv k w)
    intro z
    change z ∈ Finset.univ.filter (fun z => p z=false) ↔ shift k w z ∈ Finset.univ.filter (fun z => p z=true)
    simp [flip]
  have total := count_complement p
  rw [Fintype.card_fin] at total
  change 2*countValue p v=2^k
  cases v <;> omega

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

def firstWords (m t : ℕ) := (Finset.univ : Finset (Fin (2^m))).filter fun u => u.val < t

theorem small_collision {k a m t : ℕ} (enc : Fin (2^m) ↪ Fin (2^k)) (low : ∀ u, (enc u).val % 2^m = u.val)
    (x y : Fin (2^k)) (ne : x ≠ y) (ht : t ≤ 2^a)
    (hit : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).Nonempty) :
    0 < (x.val ^^^ y.val) % 2^m ∧ (x.val ^^^ y.val) % 2^m < 2^a := by
  obtain ⟨z,hz⟩ := hit
  obtain ⟨u,hu,_⟩ := Finset.mem_image.mp (overlap_image enc (firstWords m t) x y hz)
  obtain ⟨inA,v,inB,ds⟩ := Finset.mem_filter.mp hu
  have ux := (Finset.mem_filter.mp inA).2
  have vx := (Finset.mem_filter.mp inB).2
  have diff : (x.val ^^^ y.val) % 2^m=u.val ^^^ v.val := by rw [←ds,Nat.xor_mod_two_pow,low,low]
  have unequal : u.val ≠ v.val := by
    intro eq
    have same : u = v := Fin.ext eq
    rw [same,Nat.xor_self] at ds
    exact xor_nonzero (fun ev => ne (Fin.ext ev)) ds.symm
  rw [diff]
  exact ⟨Nat.pos_of_ne_zero (xor_nonzero unequal),Nat.xor_lt_two_pow (ux.trans_le ht) (vx.trans_le ht)⟩

theorem small_diff_residue {d a m : ℕ} (ha : a ≤ m) (hp : 0 < d % 2^m) (width : d % 2^m < 2^a) :
    d % 2^a ≠ 0 := by
  have smaller : d % 2^a = d % 2^m := by
    rw [← Nat.mod_mod_of_dvd d (pow_dvd_pow 2 ha),Nat.mod_eq_of_lt width]
  omega

theorem small_diff_bit {d a m : ℕ} (ha : a < m) (ha' : a < 2^a)
    (hp : 0 < d % 2^m) (width : d % 2^m < 2^a) (v : Bool) :
    ∃ j : Fin (2^a), d.testBit j.val = v := by
  have bit (j : ℕ) (hj : j < m) : (d % 2^m).testBit j = d.testBit j := by
    simp [Nat.testBit_mod_two_pow,hj]
  cases v with
  | false => exact ⟨⟨a,ha'⟩,(bit a ha).symm.trans (Nat.testBit_lt_two_pow width)⟩
  | true =>
    by_contra no
    have zero : d % 2^m=0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < a
      · rw [bit j (hj.trans ha)]
        have neg : d.testBit j ≠ true := fun hh => no ⟨⟨j,hj.trans ha'⟩,hh⟩
        simpa using Bool.eq_false_iff.mpr neg
      · have bigger : 2^a ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
        simp [Nat.testBit_lt_two_pow (width.trans_le bigger)]
    omega

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

def baseRow {k : ℕ} (a : ℕ) (x y z : Fin (2^k)) : Bool :=
  (x.val ^^^ y.val).testBit (z.val % 2^a)

def baseCol {k : ℕ} (a : ℕ) (x y z : Fin (2^k)) : Bool :=
  xor (z.val.testBit (x.val % 2^a)) (z.val.testBit (y.val % 2^a))

theorem address_large {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m) :
    4*t ≤ 2^(k-a) ∧ 8*t ≤ 2^k := by
  have hr := address_room a k ha hk
  rw [← hm] at hr
  have low : a < 2^a := Nat.lt_two_pow_self
  have eq : 2^(k-a)*2^a=2^k := by rw [←pow_add];congr 1;omega
  have bound : 2 ≤ 2^a := by
    calc
      2 = 2^1 := by decide
      _ ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
  have doubleBound := Nat.mul_le_mul_left (2^(k-a)) bound
  rw [eq] at doubleBound
  omega

theorem noise_bounds {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m)
    (enc : Fin (2^m) ↪ Fin (2^k)) (hlow : ∀ u, (enc u).val % 2^m=u.val)
    (x y : Fin (2^k)) (ne : x≠y) (v : Bool)
    (lim : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).card ≤ 2) :
    let A := translated enc (firstWords m t) x
    let B := translated enc (firstWords m t) y
    2*(if t ≤ 2^a then t else t-2) ≤ countValue (fun z => xor (baseRow a x y z) (marksDiff A B z)) v ∧
    2*(if t ≤ 2^a then t else t-2) ≤ countValue (fun z => xor (baseCol a x y z) (marksDiff A B z)) v := by
  dsimp only
  have hpow : a < 2^a := Nat.lt_two_pow_self
  have am : a < m := by omega
  have ak : a ≤ k := by omega
  have rk : 2^a ≤ k := by omega
  obtain ⟨room,largeRoom⟩ := address_large hm ha hk ht
  have ca : (firstWords m t).card=t := by
    have sz := prefix_size (Function.Embedding.refl (Fin (2^m))) ht
    simpa [firstWords,Finset.card_image_of_injective _ Fin.val_injective] using sz
  have sizes (z : Fin (2^k)) : (translated enc (firstWords m t) z).card=t := (translated_card ..).trans ca
  have smallInfo := small_collision (a := a) (t := t) enc hlow x y ne
  have col_ne (hs : t ≤ 2^a) (hI : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).Nonempty) :
      x.val % 2^a ≠ y.val % 2^a := by
    obtain ⟨pos,st⟩ := smallInfo hs hI
    have nmod := small_diff_residue am.le pos st
    intro e
    rw [Nat.xor_mod_two_pow,e,Nat.xor_self] at nmod
    exact nmod rfl
  constructor
  · apply perturb_selector _ _ _ t (2^a) v (sizes _) (sizes _) lim
    · rintro ⟨z,hz⟩
      exact room.trans (residue_count ak (fun j => (x.val ^^^ y.val).testBit j) v
        ⟨z.val % 2^a,Nat.mod_lt _ (by positivity)⟩ hz)
    · intro hs hI
      obtain ⟨pos,st⟩ := smallInfo hs hI
      obtain ⟨j,hj⟩ := small_diff_bit am hpow pos st v
      refine ⟨⟨j.val,j.isLt.trans_le (Nat.pow_le_pow_right (by decide) ak)⟩,?_⟩
      simpa [baseRow,Nat.mod_eq_of_lt j.isLt] using hj
  · apply perturb_selector _ _ _ t (2^a) v (sizes _) (sizes _) lim
    · rintro ⟨z,hz⟩
      by_cases same : x.val % 2^a=y.val % 2^a
      · have vf : v=false := by simpa [baseCol,same] using hz.symm
        simp [baseCol,countValue,same,vf]
        omega
      · have small : x.val % 2^a < k := (Nat.mod_lt _ (by positivity)).trans_le rk
        have h := two_bit_balance small same v
        change 4*t ≤ countValue (fun z : Fin (2^k) => xor (z.val.testBit (x.val % 2^a)) (z.val.testBit (y.val % 2^a))) v
        omega
    · intro hs hI
      have diff := col_ne hs hI
      cases v with
      | false => exact ⟨⟨0,by positivity⟩,by simp [baseCol]⟩
      | true =>
        have ix : x.val % 2^a < k := (Nat.mod_lt _ (by positivity)).trans_le rk
        refine ⟨⟨2^(x.val % 2^a),Nat.pow_lt_pow_right (by decide) ix⟩,?_⟩
        simp [baseCol,Nat.testBit_two_pow_of_ne diff]

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux

def raw {k : ℕ} (a : ℕ) (D : Finset ℕ) (x y : Fin (2^k)) : Bool :=
  xor (x.val.testBit (y.val % 2^a)) (decide ((x.val ^^^ y.val) ∈ D))

def separated {k : ℕ} (a : ℕ) (D : Finset ℕ) (distance : ℕ) : Prop :=
  ∀ f g : Fin (2^k) → Bool,
    let T := fun x y : Fin (2^k) => xor (raw a D x y) (xor (f x) (g y))
    ∀ i j : Fin (2^k), i ≠ j →
      distance ≤ (Finset.univ.filter (fun z => T i z ≠ T j z)).card ∧
      distance ≤ (Finset.univ.filter (fun z => T z i ≠ T z j)).card

theorem bool_pair (a b c d u v w : Bool) :
    (xor (xor a b) (xor u w) ≠ xor (xor c d) (xor v w)) ↔
    xor (xor a c) (xor b d) = !(xor u v) := by decide +revert

theorem geometric_part {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m)
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] (B : Module.Basis (Fin m) (ZMod 2) F) :
    let enc := prefixEmbedding B k (by omega)
    let D := (firstWords m t).image fun u => (enc u).val
    D.card=t ∧ @separated k a D (2*(if t ≤ 2^a then t else t-2)) := by
  classical
  let enc := prefixEmbedding B k (show 2*m ≤ k by omega)
  let A := firstWords m t
  let D := A.image fun u => (enc u).val
  change D.card=t ∧ @separated k a D _
  refine ⟨prefix_size enc ht,?_⟩
  intro f g
  dsimp only
  intro x y ne
  have hlow (u) : (enc u).val % 2^m = u.val := pack_low _ _
  have lim : (translated enc A x ∩ translated enc A y).card ≤ 2 := by
    apply overlap_at_most
    exact pair_fibre B A (x.val ^^^ y.val) (xor_nonzero (fun e => ne (Fin.ext e)))
  have bounds := fun v => noise_bounds hm ha hk ht enc hlow x y ne v lim
  let R := translated enc A x
  let S := translated enc A y
  have mx (z) : (x.val ^^^ z.val ∈ D) ↔ z ∈ R := (translated_member enc A x z).symm
  have my (z) : (y.val ^^^ z.val ∈ D) ↔ z ∈ S := (translated_member enc A y z).symm
  constructor
  · apply (bounds (!(xor (f x) (f y)))).1.trans_eq
    unfold countValue
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold raw baseRow marksDiff
    simp only [Nat.testBit_xor,mx,my]
    exact (bool_pair _ _ _ _ _ _ _).symm
  · apply (bounds (!(xor (g x) (g y)))).2.trans_eq
    unfold countValue
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold raw baseCol marksDiff
    rw [Nat.xor_comm z.val x.val,Nat.xor_comm z.val y.val,Bool.xor_comm (f z) (g x),Bool.xor_comm (f z) (g y)]
    simp only [mx,my]
    exact (bool_pair _ _ _ _ _ _ _).symm

end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
open PEqualNP.CircuitLowerBounds

abbrev Sig (X : Type*) := X → Bool
def neg {X} (f : Sig X) : Sig X := fun x => !(f x)
def use {X} (C : List (Sig X)) (f : Sig X) : Prop := f ∈ C ∧ neg f ∈ C
def values {X} (C : List (Sig X)) (x : X) := C.map (fun f => f x)
def run (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) v
def good (g : Gate) : Prop := g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Segment {X} (C D : List (Sig X)) (cost : ℕ) : Prop :=
  (∀ f ∈ C, f ∈ D) ∧ ∃ gs : List Gate, gs.length ≤ cost ∧ (∀ g ∈ gs, good g) ∧
    ∀ x, run gs (values C x) = values D x

namespace Segment
variable {X : Type*} {C D E : List (Sig X)} {a b : ℕ}
theorem ident (C : List (Sig X)) : Segment C C 0 :=
  ⟨fun _ h=>h,[],by simp,by simp,fun _=>rfl⟩

theorem trans (left : Segment C D a) (right : Segment D E b) : Segment C E (a+b) := by
  obtain ⟨i,gs,n,ok,eval⟩ := left
  obtain ⟨j,ts,m,ok',eval'⟩ := right
  refine ⟨fun f hf=>j _ (i _ hf),gs++ts,by simpa using Nat.add_le_add n m,?_,?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (ok g) (ok' g)
  · intro x
    change (gs++ts).foldl _ _ = _
    rw [List.foldl_append]
    exact (congrArg (run ts) (eval x)).trans (eval' x)

theorem relax (h : Segment C D a) (le : a≤b) : Segment C D b := by
  obtain ⟨inc,gs,len,ok,eval⟩ := h
  exact ⟨inc,gs,len.trans le,ok,eval⟩

theorem keeps (h : Segment C D a) {f : Sig X} (hf : use C f) : use D f :=
  ⟨h.1 _ hf.1,h.1 _ hf.2⟩
end Segment

theorem use_neg {X} {C : List (Sig X)} {f} (hf : use C f) : use C (neg f) := by
  refine ⟨hf.2,?_⟩
  have eq : neg (neg f) = f := by funext x;simp [neg]
  rw [eq]
  exact hf.1

theorem wire {X} {C : List (Sig X)} {f : Sig X} (hf : f ∈ C) :
    ∃ i : ℕ, ∀ x : X, (values C x).getD i false = f x := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hf
  refine ⟨i.val,fun x => ?_⟩
  rw [←hi]
  simp [values,List.getD_eq_getElem?_getD,List.get_eq_getElem]

theorem append_gate {X} {C : List (Sig X)} (g : Gate) (hg : good g) (f : Sig X)
    (hf : ∀ x, g.op.eval (g.inputs.map fun i => (values C x).getD i false) = f x) :
    Segment C (C++[f]) 1 := by
  refine ⟨fun v hv => List.mem_append_left _ hv,[g],by simp,by simpa,?_⟩
  intro x
  change values C x ++ [g.op.eval _] = _
  rw [hf]
  simp [values]

theorem add_and {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 2 ∧ use D (fun x => f x && g x) := by
  let out : Sig X := fun x => f x && g x
  obtain ⟨i,hi⟩ := wire hf.1
  obtain ⟨j,hj⟩ := wire hg.1
  have s := append_gate (C:=C) ⟨.and,[i,j]⟩ (by simp [good]) out (by
    intro x
    change ((values C x).getD i false && ((values C x).getD j false && true)) = out x
    rw [hi,hj,Bool.and_true])
  obtain ⟨k,hk⟩ := wire (s.keeps hf).2
  obtain ⟨l,hl⟩ := wire (s.keeps hg).2
  have t := append_gate (C:=C++[out]) ⟨.or,[k,l]⟩ (by simp [good]) (neg out) (by
    intro x
    change ((values (C++[out]) x).getD k false || ((values (C++[out]) x).getD l false || false)) = neg out x
    rw [hk,hl,Bool.or_false]
    simp [out,neg,Bool.not_and])
  refine ⟨_,s.trans t,?_⟩
  change use ((C++[out])++[neg out]) out
  exact ⟨t.1 _ (by simp),by simp⟩

theorem add_or {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 2 ∧ use D (fun x => f x || g x) := by
  obtain ⟨D,s,h⟩ := add_and C (neg f) (neg g) (use_neg hf) (use_neg hg)
  refine ⟨D,s,?_⟩
  have eq : neg (fun x => neg f x && neg g x) = (fun x => f x || g x) := by
    funext x;simp [neg,Bool.not_and]
  exact eq ▸ use_neg h

theorem add_xor {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 6 ∧ use D (fun x => xor (f x) (g x)) := by
  obtain ⟨D,s,h⟩ := add_and C f (neg g) hf (use_neg hg)
  obtain ⟨E,t,q⟩ := add_and D (neg f) g (s.keeps (use_neg hf)) (s.keeps hg)
  obtain ⟨H,u,w⟩ := add_or E _ _ (t.keeps h) q
  refine ⟨H,(s.trans t).trans u,?_⟩
  have eq : (fun x => f x && neg g x || neg f x && g x) = (fun x => xor (f x) (g x)) := by
    funext x;unfold neg;cases f x <;> cases g x <;> rfl
  exact eq ▸ w

theorem add_constants {X} (C : List (Sig X)) :
    ∃ D, Segment C D 2 ∧ use D (fun _ => false) ∧ use D (fun _ => true) := by
  let f : Sig X := fun _ => false
  let t : Sig X := fun _ => true
  have s := append_gate (C:=C) ⟨.or,[]⟩ (by simp [good]) f (fun _=>rfl)
  have q := append_gate (C:=C++[f]) ⟨.and,[]⟩ (by simp [good]) t (fun _=>rfl)
  have hf : f ∈ (C++[f])++[t] := q.1 _ (by simp)
  have ht : t ∈ (C++[f])++[t] := by simp
  exact ⟨_,s.trans q,⟨hf,ht⟩,⟨ht,hf⟩⟩

end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
open PEqualNP.CircuitLowerBounds

variable {X I : Type*}
abbrev Includes (C D : List (Sig X)) := ∀ f ∈ C, f ∈ D

theorem lift_use {C D : List (Sig X)} (inc : Includes C D) {f} (haveF : use C f) : use D f :=
  ⟨inc _ haveF.1,inc _ haveF.2⟩

theorem gather_list (C : List (Sig X)) (items : List I) (out : I → Sig X) (n : ℕ)
    (step : ∀ i, ∀ D, Includes C D → ∃ E, Segment D E n ∧ use E (out i)) :
    ∃ D, Segment C D (items.length*n) ∧ ∀ i ∈ items, use D (out i) := by
  induction items with
  | nil => exact ⟨C,by simpa using Segment.ident C,by simp⟩
  | cons i is ih =>
    obtain ⟨D,s,olds⟩ := ih
    obtain ⟨E,t,one⟩ := step i D s.1
    refine ⟨E,(s.trans t).relax (by simp [Nat.add_mul]),?_⟩
    intro v h
    rcases List.mem_cons.mp h with rfl | rest
    · exact one
    · exact t.keeps (olds _ rest)

theorem gather [Fintype I] (C : List (Sig X)) (out : I → Sig X) (n : ℕ)
    (step : ∀ i, ∀ D, Includes C D → ∃ E, Segment D E n ∧ use E (out i)) :
    ∃ D, Segment C D (Fintype.card I*n) ∧ ∀ i, use D (out i) := by
  classical
  obtain ⟨D,s,all⟩ := gather_list C (Finset.univ : Finset I).toList out n step
  exact ⟨D,by simpa using s,fun i => all i (by simp)⟩

theorem fold_signals (C : List (Sig X)) (items : List (Sig X)) (op : Bool → Bool → Bool) (start : Bool) (n : ℕ)
    (base : use C (fun _=>start)) (known : ∀ f∈items, use C f)
    (step : ∀ (D : List (Sig X)) f g, use D f → use D g → ∃ E, Segment D E n ∧ use E (fun x=>op (f x) (g x))) :
    ∃ D, Segment C D (items.length*n) ∧ use D (fun x => (items.map fun f=> f x).foldr op start) := by
  induction items with
  | nil => exact ⟨C,by simpa using Segment.ident C,base⟩
  | cons f fs ih =>
    obtain ⟨D,s,h⟩ := ih (fun g hg => known _ (List.mem_cons_of_mem _ hg))
    obtain ⟨E,t,out⟩ := step D f _ (s.keeps (known _ (by simp))) h
    exact ⟨E,(s.trans t).relax (by simp [Nat.add_mul]),out⟩

def initial (n : ℕ) : List (Sig (Fin n → Bool)) :=
  List.ofFn (fun i : Fin n => fun x : Fin n → Bool => x i) ++
  List.ofFn (fun i : Fin n => fun x : Fin n → Bool => !(x i))

theorem input (n : ℕ) (i : Fin n) : use (initial n) (fun x=>x i) := by
  constructor <;> unfold initial
  · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem finish (n bound : ℕ) (f : Sig (Fin n → Bool)) (D : List (Sig (Fin n → Bool)))
    (s : Segment (initial n) D bound) (output : use D f) : PEqualNP.Represents.HasLitSize n f bound := by
  obtain ⟨_,gs,len,ok,eval⟩ := s
  obtain ⟨i,hi⟩ := wire output.1
  refine ⟨⟨gs,i⟩,ok,len,?_⟩
  intro x
  have start : values (initial n) x = List.ofFn x ++ List.ofFn (fun j => !(x j)) := by
    simp [initial,values,List.map_ofFn,Function.comp_def]
  change (run gs (List.ofFn x ++ List.ofFn (fun j => !(x j)))).getD i false = _
  rw [←start,eval]
  exact hi x

end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
variable {X I : Type*}

def nz (u : ZMod 2) := decide (u ≠ 0)

theorem nz_add (u v : ZMod 2) : nz (u+v) = xor (nz u) (nz v) := by decide +revert
theorem nz_mul (u v : ZMod 2) : nz (u*v) = (nz u && nz v) := by decide +revert
theorem nz_bitField (u : Bool) : nz (bitField u) = u := by cases u <;> decide
theorem bitField_nz (u : ZMod 2) : bitField (nz u) = u := by decide +revert

theorem sum_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → X → ZMod 2)
    (base : use C (fun _ => false)) (w : ∀ i, use C (fun x => nz (f i x))) :
    ∃ D, Segment C D (s.card*6) ∧ use D (fun x => nz (∑ i ∈ s, f i x)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa [nz] using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_xor D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.sum_insert hi,nz_add] using out

theorem all_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → Sig X)
    (base : use C (fun _=>true)) (w : ∀ i, use C (f i)) :
    ∃ D, Segment C D (s.card*2) ∧ use D (fun x => decide (∀ i∈s, f i x=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_and D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.forall_mem_insert] using out

theorem any_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → Sig X)
    (base : use C (fun _=>false)) (w : ∀ i, use C (f i)) :
    ∃ D, Segment C D (s.card*2) ∧ use D (fun x => decide (∃ i∈s, f i x=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_or D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.exists_mem_insert] using out

end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux

def degree {m : ℕ} (p : Fin m × Fin m) : Fin (3*m) := ⟨2*p.1.val+p.2.val,by have := p.1.isLt; have := p.2.isLt; omega⟩
def bucket {m : ℕ} (d : Fin (3*m)) : Finset (Fin m × Fin m) := Finset.univ.filter fun p => degree p = d
def term {m : ℕ} (u : Fin (2^m)) (p : Fin m × Fin m) : ZMod 2 :=
  bitField (u.val.testBit p.1.val && u.val.testBit p.2.val)
def coefficient {m : ℕ} (u : Fin (2^m)) (d : Fin (3*m)) : ZMod 2 := ∑ p ∈ bucket d, term u p

theorem bucket_card {m : ℕ} (d : Fin (3*m)) : (bucket d).card ≤ m := by
  apply (Finset.card_le_card_of_injOn Prod.fst (t := Finset.univ) (fun _ _ => Finset.mem_univ _) ?_).trans_eq (by simp)
  intro p hp q hq he
  have dp := congrArg Fin.val (Finset.mem_filter.mp hp).2
  have dq := congrArg Fin.val (Finset.mem_filter.mp hq).2
  change 2*p.1.val+p.2.val = d.val at dp
  change 2*q.1.val+q.2.val = d.val at dq
  exact Prod.ext he (Fin.ext (by rw [he] at dp; omega))

section
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}
theorem cube_expand (B : Module.Basis (Fin m) (ZMod 2) F) (g : F) (basis : ∀ i : Fin m, B i = g^i.val)
    (u : Fin (2^m)) : (fieldWord B u)^3 = ∑ d : Fin (3*m), coefficient u d • (g^d.val) := by
  classical
  let f : Fin m → F := fun i => if u.val.testBit i.val then g^i.val else 0
  have exp : fieldWord B u = ∑ i, f i := by
    change B.equivFun.symm (coords m u) = _
    rw [Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [basis]
    cases h : u.val.testBit i.val <;> simp [coords,bitField,h,f]
  have split (p : Fin m × Fin m) : f p.1 ^ 2 * f p.2 = term u p • (g^(degree p).val) := by
    have hp : g^(2*p.1.val+p.2.val) = (g^p.1.val)^2 * g^p.2.val := by
      rw [pow_add,Nat.mul_comm 2 p.1.val,pow_mul]
    cases h : u.val.testBit p.1.val <;> cases j : u.val.testBit p.2.val <;> simp [term,bitField,degree,f,h,j,hp]
  calc
    (fieldWord B u)^3 = (∑ i, f i)^2 * ∑ i, f i := by rw [exp,pow_succ]
    _ = ∑ i, ∑ j, f i^2 * f j := by
      rw [sum_pow_char]
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ p : Fin m × Fin m, term u p • g^(degree p).val := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split (i,j)
    _ = ∑ d : Fin (3*m), ∑ p ∈ bucket d, term u p • g^(degree p).val :=
      (Finset.sum_fiberwise Finset.univ degree (fun p => term u p • g^(degree p).val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [coefficient,Finset.sum_smul]
      exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]

theorem cube_coord (B : Module.Basis (Fin m) (ZMod 2) F) (g : F) (h : ∀ i : Fin m, B i = g^i.val)
    (u : Fin (2^m)) (j : Fin m) :
    bitField ((cubeWord B u).val.testBit j.val) = ∑ d : Fin (3*m), coefficient u d * (B.equivFun (g^d.val)) j := by
  have e : B.equivFun ((fieldWord B u)^3) = coords m (cubeWord B u) := by
    change B.equivFun _ = (wordIso m) ((wordIso m).symm (B.equivFun _))
    rw [Equiv.apply_symm_apply]
  change (coords m (cubeWord B u)) j = _
  rw [←e,cube_expand B g h,map_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul]; rfl
end
end PEqualNP.Outside.L_meta_25878_aux

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
variable {X F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

theorem cube_circuit (C : List (Sig X)) (u : X → Fin (2^m)) (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i = g^i.val) (zero : use C (fun _=>false))
    (bits : ∀ i : Fin m, use C (fun x => (u x).val.testBit i.val)) :
    ∃ D, Segment C D (38*m^2) ∧ ∀ j : Fin m, use D (fun x => (cubeWord B (u x)).val.testBit j.val) := by
  classical
  obtain ⟨D,s,pairs⟩ := gather (I:=Fin m × Fin m) C (fun p x => nz (term (u x) p)) 2 (by
    intro p D incl
    simpa only [term,nz_bitField] using add_and D _ _ (lift_use incl (bits p.1)) (lift_use incl (bits p.2)))
  obtain ⟨E,t,cs⟩ := gather (I:=Fin (3*m)) D (fun d x => nz (coefficient (u x) d)) (m*6) (by
    intro d E incl
    obtain ⟨H,v,out⟩ := sum_bits E (bucket d) (fun p x => term (u x) p) (lift_use incl (s.keeps zero))
      (fun p => lift_use incl (pairs p))
    exact ⟨H,v.relax (Nat.mul_le_mul_right 6 (bucket_card d)),out⟩)
  obtain ⟨H,v,outs⟩ := gather (I:=Fin m) E (fun j x => (cubeWord B (u x)).val.testBit j.val) (3*m*6) (by
    intro j H incl
    let f := fun (d : Fin (3*m)) (x : X) => coefficient (u x) d * (B.equivFun (g^d.val)) j
    have known (d : Fin (3*m)) : use H (fun x => nz (f d x)) := by
      cases eq : nz ((B.equivFun (g^d.val)) j) <;> simp only [f,nz_mul,eq,Bool.and_false,Bool.and_true]
      · exact lift_use incl (t.keeps (s.keeps zero))
      · exact lift_use incl (cs d)
    obtain ⟨R,q,out⟩ := sum_bits H Finset.univ f (lift_use incl (t.keeps (s.keeps zero))) known
    refine ⟨R,by simpa using q,?_⟩
    have eq : (fun x => nz (∑ d, f d x)) = (fun x => (cubeWord B (u x)).val.testBit j.val) := by
      funext x
      change nz (∑ d, coefficient (u x) d * (B.equivFun (g^d.val)) j) = _
      rw [←cube_coord B g basis,nz_bitField]
    exact eq ▸ out)
  refine ⟨H,((s.trans t).trans v).relax ?_,outs⟩
  simp only [Fintype.card_prod,Fintype.card_fin]
  nlinarith

end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
variable {X : Type*}

theorem low_succ (v i : ℕ) : v % 2^(i+1) = v % 2^i + (if v.testBit i then 2^i else 0) := by
  rw [pow_succ,Nat.mod_mul,Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (v / 2^i) (by decide : 0 < 2)
  by_cases e : v / 2^i % 2 = 1
  · simp [e]
  · have z : v / 2^i % 2 = 0 := by omega
    simp [z]

theorem compare_succ (v t i : ℕ) :
    decide (v % 2^(i+1) < t % 2^(i+1)) =
      if t.testBit i then (!(v.testBit i) || decide (v % 2^i<t % 2^i))
      else (!(v.testBit i) && decide (v % 2^i<t % 2^i)) := by
  rw [low_succ,low_succ]
  have hv := Nat.mod_lt v (show 0<2^i by positivity)
  have ht := Nat.mod_lt t (show 0<2^i by positivity)
  cases e : v.testBit i <;> cases h : t.testBit i <;> simp <;> omega

theorem comparator (C : List (Sig X)) (v : X → ℕ) (t m : ℕ)
    (base : use C (fun _=>false)) (bits : ∀ i : Fin m, use C (fun x => (v x).testBit i.val)) :
    ∃ D, Segment C D (m*2) ∧ use D (fun x => decide ((v x) % 2^m<t % 2^m)) := by
  induction m with
  | zero => exact ⟨C,by simpa using Segment.ident C,by simpa [Nat.mod_one] using base⟩
  | succ m ih =>
    obtain ⟨D,s,old⟩ := ih (fun i => bits i.castSucc)
    have bit := use_neg (s.keeps (bits (Fin.last m)))
    cases h : t.testBit m with
    | false =>
      obtain ⟨E,q,out⟩ := add_and D _ _ bit old
      exact ⟨E,(s.trans q).relax (by omega),by simpa only [compare_succ,h,Bool.false_eq_true,ite_false,neg,Fin.val_last] using out⟩
    | true =>
      obtain ⟨E,q,out⟩ := add_or D _ _ bit old
      exact ⟨E,(s.trans q).relax (by omega),by simpa only [compare_succ,h,ite_true,neg,Fin.val_last] using out⟩

theorem word_eq {n : ℕ} (v w : Fin (2^n)) :
    (∀ i : Fin n, v.val.testBit i.val = w.val.testBit i.val) ↔ v = w := by
  constructor
  · intro h
    apply coords_inj n
    funext i
    simp only [coords,h i]
  · rintro rfl i
    rfl

theorem eq_wire (C : List (Sig X)) (n : ℕ) (v w : X → Fin (2^n)) (base : use C (fun _=>true))
    (bv : ∀ i : Fin n, use C (fun x => (v x).val.testBit i.val))
    (bw : ∀ i : Fin n, use C (fun x => (w x).val.testBit i.val)) :
    ∃ D, Segment C D (8*n) ∧ use D (fun x => decide (v x = w x)) := by
  classical
  let f := fun (i : Fin n) (x : X) => decide ((v x).val.testBit i.val = (w x).val.testBit i.val)
  obtain ⟨D,s,early⟩ := gather C f 6 (by
    intro i D inc
    obtain ⟨E,t,h⟩ := add_xor D _ _ (lift_use inc (bv i)) (lift_use inc (bw i))
    have e : neg (fun x => xor ((v x).val.testBit i.val) ((w x).val.testBit i.val)) = f i := by
      funext x
      dsimp only [f,neg]
      cases (v x).val.testBit i.val <;> cases (w x).val.testBit i.val <;> rfl
    exact ⟨E,t,e ▸ use_neg h⟩)
  obtain ⟨E,t,all⟩ := all_bits D Finset.univ f (s.keeps base) early
  refine ⟨E,(s.trans t).relax (by simp; omega),?_⟩
  simpa only [f,decide_eq_true_eq,Finset.mem_univ,true_implies,word_eq] using all
end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
variable {X : Type*}

def low (n : ℕ) (v : ℕ) : Fin (2^n) := ⟨v % 2^n,Nat.mod_lt _ (by positivity)⟩
theorem low_bit (n v : ℕ) (i : Fin n) : (low n v).val.testBit i.val = v.testBit i.val := by
  simp [low,Nat.testBit_mod_two_pow,i.isLt]

theorem const_bit {C : List (Sig X)} (z : use C (fun _=>false)) (o : use C (fun _=>true)) (b : Bool) :
    use C (fun _=>b) := by cases b <;> assumption

theorem selector (C : List (Sig X)) (k a : ℕ) (fits : 2^a ≤ k) (left right : X → Fin (2^k))
    (z : use C (fun _=>false)) (o : use C (fun _=>true))
    (l : ∀ i : Fin k, use C (fun x => (left x).val.testBit i.val))
    (r : ∀ i : Fin k, use C (fun x => (right x).val.testBit i.val)) :
    ∃ D, Segment C D ((2^a)*(8*a+2) + 2^a*2) ∧
      use D (fun x => (left x).val.testBit ((right x).val % 2^a)) := by
  classical
  let addr := fun x => low a (right x).val
  have small : a ≤ k := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans fits
  let hit := fun (j : Fin (2^a)) (x : X) => decide (addr x=j) && (left x).val.testBit j.val
  obtain ⟨D,s,known⟩ := gather C hit (8*a+2) (by
    intro j D inc
    have bit (i : Fin a) : use D (fun x => (addr x).val.testBit i.val) := by
      simpa only [addr,low_bit] using lift_use inc (r ⟨i.val,i.isLt.trans_le small⟩)
    obtain ⟨E,q,out⟩ := eq_wire D a addr (fun _=>j) (lift_use inc o) bit
      (fun i=>const_bit (lift_use inc z) (lift_use inc o) _)
    obtain ⟨H,t,both⟩ := add_and E _ _ out (q.keeps (lift_use inc (l ⟨j.val,j.isLt.trans_le fits⟩)))
    exact ⟨H,q.trans t,both⟩)
  obtain ⟨E,t,out⟩ := any_bits D Finset.univ hit (s.keeps z) known
  refine ⟨E,by simpa using s.trans t,?_⟩
  convert out using 1
  funext x
  symm
  cases hv : (left x).val.testBit ((right x).val % 2^a) with
  | true =>
    refine @decide_eq_true _ Finset.decidableExistsAndFinsetCoe ?_
    refine ⟨addr x,Finset.mem_univ _,?_⟩
    simp only [hit,decide_true,Bool.true_and]
    exact hv
  | false =>
    refine @decide_eq_false _ Finset.decidableExistsAndFinsetCoe ?_
    rintro ⟨i,_,hi⟩
    obtain ⟨eq,yes⟩ := Bool.and_eq_true_iff.mp hi
    have e : addr x = i := of_decide_eq_true eq
    subst i
    exact Bool.noConfusion (hv.symm.trans yes)
end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
open PEqualNP.MetaComplexity

theorem tableIndex_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem tableIndex_lt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [tableIndex_succ, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem testBit_tableIndex : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := tableIndex_lt (fun i : Fin n => x i.castSucc)
    rw [tableIndex_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def leftWord (k : ℕ) (x : Fin (k+k) → Bool) : Fin (2^k) :=
  Fin.ofNat _ (tableIndex fun i : Fin k => x (Fin.castAdd k i))
def rightWord (k : ℕ) (x : Fin (k+k) → Bool) : Fin (2^k) :=
  Fin.ofNat _ (tableIndex fun i : Fin k => x (Fin.natAdd k i))

theorem input_words (k : ℕ) :
    (∀ i : Fin k, use (initial (k+k)) (fun x => (leftWord k x).val.testBit i.val)) ∧
    (∀ i : Fin k, use (initial (k+k)) (fun x => (rightWord k x).val.testBit i.val)) := by
  constructor
  · intro i
    simpa only [leftWord,Fin.val_ofNat,Nat.mod_eq_of_lt (tableIndex_lt _),testBit_tableIndex] using input (k+k) (Fin.castAdd k i)
  · intro i
    simpa only [rightWord,Fin.val_ofNat,Nat.mod_eq_of_lt (tableIndex_lt _),testBit_tableIndex] using input (k+k) (Fin.natAdd k i)
end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
variable {X F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m k : ℕ}

omit [CharP F 2] in
theorem member_prefix (B : Module.Basis (Fin m) (ZMod 2) F) (hk : 2*m ≤ k) (t : ℕ) (z : Fin (2^k)) :
    z.val ∈ (firstWords m t).image (fun i => ((prefixEmbedding B k hk) i).val) ↔
      (low m z.val).val < t ∧ z = (prefixEmbedding B k hk) (low m z.val) := by
  constructor
  · intro mem
    obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp mem
    have e : low m z.val = u := Fin.ext (by
      change z.val % 2^m = u.val
      rw [←eq]
      exact pack_low _ _)
    rw [e]
    exact ⟨(Finset.mem_filter.mp hu).2,Fin.ext eq.symm⟩
  · rintro ⟨lt,eq⟩
    exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩,congrArg Fin.val eq.symm⟩

theorem mark_circuit (C : List (Sig X)) (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i = g^i.val) (hk : 2*m ≤ k) (t : ℕ) (ht : t ≤ 2^m)
    (v : X → Fin (2^k)) (z : use C (fun _=>false)) (o : use C (fun _=>true))
    (bits : ∀ i : Fin k, use C (fun x => (v x).val.testBit i.val)) :
    ∃ D, Segment C D (38*m^2+8*k+m*2+2) ∧ use D (fun x =>
      decide ((v x).val ∈ (firstWords m t).image (fun i=>((prefixEmbedding B k hk) i).val))) := by
  classical
  let u := fun x => low m (v x).val
  let w := fun x => (prefixEmbedding B k hk) (u x)
  have lo (i : Fin m) : use C (fun x => (u x).val.testBit i.val) := by
    simpa only [u,low_bit] using bits ⟨i.val,by have := i.isLt; omega⟩
  obtain ⟨D,s,cube⟩ := cube_circuit C u B g basis z lo
  have packed (i : Fin k) : use D (fun x => (w x).val.testBit i.val) := by
    have e (x : X) : (w x).val.testBit i.val = if i.val < m then (u x).val.testBit i.val
        else (cubeWord B (u x)).val.testBit (i.val-m) := by
      change ((u x).val + 2^m * (cubeWord B (u x)).val).testBit i.val = _
      rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ (u x).isLt]
    simp only [e]
    by_cases hi : i.val < m
    · simp only [hi,ite_true]
      exact s.keeps (lo ⟨_,hi⟩)
    · simp only [hi,ite_false]
      by_cases hj : i.val-m < m
      · exact cube ⟨_,hj⟩
      · have ez (x : X) : (cubeWord B (u x)).val.testBit (i.val-m) = false :=
          Nat.testBit_lt_two_pow ((cubeWord B (u x)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
        simpa only [ez] using s.keeps z
  obtain ⟨E,q,matchWord⟩ := eq_wire D k v w (s.keeps o) (fun i=>s.keeps (bits i)) packed
  have cmp : ∃ H, Segment E H (m*2) ∧ use H (fun x => decide ((u x).val < t)) := by
    rcases ht.lt_or_eq with h|rfl
    · obtain ⟨H,p,lt⟩ := comparator E (fun x=>(v x).val) t m (q.keeps (s.keeps z))
        (fun i=>q.keeps (s.keeps (bits ⟨i.val,by have := i.isLt; omega⟩)))
      refine ⟨H,p,?_⟩
      convert lt using 1
      funext x
      apply Bool.eq_iff_iff.mpr
      simp [u,low,Nat.mod_eq_of_lt h]
      exact @decide_eq_true_iff _ _
    · exact ⟨E,(Segment.ident E).relax (Nat.zero_le _),by simpa only [(u _).isLt,decide_true] using q.keeps (s.keeps o)⟩
  obtain ⟨H,p,lt⟩ := cmp
  obtain ⟨R,n,out⟩ := add_and H _ _ lt (p.keeps matchWord)
  refine ⟨R,((s.trans q).trans p).trans n,?_⟩
  simpa only [member_prefix, Bool.decide_and, w,u] using out
end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux.Circuits
theorem represent {k a m : ℕ} (hk : 2*m ≤ k) (fits : 2^a ≤ k) {F : Type*}
    [Field F] [Algebra (ZMod 2) F] [CharP F 2] (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i=g^i.val) (t : ℕ) (ht : t ≤ 2^m) :
    let D := (firstWords m t).image fun u => ((prefixEmbedding B k hk) u).val
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k:=k) (l:=k) (raw a D)) (150*(k+1)^2) := by
  classical
  dsimp only
  let C := initial (k+k)
  let v := fun x => shift k (leftWord k x) (rightWord k x)
  obtain ⟨left,right⟩ := input_words k
  obtain ⟨D,s,z,o⟩ := add_constants C
  obtain ⟨E,q,bits⟩ := gather D (fun (i : Fin k) x => (v x).val.testBit i.val) 6 (by
    intro i E inc
    simpa only [v,shift,Nat.testBit_xor] using add_xor E _ _ (lift_use inc (s.keeps (left i))) (lift_use inc (s.keeps (right i))))
  obtain ⟨H,p,mark⟩ := mark_circuit E B g basis hk t ht v (q.keeps z) (q.keeps o) bits
  obtain ⟨R,h,sel⟩ := selector H k a fits (leftWord k) (rightWord k) (p.keeps (q.keeps z)) (p.keeps (q.keeps o))
    (fun i=>p.keeps (q.keeps (s.keeps (left i)))) (fun i=>p.keeps (q.keeps (s.keeps (right i))))
  obtain ⟨W,l,out⟩ := add_xor R _ _ sel (h.keeps mark)
  apply finish (k+k) _ _ W _ out
  apply ((((s.trans q).trans p).trans h).trans l).relax
  simp only [Fintype.card_fin]
  have hm : m ≤ k := by omega
  have ha : a ≤ k := (Nat.le_of_lt Nat.lt_two_pow_self).trans fits
  have mm := Nat.mul_le_mul hm hm
  have ar := Nat.mul_le_mul fits ha
  nlinarith

end PEqualNP.Outside.L_meta_25878_aux.Circuits

namespace PEqualNP.Outside.L_meta_25878_aux
theorem complete_proof (k a : ℕ) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) :
    ∃ enc : Fin (2^(k/2)) ↪ Fin (2^k), (∀ i, (enc i).val % 2^(k/2) = i.val) ∧
      ∀ t, t ≤ 2^(k/2) → let D := (firstWords (k/2) t).image fun i => (enc i).val
        D.card=t ∧ PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k:=k) (l:=k) (raw a D)) (150*(k+1)^2) ∧
        @separated k a D (2*(if t ≤ 2^a then t else t-2)) := by
  have pos : 0 < 2^a := by positivity
  obtain ⟨B,g,basis⟩ := binary_power_basis (k/2) (by omega)
  let enc := prefixEmbedding B k (show 2*(k/2) ≤ k by omega)
  refine ⟨enc,fun i => pack_low _ _,?_⟩
  intro t ht
  obtain ⟨card,dist⟩ := geometric_part rfl ha hk ht B
  exact ⟨card,Circuits.represent (by omega) (by omega) B g basis t ht,dist⟩
end PEqualNP.Outside.L_meta_25878_aux

theorem PEqualNP.Outside.L_meta_25878 : (∀ k a : ℕ, (2 ≤ a ∧ 2*2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  let target := fun (D : Finset ℕ) (x y : I) =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let separated := fun (D : Finset ℕ) (d : ℕ) =>
    ∀ f g : I → Bool,
      let T := fun x y : I => xor (target D x y) (xor (f x) (g y))
      ∀ i j : I, i ≠ j →
        d ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
        d ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card
  let Q := 2^(k/2)
  ∃ enc : Fin Q ↪ I,
    (∀ i : Fin Q, (enc i).val % Q = i.val) ∧
    ∀ t : ℕ, t ≤ Q →
      let D := ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val < t)).image (fun i => (enc i).val)
      D.card = t ∧
      PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) (target D))
        (150*(k+1)^2) ∧ separated D (2*(if t ≤ r then t else t-2))) := by
  intro k a h
  exact PEqualNP.Outside.L_meta_25878_aux.complete_proof k a h.1 h.2
