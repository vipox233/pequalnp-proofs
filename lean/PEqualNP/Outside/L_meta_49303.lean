import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49303

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def fullMask : Nat := 0xffffffffffffffff
abbrev Masked (mask w : Nat) : Prop := w &&& mask = w
def bsel {α : Type} (c : Bool) (t f : α) : α := Bool.rec f t c
theorem bsel_true {α : Type} (t f : α) : bsel true t f = t := rfl
theorem bsel_false {α : Type} (t f : α) : bsel false t f = f := rfl
theorem beq_false_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
theorem ne_of_beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e; subst e; rw [Nat.beq_refl] at h; exact Bool.noConfusion h
theorem masked_self (mask : Nat) : Masked mask mask := by
  unfold Masked; simp
theorem masked_land_right (mask w : Nat) : Masked mask (w &&& mask) := by
  unfold Masked; apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and]
theorem xor_cancel_left (mask v : Nat) : mask ^^^ (mask ^^^ v) = v := by
  apply Nat.eq_of_testBit_eq; intro i; simp
theorem masked_sub_and {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (w &&& mask) &&& cut = w &&& cut := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and] at es ⊢
  cases hc : cut.testBit i <;> simp_all
theorem masked_sub_xor {mask cut w : Nat} (sub : mask &&& cut = cut) :
    (mask ^^^ w) &&& cut = cut ^^^ (w &&& cut) := by
  apply Nat.eq_of_testBit_eq; intro i
  have es := congrArg (fun x => x.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at es ⊢
  cases hc : cut.testBit i <;> simp_all
def canon (mask w : Nat) : Nat :=
  let v := w &&& mask
  bsel (Nat.beq v 0 || Nat.beq v mask) 0
    (let iv := mask ^^^ v; bsel (Nat.blt v iv) v iv)
theorem canon_zero (mask : Nat) : canon mask 0 = 0 := by
  unfold canon; simp [bsel]
theorem canon_self (mask : Nat) : canon mask mask = 0 := by
  unfold canon; simp [bsel]
theorem canon_land (mask w : Nat) : canon mask (w &&& mask) = canon mask w := by
  unfold canon; dsimp only; rw [masked_land_right mask w]
theorem canon_cases (mask w : Nat) :
    (canon mask w = 0 ∧ (w &&& mask = 0 ∨ w &&& mask = mask)) ∨
    (canon mask w ≠ 0 ∧ (canon mask w = w &&& mask ∨ canon mask w = mask ^^^ (w &&& mask))) := by
  unfold canon; dsimp only
  set v := w &&& mask
  by_cases hv0 : v = 0
  · left; rw [hv0]; simp [bsel]
  · by_cases hvm : v = mask
    · left; rw [hvm]; simp [bsel]
    · right
      rw [beq_false_ne hv0, beq_false_ne hvm]
      simp only [Bool.or_false, bsel_false]
      cases hlt : Nat.blt v (mask ^^^ v)
      · rw [bsel_false]
        refine ⟨?_, Or.inr rfl⟩
        intro hz
        have e := congrArg (fun x => mask ^^^ x) hz
        rw [xor_cancel_left] at e
        exact hvm (by simpa using e)
      · rw [bsel_true]; exact ⟨hv0, Or.inl rfl⟩
theorem canon_xor_mask (mask w : Nat) : canon mask (mask ^^^ w) = canon mask w := by
  have hsub : (mask ^^^ w) &&& mask = mask ^^^ (w &&& mask) := masked_sub_xor (masked_self mask)
  unfold canon; dsimp only
  rw [hsub]
  generalize hv : w &&& mask = v
  set iv := mask ^^^ v
  have hiv : mask ^^^ iv = v := xor_cancel_left mask v
  rw [hiv]
  by_cases hv0 : v = 0
  · have hivm : iv = mask := by simp [iv, hv0]
    rw [hv0, hivm]; simp [bsel]
  · by_cases hvm : v = mask
    · have hiv0 : iv = 0 := by simp [iv, hvm]
      rw [hvm, hiv0]; simp [bsel]
    · have hiv0 : iv ≠ 0 := by
        intro h; apply hvm
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      have hivm : iv ≠ mask := by
        intro h; apply hv0
        have e := congrArg (fun x => mask ^^^ x) h
        rw [hiv] at e; simpa using e
      rw [beq_false_ne hv0, beq_false_ne hvm, beq_false_ne hiv0, beq_false_ne hivm]
      simp only [Bool.or_false, bsel_false]
      have hne : v ≠ iv := by
        intro h
        have hm0 : mask = 0 := by
          apply Nat.eq_of_testBit_eq; intro i
          have ei := congrArg (fun x => x.testBit i) h
          simp only [iv, Nat.testBit_xor] at ei
          cases hv' : v.testBit i <;> cases hm' : mask.testBit i <;> simp_all
        have : v = 0 := by rw [← hv, hm0]; simp
        exact hv0 this
      by_cases hlt : v < iv
      · have h1 : Nat.blt v iv = true := Nat.blt_eq.mpr hlt
        have h2 : Nat.blt iv v = false := by cases h : Nat.blt iv v; rfl; have := Nat.blt_eq.mp h; omega
        rw [h1, h2, bsel_true, bsel_false]
      · have hgt : iv < v := by omega
        have h1 : Nat.blt v iv = false := by cases h : Nat.blt v iv; rfl; have := Nat.blt_eq.mp h; omega
        have h2 : Nat.blt iv v = true := Nat.blt_eq.mpr hgt
        rw [h1, h2, bsel_false, bsel_true]
theorem canon_idem (mask w : Nat) : canon mask (canon mask w) = canon mask w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · rw [h0, canon_zero]
  · calc canon mask (canon mask w) = canon mask (w &&& mask) := by rw [h1]
      _ = canon mask w := canon_land mask w
  · calc canon mask (canon mask w) = canon mask (mask ^^^ (w &&& mask)) := by rw [h2]
      _ = canon mask (w &&& mask) := canon_xor_mask mask (w &&& mask)
      _ = canon mask w := canon_land mask w
theorem canon_submask {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w ≠ 0) :
    canon cut (canon mask w) = canon cut w := by
  rcases canon_cases mask w with ⟨h0, _⟩ | ⟨_, h1 | h2⟩
  · exact absurd h0 hc
  · rw [h1, ← canon_land cut (w &&& mask), masked_sub_and sub, canon_land]
  · rw [h2, ← canon_land cut (mask ^^^ (w &&& mask)), masked_sub_xor sub, masked_sub_and sub]
    rw [← masked_sub_xor (masked_self cut), canon_land, canon_xor_mask]
theorem canon_submask_zero {mask cut w : Nat} (sub : mask &&& cut = cut) (hc : canon mask w = 0) :
    canon cut w = 0 := by
  rcases canon_cases mask w with ⟨_, h0 | hm⟩ | ⟨hne, _⟩
  · rw [← canon_land cut w, ← masked_sub_and sub, h0]; simp [canon_zero]
  · rw [← canon_land cut w, ← masked_sub_and sub, hm, sub, canon_self]
  · exact absurd hc hne
theorem canon_testBit_eq {mask w p n : Nat} (hp : mask.testBit p = true) (hn : mask.testBit n = true) :
    ((canon mask w).testBit p = (canon mask w).testBit n) ↔ (w.testBit p = w.testBit n) := by
  rcases canon_cases mask w with ⟨h0, h1 | h2⟩ | ⟨_, h1 | h2⟩
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h1
    have e2 := congrArg (fun x => x.testBit n) h1
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h0]
    have e1 := congrArg (fun x => x.testBit p) h2
    have e2 := congrArg (fun x => x.testBit n) h2
    simp [Nat.testBit_and, hp, hn] at e1 e2 ⊢; simp [e1, e2]
  · rw [h1]; simp [Nat.testBit_and, hp, hn]
  · rw [h2]; simp [Nat.testBit_xor, Nat.testBit_and, hp, hn]
def binOp (mask op a b : Nat) : Nat :=
  bsel (Nat.beq op 0) (canon mask (a &&& b))
    (bsel (Nat.beq op 1) (canon mask (a ||| b))
      (bsel (Nat.beq op 2) (canon mask (a &&& (mask ^^^ b)))
        (canon mask ((mask ^^^ a) &&& b))))
theorem binOp_canon (mask op a b : Nat) : canon mask (binOp mask op a b) = binOp mask op a b := by
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false] <;> exact canon_idem mask _
theorem binOp_comm (mask op a b : Nat) (hop : op < 4) :
    ∃ op' < 4, binOp mask op a b = binOp mask op' b a := by
  have hland : a &&& b = b &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have hlor : a ||| b = b ||| a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or, Bool.or_comm]
  have h23 : a &&& (mask ^^^ b) = (mask ^^^ b) &&& a := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  have h32 : (mask ^^^ a) &&& b = b &&& (mask ^^^ a) := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  rcases (show op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨0, by omega, by change canon mask (a &&& b) = canon mask (b &&& a); rw [hland]⟩
  · exact ⟨1, by omega, by change canon mask (a ||| b) = canon mask (b ||| a); rw [hlor]⟩
  · exact ⟨3, by omega, by change canon mask (a &&& (mask ^^^ b)) = canon mask ((mask ^^^ b) &&& a); rw [h23]⟩
  · exact ⟨2, by omega, by change canon mask ((mask ^^^ a) &&& b) = canon mask (b &&& (mask ^^^ a)); rw [h32]⟩
theorem binOp_zero_left (mask op b : Nat) : binOp mask op 0 b = 0 ∨ binOp mask op 0 b = canon mask b := by
  unfold binOp
  have hmb : (mask ^^^ 0) &&& b = b &&& mask := by
    apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_and, Bool.and_comm]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · right; rw [hmb, canon_land]
  · left; simp [canon_zero]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_zero_right (mask op a : Nat) : binOp mask op a 0 = 0 ∨ binOp mask op a 0 = canon mask a := by
  unfold binOp
  have hma : a &&& (mask ^^^ 0) = a &&& mask := by simp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; simp [canon_zero]
  · right; rw [hma, canon_land]
  · right; simp
  · right; simp
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
  · left; simp [canon_zero]
theorem binOp_self (mask op a : Nat) : binOp mask op a a = 0 ∨ binOp mask op a a = canon mask a := by
  have h2 : canon mask (a &&& (mask ^^^ a)) = 0 := by
    rw [← canon_land]
    have : (a &&& (mask ^^^ a)) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  have h3 : canon mask ((mask ^^^ a) &&& a) = 0 := by
    rw [← canon_land]
    have : ((mask ^^^ a) &&& a) &&& mask = 0 := by
      apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
      cases a.testBit i <;> cases mask.testBit i <;> rfl
    rw [this, canon_zero]
  unfold binOp
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
  · left; exact h3
  · left; exact h2
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
  · right; simp
theorem deMorgan_or_mask {mask a b : Nat} (ha : Masked mask a) (hb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  unfold Masked at ha hb
  apply Nat.eq_of_testBit_eq; intro i
  have ea := congrArg (fun x => x.testBit i) ha
  have eb := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ea eb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
  cases hm : mask.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem canon_and_in_binOp (mask x y : Nat) :
    canon mask (x &&& y) = 0 ∨
    canon mask (x &&& y) = canon mask x ∨
    canon mask (x &&& y) = canon mask y ∨
    ∃ op < 4, canon mask (x &&& y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x &&& y) = canon mask ((x &&& mask) &&& (y &&& mask)) := by
    rw [← canon_land mask (x &&& y), ← canon_land mask ((x &&& mask) &&& (y &&& mask))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_and]
    cases x.testBit i <;> cases y.testBit i <;> cases mask.testBit i <;> rfl
  rw [hxy]
  have hvxm : Masked mask (x &&& mask) := masked_land_right mask x
  have hvym : Masked mask (y &&& mask) := masked_land_right mask y
  rcases canon_cases mask x with ⟨hx0, hx1 | hx2⟩ | ⟨_, hx1 | hx2⟩
  · left; rw [hx1]; simp [canon_zero]
  · right; right; left; rw [hx2]
    have : mask &&& (y &&& mask) = y &&& mask := by
      apply Nat.eq_of_testBit_eq; intro i
      have e := congrArg (fun t => t.testBit i) hvym
      simp only [Nat.testBit_and] at e ⊢; rw [Bool.and_comm]; exact e
    rw [this, canon_land]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨0, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& canon mask y)
      rw [hx1, hy1]
    · right; right; right; refine ⟨2, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x &&& (mask ^^^ canon mask y))
      rw [hx1, hy2, xor_cancel_left]
  · rcases canon_cases mask y with ⟨hy0, hy1 | hy2⟩ | ⟨_, hy1 | hy2⟩
    · left; rw [hy1]; simp [canon_zero]
    · right; left; rw [hy2, hvxm, canon_land]
    · right; right; right; refine ⟨3, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask ((mask ^^^ canon mask x) &&& canon mask y)
      rw [hx2, hy1, xor_cancel_left]
    · right; right; right; refine ⟨1, by omega, ?_⟩
      change canon mask ((x &&& mask) &&& (y &&& mask)) = canon mask (canon mask x ||| canon mask y)
      rw [hx2, hy2, ← deMorgan_or_mask hvxm hvym, canon_xor_mask]
theorem canon_or_in_binOp (mask x y : Nat) :
    canon mask (x ||| y) = 0 ∨
    canon mask (x ||| y) = canon mask x ∨
    canon mask (x ||| y) = canon mask y ∨
    ∃ op < 4, canon mask (x ||| y) = binOp mask op (canon mask x) (canon mask y) := by
  have hxy : canon mask (x ||| y) = canon mask ((mask ^^^ x) &&& (mask ^^^ y)) := by
    rw [← canon_xor_mask mask (x ||| y), ← canon_land mask (mask ^^^ (x ||| y))]
    rw [← canon_land mask ((mask ^^^ x) &&& (mask ^^^ y))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor]
    cases mask.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> rfl
  rw [hxy]
  have h := canon_and_in_binOp mask (mask ^^^ x) (mask ^^^ y)
  rwa [canon_xor_mask, canon_xor_mask] at h
theorem canon_sub_binOp {mask cut op a b : Nat} (sub : mask &&& cut = cut) :
    canon cut (binOp mask op a b) = 0 ∨
    canon cut (binOp mask op a b) = canon cut a ∨
    canon cut (binOp mask op a b) = canon cut b ∨
    ∃ op' < 4, canon cut (binOp mask op a b) = binOp cut op' (canon cut a) (canon cut b) := by
  have go (u : Nat) : canon cut (canon mask u) = canon cut u := by
    by_cases h : canon mask u = 0
    · rw [h, canon_zero, (canon_submask_zero sub h).symm]
    · exact canon_submask sub h
  have hmx1 : canon cut ((mask ^^^ a) &&& b) = canon cut ((cut ^^^ a) &&& b) := by
    rw [← canon_land cut ((mask ^^^ a) &&& b), ← canon_land cut ((cut ^^^ a) &&& b)]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hmx2 : canon cut (a &&& (mask ^^^ b)) = canon cut (a &&& (cut ^^^ b)) := by
    rw [← canon_land cut (a &&& (mask ^^^ b)), ← canon_land cut (a &&& (cut ^^^ b))]
    congr 1; apply Nat.eq_of_testBit_eq; intro i
    have es := congrArg (fun t => t.testBit i) sub
    simp only [Nat.testBit_and] at es
    simp only [Nat.testBit_and, Nat.testBit_xor]
    cases hc : cut.testBit i
    · simp
    · simp only [hc, Bool.and_true] at es ⊢; rw [es]
  have hsub_case1 : canon cut ((cut ^^^ a) &&& b) = 0 ∨ canon cut ((cut ^^^ a) &&& b) = canon cut a ∨
      canon cut ((cut ^^^ a) &&& b) = canon cut b ∨
      ∃ op' < 4, canon cut ((cut ^^^ a) &&& b) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut (cut ^^^ a) b
    rwa [canon_xor_mask] at h
  have hsub_case2 : canon cut (a &&& (cut ^^^ b)) = 0 ∨ canon cut (a &&& (cut ^^^ b)) = canon cut a ∨
      canon cut (a &&& (cut ^^^ b)) = canon cut b ∨
      ∃ op' < 4, canon cut (a &&& (cut ^^^ b)) = binOp cut op' (canon cut a) (canon cut b) := by
    have h := canon_and_in_binOp cut a (cut ^^^ b)
    rwa [canon_xor_mask] at h
  have hbin_eq : binOp mask op a b = canon mask (a &&& b) ∨ binOp mask op a b = canon mask (a ||| b) ∨
      binOp mask op a b = canon mask (a &&& (mask ^^^ b)) ∨ binOp mask op a b = canon mask ((mask ^^^ a) &&& b) := by
    unfold binOp
    cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp [bsel]
  rcases hbin_eq with h | h | h | h <;> rw [h, go]
  · exact canon_and_in_binOp cut a b
  · exact canon_or_in_binOp cut a b
  · rw [hmx2]; exact hsub_case2
  · rw [hmx1]; exact hsub_case1
def Avail (bank : List Nat) (w : Nat) : Prop := w = 0 ∨ w ∈ bank
def GateBin (mask : Nat) (bank : List Nat) (v : Nat) : Prop :=
  ∃ a b op, op < 4 ∧ Avail bank a ∧ Avail bank b ∧ v = binOp mask op a b
def BuildsBin (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | v :: vs => GateBin mask bank v ∧ BuildsBin mask (v :: bank) vs
def LowerBin (mask : Nat) (stock : List Nat) (goal m : Nat) : Prop :=
  ∀ vs, BuildsBin mask stock vs → Avail (vs ++ stock) goal → m ≤ vs.length
theorem avail_weaken {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {w : Nat} (h : Avail b1 w) :
    Avail b2 w := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (sub w h)
theorem gate_weaken {mask : Nat} {b1 b2 : List Nat} (sub : ∀ w ∈ b1, w ∈ b2) {v : Nat}
    (h : GateBin mask b1 v) : GateBin mask b2 v := by
  obtain ⟨a, b, op, hop, ha, hb, hv⟩ := h
  exact ⟨a, b, op, hop, avail_weaken sub ha, avail_weaken sub hb, hv⟩
theorem builds_weaken {mask : Nat} {b1 b2 vs : List Nat} (sub : ∀ w ∈ b1, w ∈ b2)
    (h : BuildsBin mask b1 vs) : BuildsBin mask b2 vs := by
  induction vs generalizing b1 b2 with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gate_weaken sub h.1, ih ?_ h.2⟩
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sub w hw)
theorem builds_append {mask : Nat} {roots first second : List Nat}
    (h1 : BuildsBin mask roots first) (h2 : BuildsBin mask (first ++ roots) second) :
    BuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact h2
  | cons v vs ih =>
    refine ⟨h1.1, ih h1.2 ?_⟩
    exact builds_weaken (fun w hw => by simp only [List.mem_append, List.mem_cons] at hw ⊢; tauto) h2
def dropIf (drop : Bool) (x : Nat) (S : Finset Nat) : Finset Nat :=
  if drop then S.erase x else S
theorem dropIf_subset (drop : Bool) (x : Nat) (S : Finset Nat) : dropIf drop x S ⊆ S := by
  unfold dropIf; split; exact Finset.erase_subset _ _; exact Finset.Subset.refl _
theorem dropIf_card_le (drop : Bool) (x : Nat) (S : Finset Nat) :
    S.card ≤ (dropIf drop x S).card + 1 := by
  unfold dropIf; split
  · by_cases hx : x ∈ S
    · have := Finset.card_erase_add_one hx; omega
    · rw [Finset.erase_eq_of_notMem hx]; omega
  · omega
inductive LiveBin (mask goal : Nat) : Nat → Finset Nat → Prop
  | done : LiveBin mask goal 0 {goal}
  | step {k : Nat} {S : Finset Nat} {a b op : Nat}
      (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hop : op < 4)
      (hz : binOp mask op a b ≠ 0) (hf : binOp mask op a b ∉ S)
      (keepA keepB : Bool) :
      LiveBin mask goal k (insert (binOp mask op a b) (dropIf (!keepA) a (dropIf (!keepB) b S))) →
      LiveBin mask goal (k + 1) S
theorem liveBin_zero_not_mem {mask goal k : Nat} {S : Finset Nat} (hg : goal ≠ 0)
    (h : LiveBin mask goal k S) : 0 ∉ S := by
  induction h with
  | done => simp [hg.symm]
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    intro h0; apply ih
    apply Finset.mem_insert_of_mem
    unfold dropIf
    split
    · apply Finset.mem_erase.mpr; refine ⟨ha0.symm, ?_⟩
      split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
    · split
      · exact Finset.mem_erase.mpr ⟨hb0.symm, h0⟩
      · exact h0
theorem liveBin_card_le {mask goal k : Nat} {S : Finset Nat} (h : LiveBin mask goal k S) :
    S.card ≤ k + 1 := by
  induction h with
  | done => simp
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    set z := binOp mask op a b
    have h1 := dropIf_card_le (!keepB) b S
    have h2 := dropIf_card_le (!keepA) a (dropIf (!keepB) b S)
    have hz' : z ∉ dropIf (!keepA) a (dropIf (!keepB) b S) := fun hm =>
      hf (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm))
    have h3 : (insert z (dropIf (!keepA) a (dropIf (!keepB) b S))).card =
        (dropIf (!keepA) a (dropIf (!keepB) b S)).card + 1 := Finset.card_insert_of_notMem hz'
    omega
theorem extractLiveBin_aux {mask goal : Nat} (hg : goal ≠ 0) :
    ∀ (vs bank : List Nat) (k : Nat) (L : Finset Nat),
      BuildsBin mask bank vs → (∀ w ∈ bank, canon mask w = w) →
      L ⊆ (vs ++ bank).toFinset → LiveBin mask goal k L →
      ∃ k' S, k' ≤ k + vs.length ∧ S ⊆ bank.toFinset ∧ LiveBin mask goal k' S
  | [], bank, k, L, _, _, hsub, hlive => ⟨k, L, by simp, hsub, hlive⟩
  | v :: vs, bank, k, L, hbuild, hcb, hsub, hlive => by
    have hcv : canon mask v = v := by
      obtain ⟨a, b, op, _, _, _, rfl⟩ := hbuild.1; exact binOp_canon mask op a b
    have hcb' : ∀ w ∈ v :: bank, canon mask w = w := by
      intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hcv; exact hcb w hw
    have hsub' : L ⊆ (vs ++ (v :: bank)).toFinset := by
      intro w hw
      have := hsub hw
      simp only [List.toFinset_append, List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at this ⊢
      tauto
    obtain ⟨k1, L1, hk1, hL1sub, hlive1⟩ := extractLiveBin_aux hg vs (v :: bank) k L hbuild.2 hcb' hsub' hlive
    by_cases hv : v ∈ L1 ∧ v ∉ bank
    · obtain ⟨hvL, hvb⟩ := hv
      have hv0 : v ≠ 0 := fun h0 => liveBin_zero_not_mem hg hlive1 (h0 ▸ hvL)
      obtain ⟨a, b, op, hop, haA, hbA, hvEq⟩ := hbuild.1
      have ha0 : a ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_left mask op b with h | h
        · exact hv0 (hvEq.trans h)
        · rcases hbA with rfl | hbM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb b hbM] at h; exact hvb ((hvEq.trans h) ▸ hbM)
      have hb0 : b ≠ 0 := by
        intro h0; subst h0
        rcases binOp_zero_right mask op a with h | h
        · exact hv0 (hvEq.trans h)
        · rcases haA with rfl | haM
          · rw [canon_zero] at h; exact hv0 (hvEq.trans h)
          · rw [hcb a haM] at h; exact hvb ((hvEq.trans h) ▸ haM)
      have haM : a ∈ bank := haA.resolve_left ha0
      have hbM : b ∈ bank := hbA.resolve_left hb0
      have hab : a ≠ b := by
        intro h; subst h
        rcases binOp_self mask op a with h0 | ha'
        · exact hv0 (hvEq.trans h0)
        · rw [hcb a haM] at ha'; exact hvb ((hvEq.trans ha') ▸ haM)
      set R := L1.erase v
      set S := insert a (insert b R)
      have hSsub : S ⊆ bank.toFinset := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact List.mem_toFinset.mpr haM
        · rcases Finset.mem_insert.mp hw with rfl | hw
          · exact List.mem_toFinset.mpr hbM
          · have h1 := hL1sub (Finset.mem_of_mem_erase hw)
            simp only [List.toFinset_cons, Finset.mem_insert] at h1
            exact h1.resolve_left (Finset.ne_of_mem_erase hw)
      have hvNotS : v ∉ S := by
        intro hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact hvb haM
        · rcases Finset.mem_insert.mp hm with rfl | hm
          · exact hvb hbM
          · exact (Finset.notMem_erase v L1) hm
      have hL1eq : insert v (dropIf (!(decide (a ∈ R))) a (dropIf (!(decide (b ∈ R))) b S)) = L1 := by
        ext w
        by_cases haR : a ∈ R <;> by_cases hbR : b ∈ R
        · simp only [haR, hbR, decide_true, Bool.not_true, Bool.false_eq_true, dropIf, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | rfl | rfl | ⟨_, hw⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h; exact Or.inr (Or.inr (Or.inr ⟨h, hw⟩))
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact (Finset.mem_erase.mp haR).2; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, dropIf, ite_true, ite_false, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact (Finset.mem_erase.mp hbR).2; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
        · simp only [haR, hbR, decide_false, Bool.not_false, dropIf, ite_true, S, R, Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro (rfl | ⟨hwa, hwb, rfl | rfl | ⟨_, hw⟩⟩); exact hvL; exact absurd rfl hwa; exact absurd rfl hwb; exact hw
          · intro hw; by_cases h : w = v; exact Or.inl h
            refine Or.inr ⟨?_, ?_, Or.inr (Or.inr ⟨h, hw⟩)⟩
            · intro hwa; subst hwa; exact haR (Finset.mem_erase.mpr ⟨h, hw⟩)
            · intro hwb; subst hwb; exact hbR (Finset.mem_erase.mpr ⟨h, hw⟩)
      refine ⟨k1 + 1, S, by simp only [List.length_cons]; omega, hSsub, ?_⟩
      apply LiveBin.step (a := a) (b := b) (op := op)
        (Finset.mem_insert_self a _) (Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
        hab ha0 hb0 hop (hvEq ▸ hv0) (hvEq ▸ hvNotS) (decide (a ∈ R)) (decide (b ∈ R))
      rw [← hvEq, hL1eq]; exact hlive1
    · refine ⟨k1, L1, by simp only [List.length_cons]; omega, ?_, hlive1⟩
      intro w hw
      have h1 := hL1sub hw
      simp only [List.toFinset_cons, Finset.mem_insert] at h1
      rcases h1 with rfl | h1
      · have hvb : w ∈ bank := by by_contra hnb; exact hv ⟨hw, hnb⟩
        exact List.mem_toFinset.mpr hvb
      · exact h1
theorem extractLiveBin {mask goal : Nat} {stock vs : List Nat}
    (hg : goal ≠ 0) (hcs : ∀ w ∈ stock, canon mask w = w)
    (hbuild : BuildsBin mask stock vs) (hhit : Avail (vs ++ stock) goal) :
    ∃ k S, k ≤ vs.length ∧ S ⊆ stock.toFinset ∧ LiveBin mask goal k S := by
  have hmem : goal ∈ vs ++ stock := hhit.resolve_left hg
  have hsub : ({goal} : Finset Nat) ⊆ (vs ++ stock).toFinset := by
    intro w hw; rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hmem
  obtain ⟨k, S, hk, hS, hL⟩ := extractLiveBin_aux hg vs stock 0 {goal} hbuild hcs hsub LiveBin.done
  exact ⟨k, S, by omega, hS, hL⟩
theorem liveBin_agrees {mask goal k p n : Nat} {S : Finset Nat}
    (hp : mask.testBit p = true) (hn : mask.testBit n = true)
    (h : LiveBin mask goal k S) (hag : ∀ w ∈ S, w.testBit p = w.testBit n) :
    goal.testBit p = goal.testBit n := by
  induction h with
  | done => exact hag goal (Finset.mem_singleton_self goal)
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB _ ih =>
    apply ih; intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have ea := hag a ha
      have eb := hag b hb
      unfold binOp
      cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> simp only [bsel_true, bsel_false]
      all_goals rw [canon_testBit_eq hp hn]
      all_goals simp [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, hp, hn, ea, eb]
    · exact hag w (dropIf_subset _ _ _ (dropIf_subset _ _ _ hw))
def forceW {α : Type} (w : Nat) (k : Nat → α) : α :=
  Nat.rec (k 0) (fun m _ => k (m + 1)) w
theorem forceW_eq {α : Type} (w : Nat) (k : Nat → α) : forceW w k = k w := by
  cases w <;> rfl
def forceWs (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => forceW w (fun v => next (fun rest => k (v :: rest)))) ws) k
theorem forceWs_eq (ws : List Nat) (k : List Nat → Bool) : forceWs ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW w (fun v => forceWs ws (fun rest => k (v :: rest))) = _
    rw [forceW_eq, ih]
def dagPart (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      (Nat.beq p 0 || Nat.beq n 0) ||
        forceW (p &&& w) (fun up =>
          forceW (n &&& w) (fun down =>
            rest up down &&
              forceW (p ^^^ up) (fun offP =>
                forceW (n ^^^ down) (rest offP))))) ws
theorem offBits {v w i : Nat} (h : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at h
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at h ⊢
theorem dagPart_sound {ws : List Nat} {pos neg : Nat} (fail : dagPart ws pos neg = false) :
    ∃ p n, pos.testBit p = true ∧ neg.testBit n = true ∧ ∀ w ∈ ws, w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all; apply hn; apply Nat.eq_of_testBit_eq; intro i; simp [all i]
  induction ws generalizing pos neg with
  | nil =>
    change (Nat.beq pos 0 || Nat.beq neg 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p, hp⟩ := nonempty (ne_of_beq_false fail.1)
    obtain ⟨n, hn⟩ := nonempty (ne_of_beq_false fail.2)
    exact ⟨p, n, hp, hn, by simp⟩
  | cons w ws ih =>
    change ((Nat.beq pos 0 || Nat.beq neg 0) ||
      forceW (pos &&& w) (fun up =>
        forceW (neg &&& w) (fun down =>
          dagPart ws up down &&
            forceW (pos ^^^ up) (fun offP =>
              forceW (neg ^^^ down) (dagPart ws offP))))) = false at fail
    simp only [forceW_eq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p, n, hp, hn, ag⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p, n, hp.1, hn.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp.2, hn.2]
      · exact ag a ha
    · obtain ⟨p, n, hp, hn, ag⟩ := ih off
      have hp' := offBits hp
      have hn' := offBits hn
      refine ⟨p, n, hp'.1, hn'.1, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · rw [hp'.2, hn'.2]
      · exact ag a ha
theorem dagPart_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    dagPart ws goal (mask ^^^ goal) = true := by
  by_contra hf
  have hfalse : dagPart ws goal (mask ^^^ goal) = false := by
    cases h : dagPart ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, ag⟩ := dagPart_sound hfalse
  have hpm : mask.testBit p = true := by
    have e := congrArg (fun x => x.testBit p) hgm
    simp only [Nat.testBit_and, hp, Bool.true_and] at e; exact e
  have hnm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have imp : goal.testBit n = true → mask.testBit n = true := by
      intro hg
      have e := congrArg (fun x => x.testBit n) hgm
      simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
    cases hm : mask.testBit n <;> cases hg : goal.testBit n <;> simp_all
  have eq := liveBin_agrees hpm hnm.1 hlive (fun w hw => ag w (List.mem_toFinset.mp hw))
  rw [hp, hnm.2] at eq; exact Bool.noConfusion eq
def flatSet (cut : Nat) (S : Finset Nat) : Finset Nat :=
  S.filter (fun w => Nat.beq (canon cut w) 0)
theorem flatSet_insert_notMem {cut w : Nat} {S : Finset Nat} (hw : w ∉ S) :
    (flatSet cut (insert w S)).card =
      if canon cut w = 0 then (flatSet cut S).card + 1 else (flatSet cut S).card := by
  unfold flatSet
  rw [Finset.filter_insert]
  by_cases hc : canon cut w = 0
  · simp only [hc, Nat.beq_refl, ite_true]
    exact Finset.card_insert_of_notMem (fun h => hw (Finset.mem_filter.mp h).1)
  · simp only [beq_false_ne hc, Bool.false_eq_true, ite_false, hc]
theorem flatSet_erase {cut w : Nat} {S : Finset Nat} :
    (flatSet cut S).card ≤ (flatSet cut (S.erase w)).card + (if canon cut w = 0 then 1 else 0) := by
  unfold flatSet
  rw [Finset.filter_erase]
  by_cases hm : w ∈ S.filter (fun x => Nat.beq (canon cut x) 0)
  · have hcw : canon cut w = 0 := Nat.eq_of_beq_eq_true (Finset.mem_filter.mp hm).2
    have hcard := Finset.card_erase_add_one hm
    simp only [hcw, ite_true]; omega
  · rw [Finset.erase_eq_of_notMem hm]; omega
theorem maskedBuildBin {mask cut goal k : Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) (hgnf : canon cut goal ≠ 0)
    (h : LiveBin mask goal k S) :
    ∀ (bank : List Nat), (∀ w ∈ S, Avail bank (canon cut w)) →
      ∃ vs, vs.length + (flatSet cut S).card ≤ k ∧ BuildsBin cut bank vs ∧
        Avail (vs ++ bank) (canon cut goal) := by
  induction h with
  | done =>
    intro bank hsup
    have hfl : (flatSet cut {goal}).card = 0 := by
      unfold flatSet
      simp [hgnf]
    exact ⟨[], by simp [hfl], trivial, hsup goal (Finset.mem_singleton_self goal)⟩
  | @step k S a b op ha hb hab ha0 hb0 hop hz hf keepA keepB tail ih =>
    intro bank hsup
    set z := binOp mask op a b
    set S1 := dropIf (!keepB) b S
    set S2 := dropIf (!keepA) a S1
    set S' := insert z S2
    have hS2sub : S2 ⊆ S := Finset.Subset.trans (dropIf_subset _ _ _) (dropIf_subset _ _ _)
    have hzNotS2 : z ∉ S2 := fun hm => hf (hS2sub hm)
    have hfl1 : (flatSet cut S).card ≤ (flatSet cut S1).card + (if canon cut b = 0 then 1 else 0) := by
      unfold S1 dropIf; split; exact flatSet_erase; omega
    have hfl2 : (flatSet cut S1).card ≤ (flatSet cut S2).card + (if canon cut a = 0 then 1 else 0) := by
      unfold S2 dropIf; split; exact flatSet_erase; omega
    have hfl3 : (flatSet cut S').card =
        if canon cut z = 0 then (flatSet cut S2).card + 1 else (flatSet cut S2).card :=
      flatSet_insert_notMem hzNotS2
    have hcz : canon cut z = 0 ∨ canon cut z = canon cut a ∨ canon cut z = canon cut b ∨
        ∃ op' < 4, canon cut z = binOp cut op' (canon cut a) (canon cut b) :=
      canon_sub_binOp sub
    by_cases hfa : canon cut a = 0
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact h
          · exact h.trans hfa
          · exact h.trans hfb
          · rw [hfa, hfb] at h
            rcases binOp_zero_left cut op' 0 with h0 | h0
            · exact h.trans h0
            · exact h.trans (h0.trans (canon_zero cut))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · exact Or.inl hfz
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, hfz, ite_true] at hfl1 hfl2 hfl3
        exact ⟨vs, by omega, hbd, hhit⟩
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut b := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inl (h.trans hfa)
          · exact Or.inr h
          · rw [hfa] at h
            rcases binOp_zero_left cut op' (canon cut b) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut b)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | hb'
            · exact Or.inl h0
            · rw [hb']; exact hsup b hb
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
    · by_cases hfb : canon cut b = 0
      · have hfz : canon cut z = 0 ∨ canon cut z = canon cut a := by
          rcases hcz with h | h | h | ⟨op', _, h⟩
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl (h.trans hfb)
          · rw [hfb] at h
            rcases binOp_zero_right cut op' (canon cut a) with h0 | h0
            · exact Or.inl (h.trans h0)
            · exact Or.inr (h.trans (h0.trans (canon_idem cut a)))
        have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl | hw
          · rcases hfz with h0 | ha'
            · exact Or.inl h0
            · rw [ha']; exact hsup a ha
          · exact hsup w (hS2sub hw)
        obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
        simp only [hfa, hfb, ite_true, ite_false] at hfl1 hfl2
        have : (flatSet cut S2).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        exact ⟨vs, by omega, hbd, hhit⟩
      · simp only [hfa, hfb, ite_false] at hfl1 hfl2
        have hfl_le : (flatSet cut S).card ≤ (flatSet cut S').card := by split at hfl3 <;> omega
        rcases hcz with h0 | ha' | hb' | ⟨op', hop', hbin⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inl h0
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [ha']; exact hsup a ha
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · have hsup' : ∀ w ∈ S', Avail bank (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · rw [hb']; exact hsup b hb
            · exact hsup w (hS2sub hw)
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih bank hsup'
          exact ⟨vs, by omega, hbd, hhit⟩
        · set cz := canon cut z
          have hgate : GateBin cut bank cz := ⟨canon cut a, canon cut b, op', hop', hsup a ha, hsup b hb, hbin⟩
          have hsup' : ∀ w ∈ S', Avail (cz :: bank) (canon cut w) := by
            intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Or.inr List.mem_cons_self
            · exact avail_weaken (fun u hu => List.mem_cons_of_mem _ hu) (hsup w (hS2sub hw))
          obtain ⟨vs, hlen, hbd, hhit⟩ := ih (cz :: bank) hsup'
          refine ⟨cz :: vs, by simp only [List.length_cons]; omega, ⟨hgate, hbd⟩, ?_⟩
          exact avail_weaken (fun u hu => by simp only [List.mem_append, List.mem_cons] at hu ⊢; tauto) hhit
def flatCount (cut : Nat) (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ cnt => bsel (Nat.beq (canon cut w) 0) (cnt + 1) cnt) ws
theorem flatCount_card (cut : Nat) {ws : List Nat} (nd : ws.Nodup) :
    flatCount cut ws = (flatSet cut ws.toFinset).card := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hnd := List.nodup_cons.mp nd
    have fresh : w ∉ ws.toFinset := by simpa using hnd.1
    change bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws) = _
    rw [List.toFinset_cons, flatSet_insert_notMem fresh, ih hnd.2]
    by_cases hc : canon cut w = 0
    · simp [hc, bsel]
    · rw [beq_false_ne hc, bsel_false]; simp [hc]
def availB (bank : List Nat) (w : Nat) : Bool :=
  Nat.beq w 0 || bank.contains w
theorem availB_spec {bank : List Nat} {w : Nat} : availB bank w = true ↔ Avail bank w := by
  unfold availB Avail; simp [Nat.beq_eq]
def addUniq (w : Nat) (l : List Nat) : List Nat :=
  if l.contains w then l else w :: l
def recipeStart (cut : Nat) (stock ws : List Nat) : List Nat :=
  List.rec [] (fun w _ acc =>
    let v := canon cut w
    if availB stock v then acc else addUniq v acc) ws
def recipeClose (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      let v := canon cut w
      if acc.contains v then
        let va := canon cut a
        let vb := canon cut b
        let acc1 := if availB stock va then acc else addUniq va acc
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        next acc2
      else next acc) hist needed
def KnownBin (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ b ∈ bounds, LowerBin b.1 b.2.1 b.2.2.2 b.2.2.1
def insertSorted (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => bsel (Nat.ble x y) (x :: y :: ys) (y :: ih)) l
theorem insertSorted_mem {x w : Nat} {l : List Nat} :
    w ∈ insertSorted x l ↔ w = x ∨ w ∈ l := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    change w ∈ bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys) ↔ _
    cases Nat.ble x y
    · rw [bsel_false]; simp only [List.mem_cons, ih]; tauto
    · rw [bsel_true]; simp only [List.mem_cons]
theorem insertSorted_nodup {x : Nat} {l : List Nat} (hx : x ∉ l) (nd : l.Nodup) :
    (insertSorted x l).Nodup := by
  induction l with
  | nil => simp [insertSorted]
  | cons y ys ih =>
    have hnd := List.nodup_cons.mp nd
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxs : x ∉ ys := fun h => hx (List.mem_cons_of_mem _ h)
    change (bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)).Nodup
    cases Nat.ble x y
    · rw [bsel_false]
      apply List.nodup_cons.mpr
      refine ⟨fun hm => ?_, ih hxs hnd.2⟩
      rcases insertSorted_mem.mp hm with h | h
      · exact hxy h.symm
      · exact hnd.1 h
    · rw [bsel_true]; exact List.nodup_cons.mpr ⟨hx, nd⟩
def dropVal (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  bsel drop (List.rec [] (fun y _ ih => bsel (Nat.beq y x) ih (y :: ih)) l) l
theorem dropVal_mem {drop : Bool} {x w : Nat} {l : List Nat} :
    w ∈ dropVal drop x l ↔ w ∈ l ∧ (drop = true → w ≠ x) := by
  cases drop
  · simp [dropVal, bsel]
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      change w ∈ bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys) ↔ _
      cases hb : Nat.beq y x
      · rw [bsel_false]
        have hne : y ≠ x := ne_of_beq_false hb
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro (rfl | ⟨hw, hwx⟩); exact ⟨Or.inl rfl, hne⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact Or.inl rfl; exact Or.inr ⟨hw, hwx⟩
      · rw [bsel_true]
        have heq : y = x := Nat.eq_of_beq_eq_true hb
        subst heq
        simp only [List.mem_cons, ih, true_implies]
        constructor
        · rintro ⟨hw, hwx⟩; exact ⟨Or.inr hw, hwx⟩
        · rintro ⟨rfl | hw, hwx⟩; exact absurd rfl hwx; exact ⟨hw, hwx⟩
theorem dropVal_nodup {drop : Bool} {x : Nat} {l : List Nat} (nd : l.Nodup) :
    (dropVal drop x l).Nodup := by
  cases drop
  · exact nd
  · induction l with
    | nil => simp [dropVal, bsel]
    | cons y ys ih =>
      have hnd := List.nodup_cons.mp nd
      change (bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)).Nodup
      cases Nat.beq y x
      · rw [bsel_false]
        exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (dropVal_mem.mp hm).1, ih hnd.2⟩
      · rw [bsel_true]; exact ih hnd.2
theorem dropVal_toFinset (drop : Bool) (x : Nat) (l : List Nat) :
    (dropVal drop x l).toFinset = dropIf drop x l.toFinset := by
  ext w; simp only [List.mem_toFinset, dropVal_mem, dropIf]
  cases drop <;> simp [Finset.mem_erase, and_comm]
def subsetWords (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (b >>> 1)
      bsel (Nat.beq (b &&& 1) 1) (insertSorted w rest) rest) stock) bits
theorem subsetWords_subset (stock : List Nat) (bits : Nat) :
    ∀ w ∈ subsetWords stock bits, w ∈ stock := by
  induction stock generalizing bits with
  | nil => intro w hw; simp [subsetWords] at hw
  | cons x xs ih =>
    intro w hw
    change w ∈ bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1)) at hw
    cases hb : Nat.beq (bits &&& 1) 1
    · rw [hb, bsel_false] at hw; exact List.mem_cons_of_mem _ (ih _ w hw)
    · rw [hb, bsel_true] at hw
      rcases insertSorted_mem.mp hw with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih _ w hm)
theorem subsetWords_nodup {stock : List Nat} (nd : stock.Nodup) (bits : Nat) :
    (subsetWords stock bits).Nodup := by
  induction stock generalizing bits with
  | nil => simp [subsetWords]
  | cons x xs ih =>
    have hnd := List.nodup_cons.mp nd
    change (bsel (Nat.beq (bits &&& 1) 1)
      (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))).Nodup
    cases Nat.beq (bits &&& 1) 1
    · rw [bsel_false]; exact ih hnd.2 _
    · rw [bsel_true]; exact insertSorted_nodup (fun hm => hnd.1 (subsetWords_subset xs _ x hm)) (ih hnd.2 _)
theorem exists_subsetToken (stock : List Nat) (S : Finset Nat) :
    ∃ bits < 2 ^ stock.length, (subsetWords stock bits).toFinset = S ∩ stock.toFinset := by
  induction stock with
  | nil => exact ⟨0, by simp, by simp [subsetWords]⟩
  | cons x xs ih =>
    obtain ⟨b, hb, heq⟩ := ih
    by_cases hx : x ∈ S
    · refine ⟨2 * b + 1, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b + 1) >>> 1 = b := by change (2 * b + 1) / 2 = b; omega
      have hmod : ((2 * b + 1) &&& 1) = 1 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b + 1) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b + 1) >>> 1)))
        (subsetWords xs ((2 * b + 1) >>> 1))).toFinset = _
      rw [hdiv, hmod, Nat.beq_refl, bsel_true]
      ext w; simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro (rfl | ⟨hs, hxs⟩); exact ⟨hx, Or.inl rfl⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact Or.inl rfl; exact Or.inr ⟨hs, hxs⟩
    · refine ⟨2 * b, by simp only [List.length_cons, Nat.pow_succ]; omega, ?_⟩
      have hdiv : (2 * b) >>> 1 = b := by change (2 * b) / 2 = b; omega
      have hmod : ((2 * b) &&& 1) = 0 := by rw [Nat.and_one_is_mod]; omega
      change (bsel (Nat.beq ((2 * b) &&& 1) 1)
        (insertSorted x (subsetWords xs ((2 * b) >>> 1)))
        (subsetWords xs ((2 * b) >>> 1))).toFinset = _
      rw [hdiv, hmod]
      change (subsetWords xs b).toFinset = _
      ext w; simp only [List.mem_toFinset, Finset.mem_inter, List.toFinset_cons, Finset.mem_insert]
      have hw : w ∈ subsetWords xs b ↔ w ∈ S ∧ w ∈ xs := by
        have e := congrArg (fun t => w ∈ t) heq; simpa [List.mem_toFinset] using e
      rw [hw]; constructor
      · rintro ⟨hs, hxs⟩; exact ⟨hs, Or.inr hxs⟩
      · rintro ⟨hs, rfl | hxs⟩; exact absurd hs hx; exact ⟨hs, hxs⟩
def rootState (stock : List Nat) (fuel token : Nat) : Nat × List Nat × List (Nat × Nat × Nat) :=
  (fuel, subsetWords stock token, [])
def childState (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := token &&& 3
  let op := (token >>> 2) &&& 3
  let b := (token >>> 4) &&& 15
  let a := token >>> 8
  if Nat.beq fuel 0 || !(Nat.blt a b) || !(Nat.blt b ws.length) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let z := binOp mask op x y
    if Nat.beq z 0 || ws.contains z then none
    else
      let keepA := Nat.beq (keep &&& 1) 1
      let keepB := Nat.beq ((keep >>> 1) &&& 1) 1
      let rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
      some (fuel - 1, insertSorted z rest, (z, x, y) :: hist)
theorem childState_wf {mask token : Nat} {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (nd : st.2.1.Nodup) (h : childState mask token st = some ch) :
    ch.1 < st.1 ∧ ch.2.1.Nodup := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at nd
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · rename_i hfresh
      have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok hfresh
      have hfpos : fuel ≠ 0 := fun hf => hok (Or.inl (Or.inl hf))
      have hznot : ¬(ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0)
          (ws.getD ((token >>> 4) &&& 15) 0)) = true) := fun hm => hfresh (Or.inr hm)
      refine ⟨by dsimp; omega, ?_⟩
      apply insertSorted_nodup
      · intro hm
        have hmem := (dropVal_mem.mp (dropVal_mem.mp hm).1).1
        exact hznot (List.contains_iff_mem.mpr hmem)
      · exact dropVal_nodup (dropVal_nodup nd)
def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then
        if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
      else (prev (parent - 1)).bind (childState mask token)) (fuel + 1)) i
theorem dagTrace_nodup {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    (nd : stock.Nodup) {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) : st.2.1.Nodup := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s → s.2.1.Nodup from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s; exact subsetWords_nodup nd _
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p => rw [hp] at h; exact (childState_wf (ih _ _ hp) h).2
def treeBlock (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      if Nat.blt a b then
        let m := (a + b) / 2
        if Nat.beq a m then f a else next a m && next m b
      else true) (hi - lo + 1)) lo hi
theorem treeBlock_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlock lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  unfold treeBlock at h
  suffices ∀ steps a b, b - a ≤ steps →
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b = true →
      ∀ i, a ≤ i → i < b → f i = true by
    intro i h1 h2; exact this (hi - lo + 1) lo hi (by omega) h i h1 h2
  intro steps
  induction steps with
  | zero => intro a b hba _ i h1 h2; omega
  | succ s ih =>
    intro a b hba h i h1 h2
    dsimp only at h
    have hab : Nat.blt a b = true := Nat.blt_eq.mpr (by omega)
    simp only [hab, ite_true] at h
    set m := (a + b) / 2
    by_cases ham : a = m
    · have hbm : Nat.beq a m = true := Nat.beq_eq.mpr ham
      simp only [hbm, ite_true] at h
      have hia : i = a := by omega
      subst hia; exact h
    · have hbm : Nat.beq a m = false := beq_false_ne ham
      simp only [hbm, Bool.false_eq_true, ite_false] at h
      rcases Bool.and_eq_true_iff.mp h with ⟨hl, hr⟩
      by_cases him : i < m
      · exact ih a m (by omega) hl i h1 him
      · exact ih m b (by omega) hr i (by omega) h2
theorem block_join {a m b : Nat} {f : Nat → Bool}
    (h1 : ∀ i, a ≤ i → i < m → f i = true)
    (h2 : ∀ i, m ≤ i → i < b → f i = true) :
    ∀ i, a ≤ i → i < b → f i = true := by
  intro i hi1 hi2
  by_cases h : i < m
  · exact h1 i hi1 h
  · exact h2 i (by omega) hi2
theorem getElem_index_lt {l : List Nat} {x : Nat} (hx : x ∈ l) :
    ∃ i < l.length, l.getD i 0 = x := by
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hx
  refine ⟨i, hi, ?_⟩
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, heq]
theorem list_len_child {x y z : Nat} {ws : List Nat} {keepA keepB : Bool}
    (nd : ws.Nodup) (hx : x ∈ ws) (hy : y ∈ ws) (hxy : x ≠ y) (hz : z ∉ ws) :
    (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).length =
      ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) := by
  have nd' : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).Nodup :=
    insertSorted_nodup (fun hm => hz (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
  have h1 := List.toFinset_card_of_nodup nd'
  have h2 := List.toFinset_card_of_nodup nd
  have hset : (insertSorted z (dropVal (!keepA) x (dropVal (!keepB) y ws))).toFinset =
      insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
    ext w
    simp only [List.mem_toFinset, insertSorted_mem, Finset.mem_insert, ← dropVal_toFinset]
  rw [hset] at h1
  have hz' : z ∉ dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset) :=
    fun hm => hz (List.mem_toFinset.mp (dropIf_subset _ _ _ (dropIf_subset _ _ _ hm)))
  rw [Finset.card_insert_of_notMem hz'] at h1
  set T := dropIf (!keepB) y ws.toFinset
  have hxb : x ∈ T := by
    unfold T dropIf; split
    · exact Finset.mem_erase.mpr ⟨hxy, List.mem_toFinset.mpr hx⟩
    · exact List.mem_toFinset.mpr hx
  have hcb : T.card = ws.toFinset.card - (if keepB then 0 else 1) := by
    unfold T dropIf; cases keepB
    · have := Finset.card_erase_add_one (List.mem_toFinset.mpr hy); simp; omega
    · simp
  have hca : (dropIf (!keepA) x T).card = T.card - (if keepA then 0 else 1) := by
    unfold dropIf; cases keepA
    · have := Finset.card_erase_add_one hxb; simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false]; omega
    · simp
  have hlen2 : 2 ≤ ws.toFinset.card := by
    have hsub : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
      intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
      · exact List.mem_toFinset.mpr hx
      · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hy
    have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
    have := Finset.card_le_card hsub; omega
  rw [← h1, hca, hcb, h2]
  cases keepA <;> cases keepB <;> simp <;> omega
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) : Nat := (gs.filter isBinary).length
def legal (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def evalBit (k : Nat) (w : Nat) : Bool := w.testBit k
def stepBool (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def actionWord (w : List Nat) (g : Gate) : Nat := match g.op with
  | .not => fullMask ^^^ ((g.inputs.head?.map (fun i => w.getD i 0)).getD 0)
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) fullMask
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0
theorem fullMask_eq : fullMask = 2 ^ 64 - 1 := by decide
theorem fullMask_bit {k : Nat} (hk : k < 64) : fullMask.testBit k = true := by
  rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
theorem readBit (w : List Nat) (i k : Nat) :
    (w.map (evalBit k)).getD i false = evalBit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), evalBit]
theorem actionWord_spec (w : List Nat) (g : Gate) (hg : legal g) {k : Nat} (hk : k < 64) :
    stepBool (w.map (evalBit k)) g = (w ++ [actionWord w g]).map (evalBit k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hcap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hcap
  have hfm := fullMask_bit hk
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [stepBool, List.map_cons, List.map_nil, readBit, List.map_append, actionWord,
      GateOp.eval, List.foldr_cons, List.foldr_nil, List.head?_cons, List.head?_nil,
      List.headD_cons, List.headD_nil, Option.map_some, Option.map_none, Option.getD_some,
      Option.getD_none, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.and_true, Bool.or_false, evalBit, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.zero_testBit, hfm, Bool.true_xor]
def rawVars : List Nat :=
  [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def rootStock : List Nat :=
  [0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f,
   0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff]
theorem rawVars_avail : ∀ u ∈ rawVars, Avail rootStock (canon fullMask u) := by
  intro u hu
  simp only [rawVars, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr (by decide)
theorem compileBin_aux (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w bank : List Nat)
    (hw : ∀ u ∈ w, Avail bank (canon fullMask u)) :
    ∃ vs, vs.length ≤ binaryCost gs ∧ BuildsBin fullMask bank vs ∧
      ∀ u ∈ gs.foldl (fun acc g => acc ++ [actionWord acc g]) w, Avail (vs ++ bank) (canon fullMask u) := by
  induction gs generalizing w bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, by simpa using hw⟩
  | cons g gs ih =>
    have hg0 := hg g List.mem_cons_self
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    set z := actionWord w g
    have hread (i : Nat) : Avail bank (canon fullMask (w.getD i 0)) := by
      by_cases hi : i < w.length
      · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hstep : Avail bank (canon fullMask z) ∨ (isBinary g = true ∧ GateBin fullMask bank (canon fullMask z)) := by
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hcap⟩ := hg0
      change op = .and ∨ op = .or ∨ op = .not at hop
      change args.length ≤ 2 at hcap
      rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at hcap
      · rcases hop with rfl | rfl | rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_zero]; exact Or.inl rfl
        · left; simp [z, actionWord, canon_self]; exact Or.inl rfl
      · rcases hop with rfl | rfl | rfl
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          rw [canon_land]; exact hread i
        · left; simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          exact hread i
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
      · rcases hop with rfl | rfl | rfl
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
          have h1 : canon fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask)) =
              canon fullMask (w.getD i 0 &&& w.getD j 0) := by
            rw [← canon_land fullMask (w.getD i 0 &&& (w.getD j 0 &&& fullMask))]
            rw [← canon_land fullMask (w.getD i 0 &&& w.getD j 0)]
            congr 1; apply Nat.eq_of_testBit_eq; intro k; simp only [Nat.testBit_and]
            cases (w.getD i 0).testBit k <;> cases (w.getD j 0).testBit k <;> cases fullMask.testBit k <;> rfl
          rw [h1]
          rcases canon_and_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · simp only [z, actionWord, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Nat.or_zero]
          rcases canon_or_in_binOp fullMask (w.getD i 0) (w.getD j 0) with h0 | hi' | hj' | ⟨op', hop', hbin⟩
          · left; exact Or.inl h0
          · left; rw [hi']; exact hread i
          · left; rw [hj']; exact hread j
          · right; exact ⟨rfl, canon fullMask (w.getD i 0), canon fullMask (w.getD j 0), op', hop', hread i, hread j, hbin⟩
        · left; simp only [z, actionWord, List.head?_cons, Option.map_some, Option.getD_some]
          rw [canon_xor_mask]; exact hread i
    rcases hstep with hav | ⟨hbin, hgate⟩
    · have hw' : ∀ u ∈ w ++ [z], Avail bank (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact hw u hu
        · rw [List.mem_singleton.mp hu]; exact hav
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) bank hw'
      have hbc : binaryCost gs ≤ binaryCost (g :: gs) := by
        unfold binaryCost; simp only [List.filter]; cases isBinary g <;> simp
      exact ⟨vs, Nat.le_trans hlen hbc, hbd, hall⟩
    · set cz := canon fullMask z
      have hw' : ∀ u ∈ w ++ [z], Avail (cz :: bank) (canon fullMask u) := by
        intro u hu; rcases List.mem_append.mp hu with hu | hu
        · exact avail_weaken (fun a ha => List.mem_cons_of_mem _ ha) (hw u hu)
        · rw [List.mem_singleton.mp hu]; exact Or.inr List.mem_cons_self
      obtain ⟨vs, hlen, hbd, hall⟩ := ih hgs (w ++ [z]) (cz :: bank) hw'
      have hbc : binaryCost (g :: gs) = binaryCost gs + 1 := by
        unfold binaryCost; simp [hbin]
      refine ⟨cz :: vs, by simp only [List.length_cons, hbc]; omega, ⟨hgate, hbd⟩, ?_⟩
      intro u hu
      exact avail_weaken (fun a ha => by simp only [List.mem_append, List.mem_cons] at ha ⊢; tauto) (hall u hu)
theorem foldl_evalBit (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (w : List Nat) {k : Nat} (hk : k < 64) :
    gs.foldl stepBool (w.map (evalBit k)) =
      (gs.foldl (fun acc g => acc ++ [actionWord acc g]) w).map (evalBit k) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [actionWord_spec w g (hg g List.mem_cons_self) hk]
    exact ih (fun x hx => hg x (List.mem_cons_of_mem _ hx)) (w ++ [actionWord w g])
theorem rawVars_ofFn (x : Fin 6 → Bool) :
    List.ofFn x = rawVars.map (evalBit (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) := by
  have hx : ∀ (b0 b1 b2 b3 b4 b5 : Bool),
      [b0, b1, b2, b3, b4, b5] =
      rawVars.map (evalBit ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))) := by
    decide +kernel
  have hsum : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) =
      (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
      (if x 3 then 8 else 0) + (if x 4 then 16 else 0) + (if x 5 then 32 else 0) := by
    simp [Fin.sum_univ_six]
  rw [hsum, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  exact hx (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
theorem sum_bits_6 (n : Nat) (hn : n < 64) :
    (∑ i : Fin 6, if n.testBit i.val then 2 ^ (i : Nat) else 0) = n := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two]
  change (if n.testBit 0 then 1 else 0) + (if n.testBit 1 then 2 else 0) +
    (if n.testBit 2 then 4 else 0) + (if n.testBit 3 then 8 else 0) +
    (if n.testBit 4 then 16 else 0) + (if n.testBit 5 then 32 else 0) = n
  revert n; decide +kernel
theorem table2_from_lowerBin (target m : Nat)
    (hlow : LowerBin fullMask rootStock (canon fullMask target) (m - 1))
    (wg : List Gate) (wout : Nat) (hsz : wg.length = m)
    (hmono : Monotone2 ⟨wg, wout⟩)
    (heval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, wout⟩ (List.ofFn x) =
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) :
    ∀ s : Nat, HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0)) s →
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool,
      C.eval (List.ofFn x) = Nat.testBit target (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) := by
  intro s ⟨C, hfan, hsize, hC⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hgm, hgop⟩ := hasNot
    have hshort : binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, hgm, by simp [isBinary, hgop]⟩
    have hleg : ∀ g ∈ C.gates, legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    obtain ⟨vs, hvlen, hvbd, hvhit⟩ := compileBin_aux C.gates hleg rawVars rootStock rawVars_avail
    set finalW := C.gates.foldl (fun acc g => acc ++ [actionWord acc g]) rawVars
    have hout_eq : finalW.getD C.output 0 &&& fullMask = target &&& fullMask := by
      apply Nat.eq_of_testBit_eq; intro k
      by_cases hk : k < 64
      · have hfm := fullMask_bit hk
        simp only [Nat.testBit_and, hfm, Bool.and_true]
        let x : Fin 6 → Bool := fun i => k.testBit i.val
        have hxidx : (∑ i : Fin 6, if x i then 2 ^ (i : Nat) else 0) = k := sum_bits_6 k hk
        have h1 := hC x
        dsimp only at h1
        rw [hxidx, rawVars_ofFn x, hxidx] at h1
        change (C.gates.foldl stepBool (rawVars.map (evalBit k))).getD C.output false = target.testBit k at h1
        rw [foldl_evalBit C.gates hleg rawVars hk, readBit] at h1
        exact h1
      · have hfm0 : fullMask.testBit k = false := by
          rw [fullMask_eq, Nat.testBit_two_pow_sub_one]; simp [hk]
        simp [Nat.testBit_and, hfm0]
    have hout_avail : Avail (vs ++ rootStock) (canon fullMask target) := by
      rw [← canon_land fullMask target, ← hout_eq, canon_land]
      by_cases hi : C.output < finalW.length
      · exact hvhit _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi])
      · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi), canon_zero]; exact Or.inl rfl
    have hge := hlow vs hvbd hout_avail
    have hcsz : C.size = C.gates.length := rfl
    have hwsz : (⟨wg, wout⟩ : Circuit).size = m := hsz
    exact ⟨⟨wg, wout⟩, hmono, by omega, heval⟩
  · refine ⟨C, ?_, hsize, hC⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
def memN (z : Nat) (l : List Nat) : Bool :=
  List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
theorem memN_eq (z : Nat) (l : List Nat) : memN z l = l.contains z := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem]
  induction l with
  | nil => simp [memN]
  | cons w ws ih =>
    change Bool.rec (memN z ws) true (Nat.beq z w) = true ↔ z ∈ w :: ws
    cases h : Nat.beq z w
    · have hne : z ≠ w := ne_of_beq_false h
      simp [ih, hne]
    · have heq : z = w := Nat.eq_of_beq_eq_true h
      simp [heq]
def lenN (l : List Nat) : Nat :=
  List.rec 0 (fun _ _ ih => Nat.add ih 1) l
theorem lenN_eq (l : List Nat) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons _ ws ih => change Nat.add (lenN ws) 1 = ws.length + 1; rw [ih]
def getDN (l : List Nat) (i : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun w _ ih k => Nat.rec w (fun m _ => ih m) k) l) i
theorem getDN_eq (l : List Nat) (i : Nat) : getDN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => rfl
  | cons w ws ih =>
    cases i with
    | zero => rfl
    | succ m => change getDN ws m = (w :: ws).getD (m + 1) 0; rw [ih]; rfl
def eqListN (l1 : List Nat) : List Nat → Bool :=
  List.rec
    (fun l2 => List.rec true (fun _ _ _ => false) l2)
    (fun x _ ih l2 => List.rec false (fun y ys _ => Bool.rec false (ih ys) (Nat.beq x y)) l2) l1
theorem eqListN_eq (l1 l2 : List Nat) : eqListN l1 l2 = (l1 == l2) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> rfl
  | cons x xs ih =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      change Bool.rec false (eqListN xs ys) (Nat.beq x y) = ((x :: xs) == (y :: ys))
      rw [ih]
      by_cases h : x = y
      · subst h; simp [Nat.beq_refl]
      · have h1 : Nat.beq x y = false := beq_false_ne h
        have h2 : (x == y) = false := beq_false_of_ne h
        simp [h1, h2]
def canonF (mask w : Nat) : Nat :=
  let v := Nat.land w mask
  Bool.rec
    (Bool.rec
      (let iv := Nat.xor mask v
       Bool.rec iv v (Nat.blt v iv))
      0 (Nat.beq v mask))
    0 (Nat.beq v 0)
theorem canonF_eq (mask w : Nat) : canonF mask w = canon mask w := by
  unfold canonF canon bsel; dsimp only
  change (Bool.rec (Bool.rec (Bool.rec (mask ^^^ (w &&& mask)) (w &&& mask) ((w &&& mask).blt (mask ^^^ (w &&& mask)))) 0 ((w &&& mask).beq mask)) 0 ((w &&& mask).beq 0) : Nat) = _
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def binOpF (mask op a b : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec (canonF mask (Nat.land (Nat.xor mask a) b))
        (canonF mask (Nat.land a (Nat.xor mask b))) (Nat.beq op 2))
      (canonF mask (Nat.lor a b)) (Nat.beq op 1))
    (canonF mask (Nat.land a b)) (Nat.beq op 0)
theorem binOpF_eq (mask op a b : Nat) : binOpF mask op a b = binOp mask op a b := by
  unfold binOpF binOp bsel
  simp only [canonF_eq]
  cases Nat.beq op 0 <;> cases Nat.beq op 1 <;> cases Nat.beq op 2 <;> rfl
def dagPartF (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Bool.rec (Nat.beq n 0) true (Nat.beq p 0))
    (fun w _ rest p n =>
      Bool.rec
        (Bool.rec
          (forceW (Nat.land p w) (fun up =>
            forceW (Nat.land n w) (fun down =>
              Bool.rec false
                (forceW (Nat.xor p up) (fun offP =>
                  forceW (Nat.xor n down) (rest offP)))
                (rest up down))))
          true (Nat.beq n 0))
        true (Nat.beq p 0)) ws
theorem dagPartF_eq (ws : List Nat) (p n : Nat) : dagPartF ws p n = dagPart ws p n := by
  induction ws generalizing p n with
  | nil =>
    change Bool.rec (Nat.beq n 0) true (Nat.beq p 0) = (Nat.beq p 0 || Nat.beq n 0)
    cases Nat.beq p 0 <;> rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (forceW (Nat.land p w) (fun up =>
      forceW (Nat.land n w) (fun down =>
        Bool.rec false (forceW (Nat.xor p up) (fun offP => forceW (Nat.xor n down) (dagPartF ws offP)))
          (dagPartF ws up down)))) true (Nat.beq n 0)) true (Nat.beq p 0) =
      ((Nat.beq p 0 || Nat.beq n 0) || forceW (p &&& w) (fun up =>
        forceW (n &&& w) (fun down => dagPart ws up down &&
          forceW (p ^^^ up) (fun offP => forceW (n ^^^ down) (dagPart ws offP)))))
    simp only [forceW_eq]
    cases Nat.beq p 0
    · cases Nat.beq n 0
      · change Bool.rec false (dagPartF ws _ _) (dagPartF ws _ _) = (dagPart ws _ _ && dagPart ws _ _)
        rw [ih, ih]; cases dagPart ws (p &&& w) (n &&& w) <;> rfl
      · rfl
    · rfl
def insertSortedF (x : Nat) (l : List Nat) : List Nat :=
  List.rec [x] (fun y ys ih => Bool.rec (y :: ih) (x :: y :: ys) (Nat.ble x y)) l
theorem insertSortedF_eq (x : Nat) (l : List Nat) : insertSortedF x l = insertSorted x l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    change Bool.rec (y :: insertSortedF x ys) (x :: y :: ys) (Nat.ble x y) =
      bsel (Nat.ble x y) (x :: y :: ys) (y :: insertSorted x ys)
    rw [ih]; cases Nat.ble x y <;> rfl
def dropValF (drop : Bool) (x : Nat) (l : List Nat) : List Nat :=
  Bool.rec l (List.rec [] (fun y _ ih => Bool.rec (y :: ih) ih (Nat.beq y x)) l) drop
theorem dropValF_eq (drop : Bool) (x : Nat) (l : List Nat) : dropValF drop x l = dropVal drop x l := by
  cases drop
  · rfl
  · induction l with
    | nil => rfl
    | cons y ys ih =>
      change Bool.rec (y :: dropValF true x ys) (dropValF true x ys) (Nat.beq y x) =
        bsel (Nat.beq y x) (dropVal true x ys) (y :: dropVal true x ys)
      rw [ih]; cases Nat.beq y x <;> rfl
def subsetWordsF (stock : List Nat) (bits : Nat) : List Nat :=
  (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun w _ ih b =>
      let rest := ih (Nat.shiftRight b 1)
      Bool.rec rest (insertSortedF w rest) (Nat.beq (Nat.land b 1) 1)) stock) bits
theorem subsetWordsF_eq (stock : List Nat) (bits : Nat) : subsetWordsF stock bits = subsetWords stock bits := by
  induction stock generalizing bits with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (subsetWordsF xs (Nat.shiftRight bits 1))
      (insertSortedF x (subsetWordsF xs (Nat.shiftRight bits 1))) (Nat.beq (Nat.land bits 1) 1) =
      bsel (Nat.beq (bits &&& 1) 1) (insertSorted x (subsetWords xs (bits >>> 1))) (subsetWords xs (bits >>> 1))
    rw [ih, insertSortedF_eq]; cases Nat.beq (bits &&& 1) 1 <;> rfl
def childStateF (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, hist) := state
  let keep := Nat.land token 3
  let op := Nat.land (Nat.shiftRight token 2) 3
  let b := Nat.land (Nat.shiftRight token 4) 15
  let a := Nat.shiftRight token 8
  Bool.rec
    (Bool.rec none
      (Bool.rec none
        (let x := getDN ws a
         let y := getDN ws b
         let z := binOpF mask op x y
         Bool.rec
           (Bool.rec
             (let keepA := Nat.beq (Nat.land keep 1) 1
              let keepB := Nat.beq (Nat.land (Nat.shiftRight keep 1) 1) 1
              let rest := dropValF (Bool.rec true false keepA) x (dropValF (Bool.rec true false keepB) y ws)
              some (Nat.sub fuel 1, insertSortedF z rest, (z, x, y) :: hist))
             none (memN z ws))
           none (Nat.beq z 0))
        (Nat.blt b (lenN ws)))
      (Nat.blt a b))
    none (Nat.beq fuel 0)
theorem childStateF_eq (mask token : Nat) (state : Nat × List Nat × List (Nat × Nat × Nat)) :
    childStateF mask token state = childState mask token state := by
  obtain ⟨fuel, ws, hist⟩ := state
  unfold childStateF childState
  simp only [lenN_eq, getDN_eq, binOpF_eq, memN_eq, dropValF_eq, insertSortedF_eq]
  cases Nat.beq fuel 0
  · cases Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
    · rfl
    · cases Nat.blt ((token >>> 4) &&& 15) ws.length
      · rfl
      · cases Nat.beq (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0)) 0
        · cases ws.contains (binOp mask ((token >>> 2) &&& 3) (ws.getD (token >>> 8) 0) (ws.getD ((token >>> 4) &&& 15) 0))
          · cases Nat.beq ((token &&& 3) &&& 1) 1 <;> cases Nat.beq (((token &&& 3) >>> 1) &&& 1) 1 <;> rfl
          · rfl
        · rfl
  · rfl
def dagTraceF (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ prev j =>
      let (parent, token) := forest j
      Bool.rec
        (match prev (Nat.sub parent 1) with
         | none => none
         | some st => childStateF mask token st)
        (Bool.rec none (some (fuel, subsetWordsF stock token, []))
          (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
        (Nat.beq parent 0)) (Nat.add fuel 1)) i
theorem dagTraceF_eq (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : Nat → Nat × Nat) (i : Nat) :
    dagTraceF mask stock fuel forest i = dagTrace mask stock fuel forest i := by
  unfold dagTraceF dagTrace
  suffices ∀ steps j,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          Bool.rec
            (match prev (Nat.sub parent 1) with
             | none => none
             | some st => childStateF mask token st)
            (Bool.rec none (some (fuel, subsetWordsF stock token, []))
              (Nat.blt token (Nat.shiftLeft 1 (lenN stock))))
            (Nat.beq parent 0)) steps) j =
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j from
    this (fuel + 1) i
  intro steps
  induction steps with
  | zero => intro j; rfl
  | succ n ih =>
    intro j
    dsimp only
    have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
      rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
    cases Nat.beq (forest j).1 0
    · dsimp only
      rw [ih]
      cases (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          if Nat.beq (forest k).1 0 then
            if Nat.blt (forest k).2 (2 ^ stock.length) then some (rootState stock fuel (forest k).2) else none
          else (prev ((forest k).1 - 1)).bind (childState mask (forest k).2)) n) ((forest j).1 - 1)
      · rfl
      · exact childStateF_eq mask (forest j).2 _
    · dsimp only
      rw [hpow, subsetWordsF_eq]
      cases Nat.blt (forest j).2 (2 ^ stock.length) <;> rfl
def nthBound (bounds : List (Nat × List Nat × Nat × Nat)) (i : Nat) :
    Option (Nat × List Nat × Nat × Nat) :=
  (List.rec (motive := fun _ => Nat → Option (Nat × List Nat × Nat × Nat))
    (fun _ => none)
    (fun b _ ih k => Nat.rec (some b) (fun m _ => ih m) k) bounds) i
theorem nthBound_mem {bounds : List (Nat × List Nat × Nat × Nat)} {i : Nat} {b : Nat × List Nat × Nat × Nat}
    (h : nthBound bounds i = some b) : b ∈ bounds := by
  induction bounds generalizing i with
  | nil => simp [nthBound] at h
  | cons x xs ih =>
    cases i with
    | zero => cases h; exact List.mem_cons_self
    | succ m => exact List.mem_cons_of_mem _ (ih h)
def forceWP {α : Type} (w : Nat) (k : Nat → α) : α :=
  match w with
  | 0 => k 0
  | m + 1 => k (m + 1)
theorem forceWP_eq {α : Type} (w : Nat) (k : Nat → α) : forceWP w k = k w := by
  cases w <;> rfl
def forceCons {α : Type} (l : List Nat) (k : List Nat → α) : α :=
  match l with
  | [] => k []
  | x :: xs => k (x :: xs)
theorem forceCons_eq {α : Type} (l : List Nat) (k : List Nat → α) : forceCons l k = k l := by
  cases l <;> rfl
def forceList {α : Type} (ws : List Nat) (k : List Nat → α) : α :=
  (List.rec (motive := fun _ => (List Nat → α) → α) (fun k => k [])
    (fun w _ next k => next (fun rest => k (w :: rest))) ws) k
theorem forceList_eq {α : Type} (ws : List Nat) (k : List Nat → α) : forceList ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceList ws (fun rest => k (w :: rest)) = _
    rw [ih]
def canonV2 (mask w : Nat) : Nat :=
  forceWP (Nat.land w mask) (fun v =>
    Bool.rec
      (Bool.rec
        (forceWP (Nat.xor mask v) (fun iv => Bool.rec iv v (Nat.blt v iv)))
        0 (Nat.beq v mask))
      0 (Nat.beq v 0))
theorem canonV2_eq (mask w : Nat) : canonV2 mask w = canon mask w := by
  unfold canonV2 canon bsel; dsimp only
  rw [forceWP_eq]
  change Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      (forceWP (Nat.xor mask (w &&& mask)) (fun iv => Bool.rec (motive := fun _ => Nat) iv (w &&& mask) (Nat.blt (w &&& mask) iv)))
      0 (Nat.beq (w &&& mask) mask)) 0 (Nat.beq (w &&& mask) 0) = _
  rw [forceWP_eq]
  cases Nat.beq (w &&& mask) 0 <;> cases Nat.beq (w &&& mask) mask <;> rfl
def HistValid (mask : Nat) (stock : List Nat) : List (Nat × Nat × Nat) → Prop
  | [] => True
  | (z, x, y) :: rest =>
    (∃ op < 4, z = binOp mask op x y) ∧
    (x ∈ stock ∨ ∃ a b, (x, a, b) ∈ rest) ∧
    (y ∈ stock ∨ ∃ a b, (y, a, b) ∈ rest) ∧
    HistValid mask stock rest
def WsCovered (stock : List Nat) (hist : List (Nat × Nat × Nat)) (ws : List Nat) : Prop :=
  ∀ w ∈ ws, w ∈ stock ∨ ∃ a b, (w, a, b) ∈ hist
theorem getD_mem_of_lt {l : List Nat} {i : Nat} (hi : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi
theorem childState_valid {mask token : Nat} {stock : List Nat}
    {st ch : Nat × List Nat × List (Nat × Nat × Nat)}
    (hv : HistValid mask stock st.2.2) (hc : WsCovered stock st.2.2 st.2.1)
    (h : childState mask token st = some ch) :
    HistValid mask stock ch.2.2 ∧ WsCovered stock ch.2.2 ch.2.1 := by
  obtain ⟨fuel, ws, hist⟩ := st
  dsimp only at hv hc
  unfold childState at h; dsimp only at h
  split at h
  · contradiction
  · rename_i hok
    split at h
    · contradiction
    · have heq := Option.some.inj h
      subst ch
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at hok
      have hab : (token >>> 8) < ((token >>> 4) &&& 15) := by
        cases h1 : Nat.blt (token >>> 8) ((token >>> 4) &&& 15)
        · exfalso; exact hok (Or.inl (Or.inr h1))
        · exact Nat.blt_eq.mp h1
      have hbl : ((token >>> 4) &&& 15) < ws.length := by
        cases h2 : Nat.blt ((token >>> 4) &&& 15) ws.length
        · exfalso; exact hok (Or.inr h2)
        · exact Nat.blt_eq.mp h2
      have hx : ws.getD (token >>> 8) 0 ∈ ws := getD_mem_of_lt (by omega)
      have hy : ws.getD ((token >>> 4) &&& 15) 0 ∈ ws := getD_mem_of_lt hbl
      have hop : ((token >>> 2) &&& 3) < 4 := by
        have := Nat.and_lt_two_pow (token >>> 2) (n := 2) (by omega : 3 < 2 ^ 2)
        simpa using this
      refine ⟨⟨⟨(token >>> 2) &&& 3, hop, rfl⟩, hc _ hx, hc _ hy, hv⟩, ?_⟩
      intro w hw
      rcases insertSorted_mem.mp hw with rfl | hrest
      · exact Or.inr ⟨_, _, List.mem_cons_self⟩
      · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hrest).1).1
        rcases hc w hwm with hst | ⟨a, b, hmem⟩
        · exact Or.inl hst
        · exact Or.inr ⟨a, b, List.mem_cons_of_mem _ hmem⟩
theorem dagTrace_valid {mask fuel : Nat} {stock : List Nat} {forest : Nat → Nat × Nat}
    {i : Nat} {st : Nat × List Nat × List (Nat × Nat × Nat)}
    (h : dagTrace mask stock fuel forest i = some st) :
    HistValid mask stock st.2.2 ∧ WsCovered stock st.2.2 st.2.1 := by
  unfold dagTrace at h
  suffices ∀ steps j s,
      (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) steps) j = some s →
      HistValid mask stock s.2.2 ∧ WsCovered stock s.2.2 s.2.1 from
    this (fuel + 1) i st h
  intro steps
  induction steps with
  | zero => intro j s h; contradiction
  | succ n ih =>
    intro j s h; dsimp only at h
    split at h
    · split at h
      · have e := Option.some.inj h; subst s
        exact ⟨trivial, fun w hw => Or.inl (subsetWords_subset stock _ w hw)⟩
      · contradiction
    · cases hp : (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
        (fun _ prev k =>
          let (parent, token) := forest k
          if Nat.beq parent 0 then
            if Nat.blt token (2 ^ stock.length) then some (rootState stock fuel token) else none
          else (prev (parent - 1)).bind (childState mask token)) n) ((forest j).1 - 1) with
      | none => rw [hp] at h; contradiction
      | some p =>
        rw [hp] at h
        have ⟨hv, hc⟩ := ih _ _ hp
        exact childState_valid hv hc h
theorem addUniq_mem {w u : Nat} {l : List Nat} : u ∈ addUniq w l ↔ u = w ∨ u ∈ l := by
  unfold addUniq
  cases h : l.contains w
  · simp [List.mem_cons]
  · simp only [ite_true]
    have hw : w ∈ l := List.contains_iff_mem.mp h
    constructor
    · exact Or.inr
    · rintro (rfl | hu); exact hw; exact hu
theorem recipeStart_mem {cut : Nat} {stock ws : List Nat} {u : Nat} :
    u ∈ recipeStart cut stock ws ↔ ∃ w ∈ ws, canon cut w = u ∧ ¬Avail stock u := by
  induction ws with
  | nil => simp [recipeStart]
  | cons w ws ih =>
    change u ∈ (if availB stock (canon cut w) then recipeStart cut stock ws
                else addUniq (canon cut w) (recipeStart cut stock ws)) ↔ _
    cases ha : availB stock (canon cut w)
    · simp only [Bool.false_eq_true, ite_false, addUniq_mem, ih]
      have hna : ¬Avail stock (canon cut w) := fun h => by rw [availB_spec.mpr h] at ha; exact Bool.noConfusion ha
      constructor
      · rintro (rfl | ⟨w', hw', rfl, hnu⟩)
        · exact ⟨w, List.mem_cons_self, rfl, hna⟩
        · exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact Or.inl rfl
        · exact Or.inr ⟨w', hw', rfl, hnu⟩
    · simp only [ite_true, ih]
      have hya : Avail stock (canon cut w) := availB_spec.mp ha
      constructor
      · rintro ⟨w', hw', rfl, hnu⟩; exact ⟨w', List.mem_cons_of_mem _ hw', rfl, hnu⟩
      · rintro ⟨w', hw', rfl, hnu⟩
        rcases List.mem_cons.mp hw' with rfl | hw'
        · exact absurd hya hnu
        · exact ⟨w', hw', rfl, hnu⟩
theorem recipeClose_sub {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} {acc : List Nat} :
    ∀ u ∈ acc, u ∈ recipeClose cut stock hist acc := by
  induction hist generalizing acc with
  | nil => intro u hu; exact hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro u hu
    change u ∈ (if acc.contains (canon cut w) then
      let va := canon cut a; let vb := canon cut b
      let acc1 := if availB stock va then acc else addUniq va acc
      let acc2 := if availB stock vb then acc1 else addUniq vb acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist acc)
    split
    · apply ih
      have h1 : u ∈ (if availB stock (canon cut a) then acc else addUniq (canon cut a) acc) := by
        split; exact hu; exact addUniq_mem.mpr (Or.inr hu)
      split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · exact ih u hu
theorem recipeClose_nil (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) :
    recipeClose cut stock hist [] = [] := by
  induction hist with
  | nil => rfl
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    change (if [].contains (canon cut w) then _ else recipeClose cut stock hist []) = []
    exact ih
theorem recipeClose_mono {cut : Nat} {stock : List Nat} {hist : List (Nat × Nat × Nat)} :
    ∀ {A B : List Nat}, (∀ u ∈ A, u ∈ B) →
      ∀ u ∈ recipeClose cut stock hist A, u ∈ recipeClose cut stock hist B := by
  induction hist with
  | nil => intro A B hAB u hu; exact hAB u hu
  | cons r hist ih =>
    obtain ⟨w, a, b⟩ := r
    intro A B hAB u hu
    change u ∈ (if A.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then A else addUniq (canon cut a) A
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist A) at hu
    change u ∈ (if B.contains (canon cut w) then
      let acc1 := if availB stock (canon cut a) then B else addUniq (canon cut a) B
      let acc2 := if availB stock (canon cut b) then acc1 else addUniq (canon cut b) acc1
      recipeClose cut stock hist acc2
    else recipeClose cut stock hist B)
    cases hA : A.contains (canon cut w)
    · simp only [hA, Bool.false_eq_true, ite_false] at hu
      cases hB : B.contains (canon cut w)
      · simp only [Bool.false_eq_true, ite_false]; exact ih hAB u hu
      · simp only [ite_true]
        apply ih _ u hu
        intro x hx
        have h1 : x ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
          split; exact hAB x hx; exact addUniq_mem.mpr (Or.inr (hAB x hx))
        split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
    · have hwB : B.contains (canon cut w) = true := List.contains_iff_mem.mpr (hAB _ (List.contains_iff_mem.mp hA))
      simp only [hA, ite_true] at hu
      simp only [hwB, ite_true]
      apply ih _ u hu
      intro x hx
      have h1 : ∀ y, y ∈ (if availB stock (canon cut a) then A else addUniq (canon cut a) A) →
          y ∈ (if availB stock (canon cut a) then B else addUniq (canon cut a) B) := by
        intro y hy
        cases hca : availB stock (canon cut a)
        · simp only [hca, Bool.false_eq_true, ite_false, addUniq_mem] at hy ⊢
          rcases hy with rfl | hy; exact Or.inl rfl; exact Or.inr (hAB y hy)
        · simp only [hca, ite_true] at hy ⊢; exact hAB y hy
      cases hcb : availB stock (canon cut b)
      · simp only [hcb, Bool.false_eq_true, ite_false, addUniq_mem] at hx ⊢
        rcases hx with rfl | hx; exact Or.inl rfl; exact Or.inr (h1 x hx)
      · simp only [hcb, ite_true] at hx ⊢; exact h1 x hx
noncomputable def buildFrom (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    List (Nat × Nat × Nat) → List Nat
  | [] => []
  | (z, x, y) :: rest =>
    let vs := buildFrom cut bstock S rest
    let v := canon cut z
    let := Classical.propDecidable
    if v ∈ S ∧ ¬Avail (vs ++ bstock) v ∧ Avail (vs ++ bstock) (canon cut x) ∧ Avail (vs ++ bstock) (canon cut y)
    then vs ++ [v] else vs
theorem buildFrom_builds {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (sub : mask &&& cut = cut) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      BuildsBin cut bstock (buildFrom cut bstock S hist)
  | [], _ => trivial
  | (z, x, y) :: rest, ⟨⟨op, hop, hz⟩, _, _, hrest⟩ => by
    unfold buildFrom; dsimp only
    have ih := buildFrom_builds (bstock := bstock) (S := S) sub hrest
    split
    · rename_i hcond
      obtain ⟨_, hna, hax, hay⟩ := hcond
      have hgate : GateBin cut (buildFrom cut bstock S rest ++ bstock) (canon cut z) := by
        have hsub := canon_sub_binOp (op := op) (a := x) (b := y) sub
        rw [← hz] at hsub
        rcases hsub with h0 | hx | hy | ⟨op', hop', heq⟩
        · exact absurd (Or.inl h0) hna
        · exact absurd (hx ▸ hax) hna
        · exact absurd (hy ▸ hay) hna
        · exact ⟨canon cut x, canon cut y, op', hop', hax, hay, heq⟩
      exact builds_append ih ⟨hgate, trivial⟩
    · exact ih
theorem buildFrom_nodup_sub (cut : Nat) (bstock : List Nat) (S : Finset Nat) :
    ∀ (hist : List (Nat × Nat × Nat)),
      (buildFrom cut bstock S hist).Nodup ∧ ∀ u ∈ buildFrom cut bstock S hist, u ∈ S
  | [] => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | (z, x, y) :: rest => by
    unfold buildFrom; dsimp only
    obtain ⟨hnd, hsub⟩ := buildFrom_nodup_sub cut bstock S rest
    split
    · rename_i hcond
      obtain ⟨hvS, hna, _, _⟩ := hcond
      have hnm : canon cut z ∉ buildFrom cut bstock S rest := fun hm =>
        hna (Or.inr (List.mem_append_left bstock hm))
      refine ⟨List.nodup_append.mpr ⟨hnd, List.nodup_singleton _, fun a ha b hb heq => by
        rw [List.mem_singleton.mp hb] at heq; exact hnm (heq ▸ ha)⟩, ?_⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hsub u hu
      · rw [List.mem_singleton.mp hu]; exact hvS
    · exact ⟨hnd, hsub⟩
theorem buildFrom_mono_avail (cut : Nat) (bstock : List Nat) (S : Finset Nat)
    (r : Nat × Nat × Nat) (rest : List (Nat × Nat × Nat)) {u : Nat}
    (hu : Avail (buildFrom cut bstock S rest ++ bstock) u) :
    Avail (buildFrom cut bstock S (r :: rest) ++ bstock) u := by
  obtain ⟨z, x, y⟩ := r
  unfold buildFrom; dsimp only
  split
  · exact avail_weaken (fun w hw => by simp only [List.mem_append] at hw ⊢; tauto) hu
  · exact hu
theorem buildFrom_covers {mask cut : Nat} {stock bstock : List Nat} {S : Finset Nat}
    (hstk : ∀ s ∈ stock, Avail bstock (canon cut s)) :
    ∀ {hist : List (Nat × Nat × Nat)}, HistValid mask stock hist →
      ∀ (acc : List Nat),
        (∀ u ∈ acc, Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u) →
        (∀ u ∈ recipeClose cut bstock hist acc, u ∈ S) →
        ∀ u ∈ acc, Avail (buildFrom cut bstock S hist ++ bstock) u
  | [], _, acc, hcov, _, u, hu => by
    rcases hcov u hu with ha | ⟨_, _, _, hm, _⟩
    · exact avail_weaken (fun w hw => List.mem_append_right _ hw) ha
    · exact nomatch hm
  | (z, x, y) :: rest, ⟨_, hxc, hyc, hrest⟩, acc, hcov, hS, u, hu => by
    cases hcz : acc.contains (canon cut z)
    · have hnz : canon cut z ∉ acc := fun hm => by rw [List.contains_iff_mem.mpr hm] at hcz; exact Bool.noConfusion hcz
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then _ else recipeClose cut bstock rest acc)
        simp only [hcz, Bool.false_eq_true, ite_false]; exact hv
      have hcov' : ∀ v ∈ acc, Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v := by
        intro v hv
        rcases hcov v hv with ha | ⟨z', x', y', hm, heq⟩
        · exact Or.inl ha
        · rcases List.mem_cons.mp hm with hhead | htail
          · rcases Prod.mk.inj hhead with ⟨rfl, _⟩
            exact absurd (heq ▸ hv) hnz
          · exact Or.inr ⟨z', x', y', htail, heq⟩
      exact buildFrom_mono_avail cut bstock S (z, x, y) rest
        (buildFrom_covers hstk hrest acc hcov' hS' u hu)
    · have hzacc : canon cut z ∈ acc := List.contains_iff_mem.mp hcz
      have hzS : canon cut z ∈ S := hS _ (recipeClose_sub _ hzacc)
      set acc1 := if availB bstock (canon cut x) then acc else addUniq (canon cut x) acc
      set acc2 := if availB bstock (canon cut y) then acc1 else addUniq (canon cut y) acc1
      have hS2 : ∀ v ∈ recipeClose cut bstock rest acc2, v ∈ S := by
        intro v hv; apply hS v
        change v ∈ (if acc.contains (canon cut z) then recipeClose cut bstock rest acc2 else _)
        simp only [hcz, ite_true]; exact hv
      let := Classical.propDecidable
      set acc' := acc2.filter (fun v => decide (Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v))
      have hsub' : ∀ v ∈ acc', v ∈ acc2 := fun v hv => (List.mem_filter.mp hv).1
      have hcov' : ∀ v ∈ acc', Avail bstock v ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = v :=
        fun v hv => of_decide_eq_true (List.mem_filter.mp hv).2
      have hS' : ∀ v ∈ recipeClose cut bstock rest acc', v ∈ S :=
        fun v hv => hS2 v (recipeClose_mono hsub' v hv)
      have hIH := buildFrom_covers hstk hrest acc' hcov' hS'
      have hacc_sub2 : ∀ v ∈ acc, v ∈ acc2 := by
        intro v hv
        have h1 : v ∈ acc1 := by
          unfold acc1; split; exact hv; exact addUniq_mem.mpr (Or.inr hv)
        unfold acc2; split; exact h1; exact addUniq_mem.mpr (Or.inr h1)
      have hax : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut x) := by
        cases hbx : availB bstock (canon cut x)
        · have hx2 : canon cut x ∈ acc2 := by
            have hx1 : canon cut x ∈ acc1 := by
              unfold acc1; simp only [hbx, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
            unfold acc2; split; exact hx1; exact addUniq_mem.mpr (Or.inr hx1)
          have hpx : Avail bstock (canon cut x) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut x := by
            rcases hxc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk x hs)
            · exact Or.inr ⟨x, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hx2, decide_eq_true hpx⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hbx)
      have hay : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut y) := by
        cases hby : availB bstock (canon cut y)
        · have hy2 : canon cut y ∈ acc2 := by
            unfold acc2; simp only [hby, Bool.false_eq_true, ite_false]; exact addUniq_mem.mpr (Or.inl rfl)
          have hpy : Avail bstock (canon cut y) ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = canon cut y := by
            rcases hyc with hs | ⟨a, b, hm⟩
            · exact Or.inl (hstk y hs)
            · exact Or.inr ⟨y, a, b, hm, rfl⟩
          exact hIH _ (List.mem_filter.mpr ⟨hy2, decide_eq_true hpy⟩)
        · exact avail_weaken (fun w hw => List.mem_append_right _ hw) (availB_spec.mp hby)
      by_cases huz : u = canon cut z
      · subst huz
        unfold buildFrom; dsimp only
        split
        · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
        · rename_i hneg
          by_cases ha : Avail (buildFrom cut bstock S rest ++ bstock) (canon cut z)
          · exact ha
          · exact absurd ⟨hzS, ha, hax, hay⟩ hneg
      · have hpu : Avail bstock u ∨ ∃ z' x' y', (z', x', y') ∈ rest ∧ canon cut z' = u := by
          rcases hcov u hu with ha | ⟨z', x', y', hm, heq⟩
          · exact Or.inl ha
          · rcases List.mem_cons.mp hm with hhead | htail
            · rcases Prod.mk.inj hhead with ⟨rfl, _⟩; exact absurd heq.symm huz
            · exact Or.inr ⟨z', x', y', htail, heq⟩
        exact buildFrom_mono_avail cut bstock S (z, x, y) rest
          (hIH u (List.mem_filter.mpr ⟨hacc_sub2 u hu, decide_eq_true hpu⟩))
def flatStartF (cut : Nat) (stock ws : List Nat) : Nat × List Nat :=
  List.rec (0, []) (fun w _ ih =>
    match ih with
    | (fl, acc) =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec
          (Bool.rec
            (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
            (fl, acc) (memN v stock))
          (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
          (Nat.beq v 0))) ws
theorem flatStartF_eq (cut : Nat) (stock ws : List Nat) :
    flatStartF cut stock ws = (flatCount cut ws, recipeStart cut stock ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have hstep : flatStartF cut stock (w :: ws) =
      match flatStartF cut stock ws with
      | (fl, acc) =>
        forceWP (canonV2 cut w) (fun v =>
          Bool.rec
            (Bool.rec
              (Bool.rec (fl, v :: acc) (fl, acc) (memN v acc))
              (fl, acc) (memN v stock))
            (forceWP (Nat.add fl 1) (fun fl1 => (fl1, acc)))
            (Nat.beq v 0)) := rfl
    rw [hstep, ih]; dsimp only; rw [forceWP_eq, canonV2_eq, forceWP_eq]
    change Bool.rec
        (Bool.rec
          (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
            (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) (recipeStart cut stock ws)))
          (flatCount cut ws, recipeStart cut stock ws) (memN (canon cut w) stock))
        (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) (Nat.beq (canon cut w) 0) =
      (bsel (Nat.beq (canon cut w) 0) (flatCount cut ws + 1) (flatCount cut ws),
       if availB stock (canon cut w) then recipeStart cut stock ws else addUniq (canon cut w) (recipeStart cut stock ws))
    simp only [memN_eq, availB, addUniq]
    have haux (b1 b2 b3 : Bool) :
        Bool.rec (Bool.rec (Bool.rec (flatCount cut ws, canon cut w :: recipeStart cut stock ws)
          (flatCount cut ws, recipeStart cut stock ws) b3)
          (flatCount cut ws, recipeStart cut stock ws) b2)
          (Nat.add (flatCount cut ws) 1, recipeStart cut stock ws) b1 =
        (bsel b1 (flatCount cut ws + 1) (flatCount cut ws),
         if (b1 || b2) = true then recipeStart cut stock ws
         else if b3 = true then recipeStart cut stock ws else canon cut w :: recipeStart cut stock ws) := by
      cases b1 <;> cases b2 <;> cases b3 <;> rfl
    exact haux _ _ _
def recipeCloseV2 (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun (w, a, b) _ next acc =>
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (next acc)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: acc) acc (memN va acc)) acc (memN va stock)) acc (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    next))))
          (memN v acc))) hist needed
theorem recipeCloseV2_eq (cut : Nat) (stock : List Nat) (hist : List (Nat × Nat × Nat)) (needed : List Nat) :
    recipeCloseV2 cut stock hist needed = recipeClose cut stock hist needed := by
  induction hist generalizing needed with
  | nil => rfl
  | cons rec hist ih =>
    obtain ⟨w, a, b⟩ := rec
    have hstep : recipeCloseV2 cut stock ((w, a, b) :: hist) needed =
      forceWP (canonV2 cut w) (fun v =>
        Bool.rec (recipeCloseV2 cut stock hist needed)
          (forceWP (canonV2 cut a) (fun va =>
            forceCons
              (Bool.rec (Bool.rec (Bool.rec (va :: needed) needed (memN va needed)) needed (memN va stock)) needed (Nat.beq va 0))
              (fun acc1 =>
                forceWP (canonV2 cut b) (fun vb =>
                  forceCons
                    (Bool.rec (Bool.rec (Bool.rec (vb :: acc1) acc1 (memN vb acc1)) acc1 (memN vb stock)) acc1 (Nat.beq vb 0))
                    (recipeCloseV2 cut stock hist)))))
          (memN v needed)) := rfl
    rw [hstep]
    simp only [forceWP_eq, forceCons_eq, canonV2_eq, memN_eq]
    change Bool.rec (recipeCloseV2 cut stock hist needed) _ (needed.contains (canon cut w)) =
      (if needed.contains (canon cut w) then
        let va := canon cut a; let vb := canon cut b
        let acc1 := if availB stock va then needed else addUniq va needed
        let acc2 := if availB stock vb then acc1 else addUniq vb acc1
        recipeClose cut stock hist acc2
      else recipeClose cut stock hist needed)
    cases needed.contains (canon cut w)
    · exact ih needed
    · dsimp only [ite_true]
      rw [ih]
      congr 1
      have hadd (v : Nat) (l : List Nat) :
          Bool.rec (Bool.rec (Bool.rec (v :: l) l (l.contains v)) l (stock.contains v)) l (Nat.beq v 0) =
          if availB stock v then l else addUniq v l := by
        dsimp only [availB, addUniq]
        have haux (b1 b2 b3 : Bool) :
            Bool.rec (Bool.rec (Bool.rec (v :: l) l b3) l b2) l b1 =
            if (b1 || b2) = true then l else if b3 = true then l else v :: l := by
          cases b1 <;> cases b2 <;> cases b3 <;> rfl
        exact haux _ _ _
      rw [hadd (canon cut a) needed, hadd (canon cut b)]
def boundClosesV2 (fuel : Nat) (ws : List Nat) (hist : List (Nat × Nat × Nat))
    (bound : Nat × List Nat × Nat × Nat) : Bool :=
  let (cut, bstock, lower, _) := bound
  match flatStartF cut bstock ws with
  | (fl, start0) =>
    forceWP (Nat.sub fuel fl) (fun rem =>
      Bool.rec false
        (match start0 with
         | [] => true
         | s0 :: sr =>
           forceList (s0 :: sr) (fun start =>
             Bool.rec false
               (Nat.blt (Nat.add (lenN (recipeCloseV2 cut bstock hist start)) rem) lower)
               (Nat.blt (Nat.add (lenN start) rem) lower)))
        (Nat.blt rem lower))
theorem boundClosesV2_sound {mask goal : Nat} {stock : List Nat}
    {fuel : Nat} {ws : List Nat} {hist : List (Nat × Nat × Nat)}
    {bound : Nat × List Nat × Nat × Nat}
    (hlow : LowerBin bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (sub : mask &&& bound.1 = bound.1)
    (hg : canon bound.1 goal = bound.2.2.2) (hnz : bound.2.2.2 ≠ 0)
    (hstk : ∀ s ∈ stock, Avail bound.2.1 (canon bound.1 s))
    (hv : HistValid mask stock hist) (hc : WsCovered stock hist ws)
    (nd : ws.Nodup) {k : Nat} (hk : k ≤ fuel)
    (hlive : LiveBin mask goal k ws.toFinset) :
    boundClosesV2 fuel ws hist bound = false := by
  obtain ⟨cut, bstock, lower, bgoal⟩ := bound
  dsimp only at hlow sub hg hnz hstk
  apply Bool.eq_false_iff.mpr
  intro hbc
  unfold boundClosesV2 at hbc; dsimp only at hbc
  rw [flatStartF_eq] at hbc; dsimp only at hbc
  simp only [forceWP_eq] at hbc
  cases h1 : Nat.blt (Nat.sub fuel (flatCount cut ws)) lower
  · rw [h1] at hbc; exact Bool.noConfusion hbc
  · rw [h1] at hbc; dsimp only at hbc
    have hlen_lt : (recipeClose cut bstock hist (recipeStart cut bstock ws)).length + (fuel - flatCount cut ws) < lower := by
      cases hs : recipeStart cut bstock ws with
      | nil =>
        rw [recipeClose_nil]; simp only [List.length_nil, Nat.zero_add]
        exact Nat.blt_eq.mp h1
      | cons s0 sr =>
        rw [hs] at hbc; dsimp only at hbc
        simp only [forceList_eq, recipeCloseV2_eq, lenN_eq] at hbc
        cases h2 : Nat.blt (Nat.add (s0 :: sr).length (Nat.sub fuel (flatCount cut ws))) lower
        · rw [h2] at hbc; exact Bool.noConfusion hbc
        · rw [h2] at hbc; dsimp only at hbc
          exact Nat.blt_eq.mp hbc
    set needed := recipeClose cut bstock hist (recipeStart cut bstock ws)
    set S := needed.toFinset
    set vs := buildFrom cut bstock S hist
    have hvbd : BuildsBin cut bstock vs := buildFrom_builds sub hv
    obtain ⟨hvnd, hvsub⟩ := buildFrom_nodup_sub cut bstock S hist
    have hvlen : vs.length ≤ needed.length := by
      rw [← List.toFinset_card_of_nodup hvnd]
      have hsubf : vs.toFinset ⊆ S := fun u hu => hvsub u (List.mem_toFinset.mp hu)
      exact Nat.le_trans (Finset.card_le_card hsubf) (List.toFinset_card_le needed)
    have hcov_start : ∀ u ∈ recipeStart cut bstock ws,
        Avail bstock u ∨ ∃ z x y, (z, x, y) ∈ hist ∧ canon cut z = u := by
      intro u hu
      obtain ⟨w, hww, rfl, hna⟩ := recipeStart_mem.mp hu
      rcases hc w hww with hws | ⟨a, b, hmem⟩
      · exact absurd (hstk w hws) hna
      · exact Or.inr ⟨w, a, b, hmem, rfl⟩
    have hvs_start := buildFrom_covers hstk hv (recipeStart cut bstock ws) hcov_start
      (fun u hu => List.mem_toFinset.mpr hu)
    have hsup : ∀ w ∈ ws.toFinset, Avail (vs ++ bstock) (canon cut w) := by
      intro w hw
      have hww : w ∈ ws := List.mem_toFinset.mp hw
      by_cases ha : Avail bstock (canon cut w)
      · exact avail_weaken (fun u hu => List.mem_append_right _ hu) ha
      · exact hvs_start _ (recipeStart_mem.mpr ⟨w, hww, rfl, ha⟩)
    have hgnf : canon cut goal ≠ 0 := hg.symm ▸ hnz
    obtain ⟨ys, hylen, hybd, hyhit⟩ := maskedBuildBin sub hgnf hlive (vs ++ bstock) hsup
    rw [← flatCount_card cut nd] at hylen
    have hboth := builds_append hvbd hybd
    have hfinal : Avail ((vs ++ ys) ++ bstock) bgoal := by
      rw [← hg]
      exact avail_weaken (fun u hu => by simp only [List.mem_append] at hu ⊢; tauto) hyhit
    have heno := hlow (vs ++ ys) hboth hfinal
    simp only [List.length_append] at heno
    omega
def edgeAxis (mask goal stride lm : Nat) : Nat :=
  let neg := Nat.xor mask goal
  Nat.land (Nat.lor (Nat.land (Nat.shiftRight goal stride) neg)
    (Nat.land goal (Nat.shiftRight neg stride))) lm
def edgePack (mask goal : Nat) : Nat :=
  Nat.lor (edgeAxis mask goal 1 0x5555555555555555)
    (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 2 0x3333333333333333) 64)
      (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f) 128)
        (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 8 0x00ff00ff00ff00ff) 192)
          (Nat.lor (Nat.shiftLeft (edgeAxis mask goal 16 0x0000ffff0000ffff) 256)
            (Nat.shiftLeft (edgeAxis mask goal 32 0x00000000ffffffff) 320)))))
def sepAxis (stride lm w : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.shiftRight w stride) w) lm
def sepPack (w : Nat) : Nat :=
  Nat.lor (sepAxis 1 0x5555555555555555 w)
    (Nat.lor (Nat.shiftLeft (sepAxis 2 0x3333333333333333 w) 64)
      (Nat.lor (Nat.shiftLeft (sepAxis 4 0x0f0f0f0f0f0f0f0f w) 128)
        (Nat.lor (Nat.shiftLeft (sepAxis 8 0x00ff00ff00ff00ff w) 192)
          (Nat.lor (Nat.shiftLeft (sepAxis 16 0x0000ffff0000ffff w) 256)
            (Nat.shiftLeft (sepAxis 32 0x00000000ffffffff w) 320)))))
def orSep (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ ih => Nat.lor (sepPack w) ih) ws
theorem edgeAxis_live {mask goal stride lm k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset)
    {n : Nat} (he : (edgeAxis mask goal stride lm).testBit n = true) :
    ∃ w ∈ ws, (sepAxis stride lm w).testBit n = true := by
  unfold edgeAxis at he
  change (((goal >>> stride &&& (mask ^^^ goal)) ||| (goal &&& ((mask ^^^ goal) >>> stride))) &&& lm).testBit n = true at he
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, Bool.and_eq_true, Bool.or_eq_true] at he
  obtain ⟨hcases, hlm⟩ := he
  have hpm : ∀ j, goal.testBit j = true → mask.testBit j = true := fun j hg => by
    have e := congrArg (fun x => x.testBit j) hgm
    simp only [Nat.testBit_and, hg, Bool.true_and] at e; exact e
  have hnm : ∀ j, (mask ^^^ goal).testBit j = true → mask.testBit j = true ∧ goal.testBit j = false := fun j hn => by
    rw [Nat.testBit_xor] at hn
    cases hm : mask.testBit j <;> cases hg : goal.testBit j <;> simp_all
  have hsep : ∃ w ∈ ws, w.testBit (stride + n) ≠ w.testBit n := by
    by_contra! hall
    rcases hcases with ⟨hg1, hn0⟩ | ⟨hg0, hn1⟩
    · have h1 := hpm (stride + n) hg1
      have h0 := hnm n hn0
      have eq := liveBin_agrees h1 h0.1 hlive (fun w hw => hall w (List.mem_toFinset.mp hw))
      rw [hg1, h0.2] at eq; exact Bool.noConfusion eq
    · have h0 := hpm n hg0
      have h1 := hnm (stride + n) hn1
      have eq := liveBin_agrees h0 h1.1 hlive (fun w hw => (hall w (List.mem_toFinset.mp hw)).symm)
      rw [hg0, h1.2] at eq; exact Bool.noConfusion eq
  obtain ⟨w, hw, hne⟩ := hsep
  refine ⟨w, hw, ?_⟩
  unfold sepAxis
  change (((w >>> stride) ^^^ w) &&& lm).testBit n = true
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, hlm, Bool.and_true]
  cases hb1 : w.testBit (stride + n) <;> cases hb2 : w.testBit n <;> simp_all
theorem orSep_testBit {ws : List Nat} {w j : Nat}
    (hw : w ∈ ws) (hb : (sepPack w).testBit j = true) : (orSep ws).testBit j = true := by
  induction ws with
  | nil => cases hw
  | cons x xs ih =>
    change (sepPack x ||| orSep xs).testBit j = true
    rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | htl
    · exact Or.inl hb
    · exact Or.inr (ih htl)
theorem sepPack_live {mask goal k : Nat} {ws : List Nat}
    (hgm : Masked mask goal) (hlive : LiveBin mask goal k ws.toFinset) :
    Nat.beq (Nat.land (edgePack mask goal) (orSep ws)) (edgePack mask goal) = true := by
  apply Nat.beq_eq.mpr
  apply Nat.eq_of_testBit_eq; intro j
  change ((edgePack mask goal) &&& (orSep ws)).testBit j = (edgePack mask goal).testBit j
  rw [Nat.testBit_and]
  cases he : (edgePack mask goal).testBit j
  · rfl
  · simp only [Bool.true_and]
    have hlane (stride lm shift : Nat)
        (hl : (edgeAxis mask goal stride lm <<< shift).testBit j = true)
        (hs : ∀ w, (sepAxis stride lm w <<< shift).testBit j = true → (sepPack w).testBit j = true) :
        (orSep ws).testBit j = true := by
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive hl.2
      apply orSep_testBit hw
      apply hs w
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hl.1, hsw⟩
    unfold edgePack at he
    change (edgeAxis mask goal 1 0x5555555555555555 |||
      ((edgeAxis mask goal 2 0x3333333333333333 <<< 64) |||
        ((edgeAxis mask goal 4 0x0f0f0f0f0f0f0f0f <<< 128) |||
          ((edgeAxis mask goal 8 0x00ff00ff00ff00ff <<< 192) |||
            ((edgeAxis mask goal 16 0x0000ffff0000ffff <<< 256) |||
              (edgeAxis mask goal 32 0x00000000ffffffff <<< 320)))))).testBit j = true at he
    simp only [Nat.testBit_or, Bool.or_eq_true] at he
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · obtain ⟨w, hw, hsw⟩ := edgeAxis_live hgm hlive h0
      exact orSep_testBit hw (by
        unfold sepPack
        change (sepAxis 1 0x5555555555555555 w ||| _).testBit j = true
        simp [Nat.testBit_or, hsw])
    · exact hlane 2 0x3333333333333333 64 h1 (fun w hw => by
        unfold sepPack
        change (_ ||| ((sepAxis 2 0x3333333333333333 w <<< 64) ||| _)).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 4 0x0f0f0f0f0f0f0f0f 128 h2 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| ((sepAxis 4 0x0f0f0f0f0f0f0f0f w <<< 128) ||| _))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 8 0x00ff00ff00ff00ff 192 h3 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| ((sepAxis 8 0x00ff00ff00ff00ff w <<< 192) ||| _)))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 16 0x0000ffff0000ffff 256 h4 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| ((sepAxis 16 0x0000ffff0000ffff w <<< 256) ||| _))))).testBit j = true
        simp [Nat.testBit_or, hw])
    · exact hlane 32 0x00000000ffffffff 320 h5 (fun w hw => by
        unfold sepPack
        change (_ ||| (_ ||| (_ ||| (_ ||| (_ ||| (sepAxis 32 0x00000000ffffffff w <<< 320)))))).testBit j = true
        simp [Nat.testBit_or, hw])
def mapSep (ws : List Nat) : List (Nat × Nat) :=
  List.rec [] (fun w _ ih => (w, sepPack w) :: ih) ws
def forceSepPairs : List Nat → (List (Nat × Nat) → Bool) → Bool
  | [], k => k []
  | w :: ws, k => forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest)))
theorem forceSepPairs_eq (ws : List Nat) (k : List (Nat × Nat) → Bool) :
    forceSepPairs ws k = k (mapSep ws) := by
  induction ws generalizing k with
  | nil => rfl
  | cons w ws ih =>
    change forceW (sepPack w) (fun sp => forceSepPairs ws (fun rest => k ((w, sp) :: rest))) = _
    rw [forceW_eq, ih]; rfl
def orSepAll (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Nat.lor p.2 ih) ps
def orSepSkip (x : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 x)) ps
def orSepSkip2 (x y : Nat) (ps : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun p _ ih => Bool.rec (Bool.rec (Nat.lor p.2 ih) ih (Nat.beq p.1 y)) ih (Nat.beq p.1 x)) ps
theorem orSepAll_mapSep (ws : List Nat) : orSepAll (mapSep ws) = orSep ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih => change Nat.lor (sepPack w) (orSepAll (mapSep ws)) = Nat.lor (sepPack w) (orSep ws); rw [ih]
theorem orSepSkip_mapSep (x : Nat) (ws : List Nat) :
    orSepSkip x (mapSep ws) = orSep (dropVal true x ws) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Nat.lor (sepPack w) (orSepSkip x (mapSep ws))) (orSepSkip x (mapSep ws)) (Nat.beq w x) =
      orSep (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws))
    rw [ih]
    cases Nat.beq w x <;> rfl
theorem dropVal_comm (x y : Nat) (l : List Nat) :
    dropVal true y (dropVal true x l) = dropVal true x (dropVal true y l) := by
  induction l with
  | nil => rfl
  | cons u us ih =>
    change dropVal true y (bsel (Nat.beq u x) (dropVal true x us) (u :: dropVal true x us)) =
      dropVal true x (bsel (Nat.beq u y) (dropVal true y us) (u :: dropVal true y us))
    cases hux : Nat.beq u x <;> cases huy : Nat.beq u y
    · simp only [bsel_false]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) =
        bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [huy, hux, bsel_false, bsel_false, ih]
    · simp only [bsel_false, bsel_true]
      change bsel (Nat.beq u y) (dropVal true y (dropVal true x us)) (u :: dropVal true y (dropVal true x us)) = _
      rw [huy, bsel_true, ih]
    · simp only [bsel_true, bsel_false]
      change _ = bsel (Nat.beq u x) (dropVal true x (dropVal true y us)) (u :: dropVal true x (dropVal true y us))
      rw [hux, bsel_true, ih]
    · simp only [bsel_true]; exact ih
theorem orSepSkip2_mapSep (x y : Nat) (ws : List Nat) :
    orSepSkip2 x y (mapSep ws) = orSep (dropVal true y (dropVal true x ws)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (Bool.rec (Nat.lor (sepPack w) (orSepSkip2 x y (mapSep ws))) (orSepSkip2 x y (mapSep ws)) (Nat.beq w y))
      (orSepSkip2 x y (mapSep ws)) (Nat.beq w x) =
      orSep (dropVal true y (bsel (Nat.beq w x) (dropVal true x ws) (w :: dropVal true x ws)))
    rw [ih]
    cases hx : Nat.beq w x
    · rw [bsel_false]
      change Bool.rec (Nat.lor (sepPack w) (orSep (dropVal true y (dropVal true x ws))))
        (orSep (dropVal true y (dropVal true x ws))) (Nat.beq w y) =
        orSep (bsel (Nat.beq w y) (dropVal true y (dropVal true x ws)) (w :: dropVal true y (dropVal true x ws)))
      cases Nat.beq w y <;> rfl
    · rw [bsel_true]
def treeBlockF (lo hi : Nat) (f : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ next a b =>
      Bool.rec true
        (let m := Nat.shiftRight (Nat.add a b) 1
         Bool.rec (Bool.rec false (next m b) (next a m)) (f a) (Nat.beq a m))
        (Nat.blt a b)) (Nat.add (Nat.sub hi lo) 1)) lo hi
theorem treeBlockF_eq (lo hi : Nat) (f : Nat → Bool) : treeBlockF lo hi f = treeBlock lo hi f := by
  unfold treeBlockF treeBlock
  suffices ∀ steps a b,
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          Bool.rec true
            (let m := Nat.shiftRight (Nat.add x y) 1
             Bool.rec (Bool.rec false (next m y) (next x m)) (f x) (Nat.beq x m))
            (Nat.blt x y)) steps) a b =
      (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
        (fun _ next x y =>
          if Nat.blt x y then
            let m := (x + y) / 2
            if Nat.beq x m then f x else next x m && next m y
          else true) steps) a b from
    this (hi - lo + 1) lo hi
  intro steps
  induction steps with
  | zero => intro a b; rfl
  | succ s ih =>
    intro a b
    dsimp only
    have hdiv : Nat.shiftRight (Nat.add a b) 1 = (a + b) / 2 := by
      change (a + b) >>> 1 = (a + b) / 2; rw [Nat.shiftRight_eq_div_pow]
    rw [hdiv]
    cases Nat.blt a b
    · rfl
    · cases Nat.beq a ((a + b) / 2)
      · rw [ih, ih]
        change Bool.rec false _ _ = (_ && _)
        cases (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true) _ s) a ((a + b) / 2) <;> rfl
      · rfl
theorem treeBlockF_at {lo hi : Nat} {f : Nat → Bool} (h : treeBlockF lo hi f = true) :
    ∀ {i : Nat}, lo ≤ i → i < hi → f i = true := by
  rw [treeBlockF_eq] at h; exact treeBlock_at h
def checkHintBoundV5 (goal negGoal fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (bounds : List (Nat × List Nat × Nat × Nat)) (cid : Nat) : Bool :=
  match nthBound bounds cid with
  | some b => boundClosesV2 fuel1 ws1 hist1 b
  | none => Bool.rec true false (dagPartF ws1 goal negGoal)
theorem checkHintBoundV5_open {mask goal fuel1 cid : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    checkHintBoundV5 goal (Nat.xor mask goal) fuel1 ws1 hist1 bounds cid = false := by
  unfold checkHintBoundV5
  cases hb : nthBound bounds cid with
  | some b =>
    dsimp only
    have hmem := nthBound_mem hb
    have hg := hgoals b hmem
    exact boundClosesV2_sound (hknown b hmem) (hsub b hmem) hg.1 hg.2 (hstk b hmem) hv hc nd hk hlive
  | none =>
    dsimp only
    have hdp : dagPartF ws1 goal (Nat.xor mask goal) = true := by
      have heq : dagPartF ws1 goal (Nat.xor mask goal) = dagPart ws1 goal (mask ^^^ goal) :=
        dagPartF_eq ws1 goal (mask ^^^ goal)
      rw [heq]; exact dagPart_live hgm hlive
    rw [hdp]
def hintCloseLeafV5 (goal negGoal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (fuel1 : Nat) (ws1 : List Nat) (hist1 : List (Nat × Nat × Nat))
    (sp : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec (some (cur, h))
    (forceWP (Nat.land h 3) (fun tag =>
      Bool.rec
        (Bool.rec none
          (forceWP (Nat.shiftRight h 2) (fun h' => some (cur, h')))
          (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds tag))
        (forceWP (Nat.shiftRight h 2) (fun h1 =>
          forceWP (Nat.add 3 (Nat.land h1 cutMask)) (fun cid =>
            Bool.rec none
              (forceWP (Nat.shiftRight h1 cutBits) (fun h' => some (cur, h')))
              (checkHintBoundV5 goal negGoal fuel1 ws1 hist1 bounds cid))))
        (Nat.beq tag 3)))
    (Nat.beq (Nat.land ep sp) ep)
theorem hintCloseLeafV5_open {mask goal cutBits cutMask fuel1 : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {ws1 : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)} {h : Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 ws1)
    (nd : ws1.Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k ws1.toFinset) :
    hintCloseLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask bounds fuel1 ws1 hist1 (orSep ws1) cur h = none := by
  unfold hintCloseLeafV5
  rw [sepPack_live hgm hlive]; dsimp only
  rw [forceWP_eq]
  cases Nat.beq (Nat.land h 3) 3
  · dsimp only
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
  · dsimp only
    rw [forceWP_eq, forceWP_eq]
    rw [checkHintBoundV5_open hgm hknown hsub hgoals hstk hv hc nd hk hlive]
def stepLeafV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel1 z spZ baseSp : Nat) (rest : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match cur with
  | (t, dest) :: tl =>
    Bool.rec
      (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) cur h)
      (Bool.rec none
        (match states dest with
         | none => none
         | some saved =>
           Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 (insertSortedF z rest)))
             (Nat.beq saved.1 fuel1))
        (Nat.blt dest count))
      (Nat.beq tok t)
  | [] =>
    hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel1 (z :: rest) hist1 (Nat.lor spZ baseSp) [] h
theorem stepLeafV5_ref {mask goal cutBits cutMask count fuel1 z tok h : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {rest : List Nat} {hist1 : List (Nat × Nat × Nat)} {cur : List (Nat × Nat)}
    {res : List (Nat × Nat) × Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (hv : HistValid mask stock hist1) (hc : WsCovered stock hist1 (z :: rest))
    (nd : (z :: rest).Nodup) {k : Nat} (hk : k ≤ fuel1)
    (hlive : LiveBin mask goal k (z :: rest).toFinset)
    (hok : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds states
      fuel1 z (sepPack z) (orSep rest) rest hist1 tok cur h = some res) :
    ∃ dest < count, ∃ saved, states dest = some saved ∧ saved.1 = fuel1 ∧ saved.2.1 = insertSorted z rest := by
  have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (cur := cur) (h := h)
    hgm hknown hsub hgoals hstk hv hc nd hk hlive
  unfold stepLeafV5 at hok
  have hor : Nat.lor (sepPack z) (orSep rest) = orSep (z :: rest) := rfl
  rw [hor] at hok
  cases cur with
  | nil => dsimp only at hok; rw [hcl] at hok; cases hok
  | cons hd tl =>
    obtain ⟨t, dest⟩ := hd
    dsimp only at hok
    cases ht : Nat.beq tok t
    · rw [ht] at hok; dsimp only at hok; rw [hcl] at hok; cases hok
    · rw [ht] at hok; dsimp only at hok
      cases hlt : Nat.blt dest count
      · rw [hlt] at hok; dsimp only at hok; cases hok
      · rw [hlt] at hok; dsimp only at hok
        cases hst : states dest with
        | none => rw [hst] at hok; dsimp only at hok; cases hok
        | some saved =>
          rw [hst] at hok; dsimp only at hok
          cases hf : Nat.beq saved.1 fuel1
          · rw [hf] at hok; dsimp only at hok; cases hok
          · rw [hf] at hok; dsimp only at hok
            cases heq : eqListN saved.2.1 (insertSortedF z rest)
            · rw [heq] at hok; dsimp only at hok; cases hok
            · rw [eqListN_eq, insertSortedF_eq, beq_iff_eq] at heq
              exact ⟨dest, Nat.blt_eq.mp hlt, saved, hst, Nat.beq_eq.mp hf, heq⟩
def checkKeepsV5 (goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n z spZ spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist1 : List (Nat × Nat × Nat))
    (tokBase : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match (Bool.rec
    (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => none
  | some (c1, h1) =>
    match (Bool.rec
      (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => none
    | some (c2, h2) =>
      match (Bool.rec
        (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => none
      | some (c3, h3) =>
        Bool.rec
          (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (Nat.add tokBase 3) c3 h3)
          (some (c3, h3)) (Nat.blt fuel (Nat.add n 1))
theorem checkKeepsV5_at {goal negGoal ep cutBits cutMask count fuel fuel1 n z spZ spAll spNoA spNoB spNoAB tokBase h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist1 : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hok : checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
      ws0 wsNoA wsNoB wsNoAB hist1 tokBase cur h = some res)
    (keepA keepB : Bool) :
    match keepA, keepB with
    | false, false => Nat.blt fuel (n - 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase c hh = some r
    | true, false => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (tokBase + 1) c hh = some r
    | false, true => Nat.blt fuel n = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (tokBase + 2) c hh = some r
    | true, true => Nat.blt fuel (n + 1) = true ∨ ∃ c hh r, stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spAll ws0 hist1 (tokBase + 3) c hh = some r := by
  unfold checkKeepsV5 at hok
  cases hp0 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoAB wsNoAB hist1 tokBase cur h)
    (some (cur, h)) (Nat.blt fuel (Nat.sub n 1)) : Option (List (Nat × Nat) × Nat)) with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1
    rw [hp0] at hok; dsimp only at hok
    cases hp1 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoB wsNoB hist1 (Nat.add tokBase 1) c1 h1)
      (some (c1, h1)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2
      rw [hp1] at hok; dsimp only at hok
      cases hp2 : (Bool.rec (stepLeafV5 goal negGoal ep cutBits cutMask count bounds states fuel1 z spZ spNoA wsNoA hist1 (Nat.add tokBase 2) c2 h2)
        (some (c2, h2)) (Nat.blt fuel n) : Option (List (Nat × Nat) × Nat)) with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3
        rw [hp2] at hok; dsimp only at hok
        cases keepA <;> cases keepB
        · cases hw : Nat.blt fuel (n - 1)
          · have hw' : Nat.blt fuel (Nat.sub n 1) = false := hw
            rw [hw'] at hp0; exact Or.inr ⟨cur, h, (c1, h1), hp0⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp2; exact Or.inr ⟨c2, h2, (c3, h3), hp2⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel n
          · rw [hw] at hp1; exact Or.inr ⟨c1, h1, (c2, h2), hp1⟩
          · exact Or.inl rfl
        · cases hw : Nat.blt fuel (n + 1)
          · have hw' : Nat.blt fuel (Nat.add n 1) = false := hw
            rw [hw'] at hok; exact Or.inr ⟨c3, h3, res, hok⟩
          · exact Or.inl rfl
def checkOpV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x y rawZ op : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  forceWP (canonV2 mask rawZ) (fun z =>
    Bool.rec
      (Bool.rec
        (forceWP (sepPack z) (fun spZ =>
          checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z spZ spAll spNoA spNoB spNoAB
            ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) cur h))
        (some (cur, h)) (memN z ws0))
      (some (cur, h)) (Nat.beq z 0))
def check4OpsV5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n x nx y : Nat) (spAll spNoA spNoB spNoAB : Nat)
    (ws0 wsNoA wsNoB wsNoAB : List Nat) (hist : List (Nat × Nat × Nat))
    (tokAB : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => none
  | some (c1, h1) =>
    match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => none
    | some (c2, h2) =>
      match checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => none
      | some (c3, h3) =>
        checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land nx y) 3 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c3 h3
theorem check4OpsV5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n x y spAll spNoA spNoB spNoAB tokAB op h : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA wsNoB wsNoAB : List Nat} {hist : List (Nat × Nat × Nat)}
    {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hop : op < 4)
    (hok : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x (Nat.xor mask x) y
      spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h = some res) :
    let z := binOp mask op x y
    z = 0 ∨ ws0.contains z = true ∨
      ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n z (sepPack z)
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB ((z, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op) 2) c hh = some r := by
  unfold check4OpsV5 at hok
  have extract (rawZ op' : Nat) (c0 : List (Nat × Nat)) (h0 : Nat) (r0 : List (Nat × Nat) × Nat)
      (hz : canon mask rawZ = binOp mask op' x y)
      (hrun : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y rawZ op'
        spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c0 h0 = some r0) :
      binOp mask op' x y = 0 ∨ ws0.contains (binOp mask op' x y) = true ∨
        ∃ c hh r, checkKeepsV5 goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n (binOp mask op' x y)
          (sepPack (binOp mask op' x y)) spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB
          ((binOp mask op' x y, x, y) :: hist) (Nat.shiftLeft (Nat.add tokAB op') 2) c hh = some r := by
    unfold checkOpV5 at hrun
    rw [forceWP_eq, canonV2_eq, hz] at hrun
    cases hz0 : Nat.beq (binOp mask op' x y) 0
    · rw [hz0] at hrun; dsimp only at hrun
      cases hm : memN (binOp mask op' x y) ws0
      · rw [hm] at hrun; dsimp only at hrun
        rw [forceWP_eq] at hrun
        exact Or.inr (Or.inr ⟨c0, h0, r0, hrun⟩)
      · rw [memN_eq] at hm; exact Or.inr (Or.inl hm)
    · exact Or.inl (Nat.beq_eq.mp hz0)
  cases hp0 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x y) 0 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
  | none => rw [hp0] at hok; dsimp only at hok; cases hok
  | some p1 =>
    obtain ⟨c1, h1⟩ := p1; rw [hp0] at hok; dsimp only at hok
    cases hp1 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.lor x y) 1 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c1 h1 with
    | none => rw [hp1] at hok; dsimp only at hok; cases hok
    | some p2 =>
      obtain ⟨c2, h2⟩ := p2; rw [hp1] at hok; dsimp only at hok
      cases hp2 : checkOpV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x y (Nat.land x (Nat.xor mask y)) 2 spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB c2 h2 with
      | none => rw [hp2] at hok; dsimp only at hok; cases hok
      | some p3 =>
        obtain ⟨c3, h3⟩ := p3; rw [hp2] at hok; dsimp only at hok
        rcases (by omega : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3) with rfl | rfl | rfl | rfl
        · exact extract _ 0 cur h (c1, h1) rfl hp0
        · exact extract _ 1 c1 h1 (c2, h2) rfl hp1
        · exact extract _ 2 c2 h2 (c3, h3) rfl hp2
        · exact extract _ 3 c3 h3 res rfl hok
def loopB_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n a x nx spAll spNoA : Nat) (ws0 wsNoA : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, b, cur, h =>
    forceWP (getDN ws0 b) (fun y =>
      forceList (dropValF true y ws0) (fun wsNoB =>
        forceList (dropValF true y wsNoA) (fun wsNoAB =>
          forceWP (orSepSkip y ps) (fun spNoB =>
            forceWP (orSepSkip2 x y ps) (fun spNoAB =>
              forceWP (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) (fun tokAB =>
                match check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA spNoB spNoAB ws0 wsNoA wsNoB wsNoAB hist tokAB cur h with
                | none => none
                | some (cur1, h1) =>
                  loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem (Nat.add b 1) cur1 h1))))))
theorem loopB_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n a x nx spAll spNoA : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 wsNoA : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem b0 b h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (hb1 : b0 ≤ b) (hb2 : b < b0 + rem)
    (hok : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist rem b0 cur h = some res) :
    let y := getDN ws0 b
    ∃ c hh r, check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx y spAll spNoA
      (orSepSkip y ps) (orSepSkip2 x y ps) ws0 wsNoA (dropValF true y ws0) (dropValF true y wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b) 2) c hh = some r := by
  induction rem generalizing b0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopB_V5 at hok
    rw [forceWP_eq, forceList_eq, forceList_eq, forceWP_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : check4OpsV5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n x nx (getDN ws0 b0) spAll spNoA
      (orSepSkip (getDN ws0 b0) ps) (orSepSkip2 x (getDN ws0 b0) ps) ws0 wsNoA
      (dropValF true (getDN ws0 b0) ws0) (dropValF true (getDN ws0 b0) wsNoA)
      hist (Nat.shiftLeft (Nat.add (Nat.shiftLeft a 4) b0) 2) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : b = b0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change b0 + 1 ≤ b; omega) (by change b < (b0 + 1) + r; omega) hok
def loopA_V5 (mask goal negGoal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (fuel fuel1 n spAll : Nat) (ws0 : List Nat) (ps : List (Nat × Nat)) (hist : List (Nat × Nat × Nat)) :
    Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, a, cur, h =>
    forceWP (getDN ws0 a) (fun x =>
      forceList (dropValF true x ws0) (fun wsNoA =>
        forceWP (Nat.xor mask x) (fun nx =>
          forceWP (orSepSkip x ps) (fun spNoA =>
            match loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x nx spAll spNoA ws0 wsNoA ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) cur h with
            | none => none
            | some (cur1, h1) =>
              loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem (Nat.add a 1) cur1 h1))))
theorem loopA_V5_at {mask goal negGoal ep cutBits cutMask count fuel fuel1 n spAll : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {ws0 : List Nat} {ps : List (Nat × Nat)} {hist : List (Nat × Nat × Nat)}
    {rem a0 a h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ha1 : a0 ≤ a) (ha2 : a < a0 + rem)
    (hok : loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist rem a0 cur h = some res) :
    let x := getDN ws0 a
    ∃ c hh r, loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a x (Nat.xor mask x) spAll
      (orSepSkip x ps) ws0 (dropValF true x ws0) ps hist (Nat.sub n (Nat.add a 1)) (Nat.add a 1) c hh = some r := by
  induction rem generalizing a0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopA_V5 at hok
    rw [forceWP_eq, forceList_eq, forceWP_eq, forceWP_eq] at hok
    cases hp : loopB_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n a0 (getDN ws0 a0) (Nat.xor mask (getDN ws0 a0)) spAll
      (orSepSkip (getDN ws0 a0) ps) ws0 (dropValF true (getDN ws0 a0) ws0) ps hist (Nat.sub n (Nat.add a0 1)) (Nat.add a0 1) cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : a = a0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change a0 + 1 ≤ a; omega) (by change a < (a0 + 1) + r; omega) hok
def dagCheckNodeV5 (mask goal ep cutBits cutMask : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (cursors : Nat → List (Nat × Nat)) (nodeHints : Nat → Nat) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, hist) =>
    forceWs ws (fun ws0 =>
      forceWP (lenN ws0) (fun n =>
        Bool.rec
          (Bool.rec
            (Bool.rec false
              (forceW (Nat.xor mask goal) (fun negGoal =>
                forceW (Nat.sub fuel 1) (fun fuel1 =>
                  forceSepPairs ws0 (fun ps =>
                    forceW (orSepAll ps) (fun spAll =>
                      forceW (nodeHints (Nat.add i 1)) (fun h0 =>
                        match loopA_V5 mask goal negGoal ep cutBits cutMask count bounds states fuel fuel1 n spAll ws0 ps hist n 0 (cursors (Nat.add i 1)) h0 with
                        | none => false
                        | some _ => true))))))
              (Nat.blt n 17))
            true (Nat.beq fuel 0))
          false (memN goal ws0)))
def stepRootV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (ws : List Nat) (tok : Nat) (cur : List (Nat × Nat)) (h : Nat) : Option (List (Nat × Nat) × Nat) :=
  Bool.rec
    (match cur with
     | (t, dest) :: tl =>
       Bool.rec
         (hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) cur h)
         (Bool.rec none
           (match states dest with
            | none => none
            | some saved =>
              Bool.rec none (Bool.rec none (some (tl, h)) (eqListN saved.2.1 ws)) (Nat.beq saved.1 fuel))
           (Nat.blt dest count))
         (Nat.beq tok t)
     | [] =>
       hintCloseLeafV5 goal negGoal ep cutBits cutMask bounds fuel ws [] (orSep ws) [] h)
    (some (cur, h)) (Nat.blt (Nat.add fuel 1) (lenN ws))
def loopRootsV5 (goal negGoal ep cutBits cutMask count fuel : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (stock : List Nat) : Nat → Nat → List (Nat × Nat) → Nat → Option (List (Nat × Nat) × Nat)
  | 0, _, c, h => some (c, h)
  | rem + 1, tok, cur, h =>
    forceList (subsetWordsF stock tok) (fun ws =>
      match stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states ws tok cur h with
      | none => none
      | some (cur1, h1) =>
        loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem (Nat.add tok 1) cur1 h1)
def dagCheckRootsV5 (mask goal ep cutBits cutMask count : Nat)
    (bounds : List (Nat × List Nat × Nat × Nat))
    (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (rootCur : List (Nat × Nat)) (rootHint : Nat) (stock : List Nat) (fuel : Nat) : Bool :=
  match loopRootsV5 goal (Nat.xor mask goal) ep cutBits cutMask count fuel bounds states stock (Nat.shiftLeft 1 (lenN stock)) 0 rootCur rootHint with
  | none => false
  | some _ => true
theorem loopRootsV5_at {goal negGoal ep cutBits cutMask count fuel : Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {stock : List Nat} {rem t0 tok h : Nat} {cur : List (Nat × Nat)} {res : List (Nat × Nat) × Nat}
    (ht1 : t0 ≤ tok) (ht2 : tok < t0 + rem)
    (hok : loopRootsV5 goal negGoal ep cutBits cutMask count fuel bounds states stock rem t0 cur h = some res) :
    ∃ c hh r, stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock tok) tok c hh = some r := by
  induction rem generalizing t0 cur h with
  | zero => omega
  | succ r ih =>
    unfold loopRootsV5 at hok
    rw [forceList_eq] at hok
    cases hp : stepRootV5 goal negGoal ep cutBits cutMask count fuel bounds states (subsetWordsF stock t0) t0 cur h with
    | none => rw [hp] at hok; dsimp only at hok; cases hok
    | some p1 =>
      obtain ⟨cur1, h1⟩ := p1; rw [hp] at hok; dsimp only at hok
      by_cases heq : tok = t0
      · subst heq; exact ⟨cur, h, (cur1, h1), hp⟩
      · exact ih (by change t0 + 1 ≤ tok; omega) (by change tok < (t0 + 1) + r; omega) hok
theorem dagAllNodesV5 {mask goal cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hgm : Masked mask goal) (hknown : KnownBin bounds)
    (hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0)
    (hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s))
    (snd : stock.Nodup)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal (edgePack mask goal) cutBits cutMask bounds count
      (dagTrace mask stock fuel forest) cursors nodeHints i = true) :
    ∀ cap i st, i < count → dagTrace mask stock fuel forest i = some st →
      st.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k st.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i st hi htr hcap k hk hlive
    obtain ⟨rem, ws, hist⟩ := st
    dsimp only at hcap hlive
    have nd : ws.Nodup := dagTrace_nodup snd htr
    obtain ⟨hv, hcov⟩ := dagTrace_valid htr
    dsimp only at hv hcov
    have hchk := hnodes i (Nat.zero_le i) hi
    unfold dagCheckNodeV5 at hchk
    rw [htr] at hchk; dsimp only at hchk
    rw [forceWs_eq, forceWP_eq, lenN_eq, memN_eq] at hchk
    generalize hS : ws.toFinset = S at hlive
    cases hlive with
    | done =>
      have hgm' : goal ∈ ws := List.mem_toFinset.mp (hS.symm ▸ Finset.mem_singleton_self goal)
      have hc : ws.contains goal = true := List.contains_iff_mem.mpr hgm'
      rw [hc] at hchk; exact Bool.noConfusion hchk
    | @step k' _ a0 b0 op0 ha0 hb0 hab0 _ _ hop0 hz0 hf0 keepA0 keepB0 tail0 =>
      rw [← hS] at ha0 hb0 hf0 tail0
      have hrem_pos : rem ≠ 0 := by omega
      cases hcg : ws.contains goal
      · rw [hcg] at hchk; dsimp only at hchk
        have hrem0 : Nat.beq rem 0 = false := beq_false_ne hrem_pos
        rw [hrem0] at hchk; dsimp only at hchk
        cases h17 : Nat.blt ws.length 17
        · rw [h17] at hchk; exact Bool.noConfusion hchk
        · rw [h17] at hchk; dsimp only at hchk
          rw [forceW_eq, forceW_eq, forceSepPairs_eq, forceW_eq, forceW_eq] at hchk
          cases hloop : loopA_V5 mask goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
              (dagTrace mask stock fuel forest) rem (Nat.sub rem 1) ws.length (orSepAll (mapSep ws)) ws (mapSep ws) hist
              ws.length 0 (cursors (Nat.add i 1)) (nodeHints (Nat.add i 1)) with
          | none => rw [hloop] at hchk; exact Bool.noConfusion hchk
          | some resA =>
            have haM : a0 ∈ ws := List.mem_toFinset.mp ha0
            have hbM : b0 ∈ ws := List.mem_toFinset.mp hb0
            obtain ⟨ia0, hia0, hea0⟩ := getElem_index_lt haM
            obtain ⟨ib0, hib0, heb0⟩ := getElem_index_lt hbM
            have hiab_ne : ia0 ≠ ib0 := fun heq => hab0 (hea0.symm.trans (heq ▸ heb0))
            have ⟨a, b, op, keepA, keepB, ha_lt, hab_lt, hb_lt, hop_lt, hax, hby, hzeq, htail⟩ :
                ∃ a b op keepA keepB, a < ws.length ∧ a < b ∧ b < ws.length ∧ op < 4 ∧
                  ws.getD a 0 = (if ia0 < ib0 then a0 else b0) ∧
                  ws.getD b 0 = (if ia0 < ib0 then b0 else a0) ∧
                  binOp mask op (ws.getD a 0) (ws.getD b 0) = binOp mask op0 a0 b0 ∧
                  LiveBin mask goal k' (insert (binOp mask op (ws.getD a 0) (ws.getD b 0))
                    (dropIf (!keepA) (ws.getD a 0) (dropIf (!keepB) (ws.getD b 0) ws.toFinset))) := by
              by_cases hlt : ia0 < ib0
              · exact ⟨ia0, ib0, op0, keepA0, keepB0, hia0, hlt, hib0, hop0,
                  by simp only [hlt, ite_true]; exact hea0,
                  by simp only [hlt, ite_true]; exact heb0,
                  by rw [hea0, heb0], by rw [hea0, heb0]; exact tail0⟩
              · obtain ⟨op1, hop1, hopEq⟩ := binOp_comm mask op0 a0 b0 hop0
                have hswap : dropIf (!keepB0) b0 (dropIf (!keepA0) a0 ws.toFinset) =
                    dropIf (!keepA0) a0 (dropIf (!keepB0) b0 ws.toFinset) := by
                  ext w; simp only [dropIf]; cases keepA0 <;> cases keepB0 <;> simp [Finset.mem_erase, and_left_comm]
                exact ⟨ib0, ia0, op1, keepB0, keepA0, hib0, by omega, hia0, hop1,
                  by simp only [hlt, ite_false]; exact heb0,
                  by simp only [hlt, ite_false]; exact hea0,
                  by rw [hea0, heb0, hopEq],
                  by rw [hea0, heb0, ← hopEq, hswap]; exact tail0⟩
            obtain ⟨cA, hA, rA, hB⟩ := loopA_V5_at (a := a) (Nat.zero_le a) (by omega) hloop
            obtain ⟨cB, hB', rB, hO⟩ := loopB_V5_at (b := b) (by change a + 1 ≤ b; omega) (by change b < (a + 1) + (ws.length - (a + 1)); omega) hB
            simp only [getDN_eq, dropValF_eq, orSepAll_mapSep, orSepSkip_mapSep, orSepSkip2_mapSep] at hO
            set x := ws.getD a 0
            set y := ws.getD b 0
            set z := binOp mask op x y
            have hznz : z ≠ 0 := hzeq.symm ▸ hz0
            have hznm : ws.contains z = false := by
              cases h : ws.contains z
              · rfl
              · exact absurd (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)) (hzeq.symm ▸ hf0)
            rcases check4OpsV5_at hop_lt hO with hz' | hcm | ⟨cK, hK', rK, hK⟩
            · exact hznz hz'
            · rw [hznm] at hcm; exact Bool.noConfusion hcm
            · have hxM : x ∈ ws := by simp only [x, hax]; split; exact haM; exact hbM
              have hyM : y ∈ ws := by simp only [y, hby]; split; exact hbM; exact haM
              have hxy : x ≠ y := by simp only [x, y, hax, hby]; split; exact hab0; exact hab0.symm
              have hzNotW : z ∉ ws := fun hm => by
                have := List.contains_iff_mem.mpr hm; rw [hznm] at this; exact Bool.noConfusion this
              have hdropComm : dropVal true y (dropVal true x ws) = dropVal true x (dropVal true y ws) :=
                dropVal_comm x y ws
              set rest := dropVal (!keepA) x (dropVal (!keepB) y ws)
              have hv' : HistValid mask stock ((z, x, y) :: hist) :=
                ⟨⟨op, hop_lt, rfl⟩, hcov x hxM, hcov y hyM, hv⟩
              have hcov' : WsCovered stock ((z, x, y) :: hist) (z :: rest) := by
                intro w hw
                rcases List.mem_cons.mp hw with rfl | hw'
                · exact Or.inr ⟨x, y, List.mem_cons_self⟩
                · have hwm : w ∈ ws := (dropVal_mem.mp (dropVal_mem.mp hw').1).1
                  rcases hcov w hwm with hst | ⟨u, v, hm⟩
                  · exact Or.inl hst
                  · exact Or.inr ⟨u, v, List.mem_cons_of_mem _ hm⟩
              have hnd_u : (z :: rest).Nodup :=
                List.nodup_cons.mpr ⟨fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1,
                  dropVal_nodup (dropVal_nodup nd)⟩
              have hset_u : (z :: rest).toFinset = insert z (dropIf (!keepA) x (dropIf (!keepB) y ws.toFinset)) := by
                ext w; simp only [rest, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, ← dropVal_toFinset]
              have hlive_u : LiveBin mask goal k' (z :: rest).toFinset := by rwa [hset_u]
              have hset_s : (insertSorted z rest).toFinset = (z :: rest).toFinset := by
                ext w; simp only [List.mem_toFinset, insertSorted_mem, List.mem_cons]
              have hlive_s : LiveBin mask goal k' (insertSorted z rest).toFinset := by rwa [hset_s]
              have hlen' : (insertSorted z rest).length =
                  ws.length - 1 + (if keepA then 1 else 0) + (if keepB then 1 else 0) :=
                list_len_child (z := z) (keepA := keepA) (keepB := keepB) nd hxM hyM hxy hzNotW
              have hcard' : (insertSorted z rest).length ≤ rem := by
                have hnd_s : (insertSorted z rest).Nodup :=
                  insertSorted_nodup (fun hm => hzNotW (dropVal_mem.mp (dropVal_mem.mp hm).1).1) (dropVal_nodup (dropVal_nodup nd))
                have := liveBin_card_le hlive_s
                rw [List.toFinset_card_of_nodup hnd_s] at this; omega
              have h2len : 2 ≤ ws.length := by
                have hsub2 : ({x, y} : Finset Nat) ⊆ ws.toFinset := by
                  intro w hw; rcases Finset.mem_insert.mp hw with rfl | hw
                  · exact List.mem_toFinset.mpr hxM
                  · rw [Finset.mem_singleton.mp hw]; exact List.mem_toFinset.mpr hyM
                have hpair : ({x, y} : Finset Nat).card = 2 := Finset.card_pair hxy
                have hc := Finset.card_le_card hsub2
                rw [List.toFinset_card_of_nodup nd] at hc; omega
              have hka := checkKeepsV5_at hK keepA keepB
              have finish {tok' hh' : Nat} {c' : List (Nat × Nat)} {rr : List (Nat × Nat) × Nat}
                  (hstep : stepLeafV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count bounds
                    (dagTrace mask stock fuel forest) (Nat.sub rem 1) z (sepPack z) (orSep rest) rest ((z, x, y) :: hist) tok' c' hh' = some rr) : False := by
                obtain ⟨dest, hdest, saved, htr2, hfEq, hwEq⟩ :=
                  stepLeafV5_ref hgm hknown hsub hgoals hstk hv' hcov' hnd_u (k := k') (by change k' ≤ rem - 1; omega) hlive_u hstep
                exact ih (rem - 1) (by omega) dest saved hdest htr2 hfEq k' (by omega) (hwEq ▸ hlive_s)
              cases keepA <;> cases keepB
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false] at hlen'; omega
                · rw [hdropComm] at hst; exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [Bool.false_eq_true, ite_false, ite_true] at hlen'; omega
                · exact finish hst
              · rcases hka with hwide | ⟨c', hh', rr, hst⟩
                · have := Nat.blt_eq.mp hwide; simp only [ite_true] at hlen'; omega
                · exact finish hst
      · rw [hcg] at hchk; exact Bool.noConfusion hchk
def nodupB : List Nat → Bool
  | [] => true
  | w :: ws => !memN w ws && nodupB ws
theorem nodupB_spec {l : List Nat} (h : nodupB l = true) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons w ws ih =>
    unfold nodupB at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', memN_eq] at h
    exact List.nodup_cons.mpr ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1, ih h.2⟩
theorem kn_nil : KnownBin [] := fun _ h => nomatch h
theorem kn_cons {m : Nat} {s : List Nat} {l g : Nat} {bs : List (Nat × List Nat × Nat × Nat)}
    (h : LowerBin m s g l) (hs : KnownBin bs) : KnownBin ((m, s, l, g) :: bs) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact h
  · exact hs b hb
def checkSliceMetaV5 (mask goal ep : Nat) (stock : List Nat)
    (bounds : List (Nat × List Nat × Nat × Nat)) : Bool :=
  Nat.beq (Nat.land goal mask) goal &&
  !Nat.beq goal 0 &&
  stock.all (fun w => Nat.beq (canon mask w) w) &&
  nodupB stock &&
  Nat.beq ep (edgePack mask goal) &&
  bounds.all (fun b =>
    Nat.beq (Nat.land mask b.1) b.1 &&
    Nat.beq (canon b.1 goal) b.2.2.2 &&
    !Nat.beq b.2.2.2 0 &&
    stock.all (fun s => availB b.2.1 (canon b.1 s)))
theorem lowerDagV5 {mask goal ep cutBits cutMask fuel count : Nat} {stock : List Nat}
    {bounds : List (Nat × List Nat × Nat × Nat)}
    {forest : Nat → Nat × Nat} {cursors : Nat → List (Nat × Nat)} {nodeHints : Nat → Nat}
    (hknown : KnownBin bounds)
    (hroots : dagCheckRootsV5 mask goal ep cutBits cutMask count bounds
      (dagTraceF mask stock fuel forest) (cursors 0) (nodeHints 0) stock fuel = true)
    (hnodes : ∀ i, 0 ≤ i → i < count → dagCheckNodeV5 mask goal ep cutBits cutMask bounds count
      (dagTraceF mask stock fuel forest) cursors nodeHints i = true)
    (hmeta : checkSliceMetaV5 mask goal ep stock bounds = true) :
    LowerBin mask stock goal (fuel + 1) := by
  unfold checkSliceMetaV5 at hmeta
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hmeta
  obtain ⟨⟨⟨⟨⟨hgmB, hgnzB⟩, hcs⟩, hndB⟩, hepB⟩, hbdB⟩ := hmeta
  have hgm : Masked mask goal := Nat.beq_eq.mp hgmB
  have hgnz : goal ≠ 0 := fun h => by rw [h] at hgnzB; exact Bool.noConfusion hgnzB
  have snd : stock.Nodup := nodupB_spec hndB
  have hep : ep = edgePack mask goal := Nat.beq_eq.mp hepB
  have hsub : ∀ b ∈ bounds, mask &&& b.1 = b.1 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact Nat.beq_eq.mp h.1.1.1
  have hgoals : ∀ b ∈ bounds, canon b.1 goal = b.2.2.2 ∧ b.2.2.2 ≠ 0 := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    exact ⟨Nat.beq_eq.mp h.1.1.2, fun h0 => by rw [h0] at h; exact Bool.noConfusion h.1.2⟩
  have hstkB : ∀ b ∈ bounds, stock.all (fun s => availB b.2.1 (canon b.1 s)) = true := fun b hb => by
    have h := List.all_eq_true.mp hbdB b hb
    simp only [Bool.and_eq_true] at h
    exact h.2
  subst hep
  have hstk : ∀ b ∈ bounds, ∀ s ∈ stock, Avail b.2.1 (canon b.1 s) := fun b hb s hs =>
    availB_spec.mp (List.all_eq_true.mp (hstkB b hb) s hs)
  have htr : dagTraceF mask stock fuel forest = dagTrace mask stock fuel forest := by
    funext i; exact dagTraceF_eq mask stock fuel forest i
  rw [htr] at hroots hnodes
  intro vs hbuild hhit
  by_contra! hlt
  have hcs' : ∀ w ∈ stock, canon mask w = w := fun w hw =>
    Nat.beq_eq.mp (List.all_eq_true.mp hcs w hw)
  obtain ⟨k, S, hk, hSsub, hlive⟩ := extractLiveBin hgnz hcs' hbuild hhit
  obtain ⟨tok, htok, hteq⟩ := exists_subsetToken stock S
  rw [Finset.inter_eq_left.mpr hSsub] at hteq
  unfold dagCheckRootsV5 at hroots
  have hpow : Nat.shiftLeft 1 (lenN stock) = 2 ^ stock.length := by
    rw [lenN_eq]; change 1 <<< stock.length = _; rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hpow] at hroots
  cases hrl : loopRootsV5 goal (Nat.xor mask goal) (edgePack mask goal) cutBits cutMask count fuel bounds
      (dagTrace mask stock fuel forest) stock (2 ^ stock.length) 0 (cursors 0) (nodeHints 0) with
  | none => rw [hrl] at hroots; exact Bool.noConfusion hroots
  | some resR =>
    obtain ⟨c, hh, rr, hsr⟩ := loopRootsV5_at (tok := tok) (Nat.zero_le tok) (by omega) hrl
    rw [subsetWordsF_eq] at hsr
    have hnd : (subsetWords stock tok).Nodup := subsetWords_nodup snd tok
    have hlive' : LiveBin mask goal k (subsetWords stock tok).toFinset := by rwa [hteq]
    have hcard : (subsetWords stock tok).length ≤ fuel + 1 := by
      have := liveBin_card_le hlive'
      rw [List.toFinset_card_of_nodup hnd] at this; omega
    have hnw : Nat.blt (Nat.add fuel 1) (lenN (subsetWords stock tok)) = false := by
      rw [lenN_eq]
      cases h : Nat.blt (Nat.add fuel 1) (subsetWords stock tok).length
      · rfl
      · have hlt' : fuel + 1 < (subsetWords stock tok).length := Nat.blt_eq.mp h
        omega
    have hcov0 : WsCovered stock [] (subsetWords stock tok) :=
      fun w hw => Or.inl (subsetWords_subset stock tok w hw)
    have hcl := hintCloseLeafV5_open (cutBits := cutBits) (cutMask := cutMask) (fuel1 := fuel) (hist1 := []) (cur := c) (h := hh)
      hgm hknown hsub hgoals hstk trivial hcov0 hnd (k := k) (by omega) hlive'
    unfold stepRootV5 at hsr
    rw [hnw] at hsr; dsimp only at hsr
    cases c with
    | nil => dsimp only at hsr; rw [hcl] at hsr; cases hsr
    | cons hd tl =>
      obtain ⟨t, dest⟩ := hd
      dsimp only at hsr
      cases ht : Nat.beq tok t
      · rw [ht] at hsr; dsimp only at hsr; rw [hcl] at hsr; cases hsr
      · rw [ht] at hsr; dsimp only at hsr
        cases hltc : Nat.blt dest count
        · rw [hltc] at hsr; dsimp only at hsr; cases hsr
        · rw [hltc] at hsr; dsimp only at hsr
          cases htr2 : dagTrace mask stock fuel forest dest with
          | none => rw [htr2] at hsr; dsimp only at hsr; cases hsr
          | some saved =>
            rw [htr2] at hsr; dsimp only at hsr
            cases hf : Nat.beq saved.1 fuel
            · rw [hf] at hsr; dsimp only at hsr; cases hsr
            · rw [hf] at hsr; dsimp only at hsr
              cases heq : eqListN saved.2.1 (subsetWords stock tok)
              · rw [heq] at hsr; dsimp only at hsr; cases hsr
              · rw [eqListN_eq, beq_iff_eq] at heq
                exact dagAllNodesV5 hgm hknown hsub hgoals hstk snd hnodes fuel dest saved
                  (Nat.blt_eq.mp hltc) htr2 (Nat.beq_eq.mp hf) k (by omega) (heq ▸ hlive')
def unpackF (data width idx : Nat) : Nat :=
  Nat.land (Nat.shiftRight data (Nat.mul idx width)) (Nat.sub (Nat.shiftLeft 1 width) 1)
def unpackForestF (data pBits tBits : Nat) : Nat → Nat × Nat := fun i =>
  let w := Nat.add pBits tBits
  let code := unpackF data w i
  (Nat.shiftRight code tBits, Nat.land code (Nat.sub (Nat.shiftLeft 1 tBits) 1))
def unpackListAux (data off w wMask tokBits tokMask : Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, acc => acc
  | k + 1, acc =>
    forceWP (Nat.land (Nat.shiftRight data (Nat.mul (Nat.add off k) w)) wMask) (fun code =>
      unpackListAux data off w wMask tokBits tokMask k ((Nat.land code tokMask, Nat.shiftRight code tokBits) :: acc))
def unpackCursorV5 (index data idxW idxMask sizeBits sizeMask tokBits tokMask w wMask : Nat) :
    Nat → List (Nat × Nat) :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      unpackListAux data (Nat.shiftRight entry sizeBits) w wMask tokBits tokMask (Nat.land entry sizeMask) [])
def unpackHintV5 (index data idxW idxMask lenBits lenMask : Nat) : Nat → Nat :=
  fun parent =>
    forceWP (Nat.land (Nat.shiftRight index (Nat.mul parent idxW)) idxMask) (fun entry =>
      forceWP (Nat.land entry lenMask) (fun hlen =>
        Bool.rec
          (Nat.land (Nat.shiftRight data (Nat.shiftRight entry lenBits)) (Nat.sub (Nat.shiftLeft 1 hlen) 1))
          0 (Nat.beq hlen 0)))

def m_0 : Nat := 0xf0f000000000000
def s_0 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_0 : Nat := 0x107000000000000
def ep_0 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
def bds_0 : List (Nat × List Nat × Nat × Nat) := []
def cur_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_0 : Nat → Nat := fun _ => 0
def f_0 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_0 : Nat → Bool := dagCheckNodeV5 m_0 g_0 ep_0 1 1 bds_0 1 (dagTraceF m_0 s_0 3 f_0) cur_0 nh_0
set_option maxHeartbeats 0 in
theorem rc_0 : dagCheckRootsV5 m_0 g_0 ep_0 1 1 1 bds_0 (dagTraceF m_0 s_0 3 f_0) (cur_0 0) (nh_0 0) s_0 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_0 : treeBlockF 0 1 ch_0 = true := by decide +kernel
theorem nc_0 : ∀ i, 0 ≤ i → i < 1 → ch_0 i = true := fun _ h1 h2 => treeBlockF_at nb_0 h1 h2
theorem lb_0 : LowerBin m_0 s_0 g_0 4 :=
  lowerDagV5 (kn_nil) rc_0 nc_0 (by decide +kernel)

def m_1 : Nat := 0xcc00cc00000000
def s_1 : List Nat := [0x44004400000000, 0xc000c00000000, 0xcc00000000]
def g_1 : Nat := 0x4004c00000000
def ep_1 : Nat := 0x48000000000000000000000000000400080000000000000000000000000004004000000000
def bds_1 : List (Nat × List Nat × Nat × Nat) := []
def cur_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_1 : Nat → Nat := fun _ => 0
def f_1 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_1 : Nat → Bool := dagCheckNodeV5 m_1 g_1 ep_1 1 1 bds_1 1 (dagTraceF m_1 s_1 3 f_1) cur_1 nh_1
set_option maxHeartbeats 0 in
theorem rc_1 : dagCheckRootsV5 m_1 g_1 ep_1 1 1 1 bds_1 (dagTraceF m_1 s_1 3 f_1) (cur_1 0) (nh_1 0) s_1 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_1 : treeBlockF 0 1 ch_1 = true := by decide +kernel
theorem nc_1 : ∀ i, 0 ≤ i → i < 1 → ch_1 i = true := fun _ h1 h2 => treeBlockF_at nb_1 h1 h2
theorem lb_1 : LowerBin m_1 s_1 g_1 4 :=
  lowerDagV5 (kn_nil) rc_1 nc_1 (by decide +kernel)

def m_2 : Nat := 0x3030303000000000
def s_2 : List Nat := [0x1010101000000000, 0x30003000000000, 0x303000000000]
def g_2 : Nat := 0x10103000000000
def ep_2 : Nat := 0x1020000000000010002000000000000000000000000000000000000000000010100000000000
def bds_2 : List (Nat × List Nat × Nat × Nat) := []
def cur_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_2 : Nat → Nat := fun _ => 0
def f_2 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_2 : Nat → Bool := dagCheckNodeV5 m_2 g_2 ep_2 1 1 bds_2 1 (dagTraceF m_2 s_2 3 f_2) cur_2 nh_2
set_option maxHeartbeats 0 in
theorem rc_2 : dagCheckRootsV5 m_2 g_2 ep_2 1 1 1 bds_2 (dagTraceF m_2 s_2 3 f_2) (cur_2 0) (nh_2 0) s_2 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_2 : treeBlockF 0 1 ch_2 = true := by decide +kernel
theorem nc_2 : ∀ i, 0 ≤ i → i < 1 → ch_2 i = true := fun _ h1 h2 => treeBlockF_at nb_2 h1 h2
theorem lb_2 : LowerBin m_2 s_2 g_2 4 :=
  lowerDagV5 (kn_nil) rc_2 nc_2 (by decide +kernel)

def m_3 : Nat := 0xaa00aa00000000
def s_3 : List Nat := [0x22002200000000, 0xa000a00000000, 0xaa00000000]
def g_3 : Nat := 0x2002a00000000
def ep_3 : Nat := 0x28000000000000000000000000000200080000000000020020000000000000000000000000
def bds_3 : List (Nat × List Nat × Nat × Nat) := []
def cur_3 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_3 : Nat → Nat := fun _ => 0
def f_3 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_3 : Nat → Bool := dagCheckNodeV5 m_3 g_3 ep_3 1 1 bds_3 1 (dagTraceF m_3 s_3 3 f_3) cur_3 nh_3
set_option maxHeartbeats 0 in
theorem rc_3 : dagCheckRootsV5 m_3 g_3 ep_3 1 1 1 bds_3 (dagTraceF m_3 s_3 3 f_3) (cur_3 0) (nh_3 0) s_3 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_3 : treeBlockF 0 1 ch_3 = true := by decide +kernel
theorem nc_3 : ∀ i, 0 ≤ i → i < 1 → ch_3 i = true := fun _ h1 h2 => treeBlockF_at nb_3 h1 h2
theorem lb_3 : LowerBin m_3 s_3 g_3 4 :=
  lowerDagV5 (kn_nil) rc_3 nc_3 (by decide +kernel)

def m_4 : Nat := 0x5050505000000000
def s_4 : List Nat := [0x1010101000000000, 0x50005000000000, 0x505000000000]
def g_4 : Nat := 0x10105000000000
def ep_4 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000000000000000000
def bds_4 : List (Nat × List Nat × Nat × Nat) := []
def cur_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_4 : Nat → Nat := fun _ => 0
def f_4 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_4 : Nat → Bool := dagCheckNodeV5 m_4 g_4 ep_4 1 1 bds_4 1 (dagTraceF m_4 s_4 3 f_4) cur_4 nh_4
set_option maxHeartbeats 0 in
theorem rc_4 : dagCheckRootsV5 m_4 g_4 ep_4 1 1 1 bds_4 (dagTraceF m_4 s_4 3 f_4) (cur_4 0) (nh_4 0) s_4 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_4 : treeBlockF 0 1 ch_4 = true := by decide +kernel
theorem nc_4 : ∀ i, 0 ≤ i → i < 1 → ch_4 i = true := fun _ h1 h2 => treeBlockF_at nb_4 h1 h2
theorem lb_4 : LowerBin m_4 s_4 g_4 4 :=
  lowerDagV5 (kn_nil) rc_4 nc_4 (by decide +kernel)

def m_5 : Nat := 0xf000f000000000
def s_5 : List Nat := [0x50005000000000, 0x30003000000000, 0xf000000000]
def g_5 : Nat := 0x10007000000000
def ep_5 : Nat := 0x60000000000000000000000000000000000000000000100020000000000010004000000000
def bds_5 : List (Nat × List Nat × Nat × Nat) := []
def cur_5 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_5 : Nat → Nat := fun _ => 0
def f_5 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_5 : Nat → Bool := dagCheckNodeV5 m_5 g_5 ep_5 1 1 bds_5 1 (dagTraceF m_5 s_5 3 f_5) cur_5 nh_5
set_option maxHeartbeats 0 in
theorem rc_5 : dagCheckRootsV5 m_5 g_5 ep_5 1 1 1 bds_5 (dagTraceF m_5 s_5 3 f_5) (cur_5 0) (nh_5 0) s_5 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_5 : treeBlockF 0 1 ch_5 = true := by decide +kernel
theorem nc_5 : ∀ i, 0 ≤ i → i < 1 → ch_5 i = true := fun _ h1 h2 => treeBlockF_at nb_5 h1 h2
theorem lb_5 : LowerBin m_5 s_5 g_5 4 :=
  lowerDagV5 (kn_nil) rc_5 nc_5 (by decide +kernel)

def m_6 : Nat := 0x5500550000000000
def s_6 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_6 : Nat := 0x100150000000000
def ep_6 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
def bds_6 : List (Nat × List Nat × Nat × Nat) := []
def cur_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_6 : Nat → Nat := fun _ => 0
def f_6 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_6 : Nat → Bool := dagCheckNodeV5 m_6 g_6 ep_6 1 1 bds_6 1 (dagTraceF m_6 s_6 3 f_6) cur_6 nh_6
set_option maxHeartbeats 0 in
theorem rc_6 : dagCheckRootsV5 m_6 g_6 ep_6 1 1 1 bds_6 (dagTraceF m_6 s_6 3 f_6) (cur_6 0) (nh_6 0) s_6 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_6 : treeBlockF 0 1 ch_6 = true := by decide +kernel
theorem nc_6 : ∀ i, 0 ≤ i → i < 1 → ch_6 i = true := fun _ h1 h2 => treeBlockF_at nb_6 h1 h2
theorem lb_6 : LowerBin m_6 s_6 g_6 4 :=
  lowerDagV5 (kn_nil) rc_6 nc_6 (by decide +kernel)

def m_7 : Nat := 0x3300330000000000
def s_7 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_7 : Nat := 0x100130000000000
def ep_7 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
def bds_7 : List (Nat × List Nat × Nat × Nat) := []
def cur_7 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_7 : Nat → Nat := fun _ => 0
def f_7 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_7 : Nat → Bool := dagCheckNodeV5 m_7 g_7 ep_7 1 1 bds_7 1 (dagTraceF m_7 s_7 3 f_7) cur_7 nh_7
set_option maxHeartbeats 0 in
theorem rc_7 : dagCheckRootsV5 m_7 g_7 ep_7 1 1 1 bds_7 (dagTraceF m_7 s_7 3 f_7) (cur_7 0) (nh_7 0) s_7 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_7 : treeBlockF 0 1 ch_7 = true := by decide +kernel
theorem nc_7 : ∀ i, 0 ≤ i → i < 1 → ch_7 i = true := fun _ h1 h2 => treeBlockF_at nb_7 h1 h2
theorem lb_7 : LowerBin m_7 s_7 g_7 4 :=
  lowerDagV5 (kn_nil) rc_7 nc_7 (by decide +kernel)

def m_8 : Nat := 0xf000f0000000000
def s_8 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_8 : Nat := 0x100070000000000
def ep_8 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
def bds_8 : List (Nat × List Nat × Nat × Nat) := []
def cur_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_8 : Nat → Nat := fun _ => 0
def f_8 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_8 : Nat → Bool := dagCheckNodeV5 m_8 g_8 ep_8 1 1 bds_8 1 (dagTraceF m_8 s_8 3 f_8) cur_8 nh_8
set_option maxHeartbeats 0 in
theorem rc_8 : dagCheckRootsV5 m_8 g_8 ep_8 1 1 1 bds_8 (dagTraceF m_8 s_8 3 f_8) (cur_8 0) (nh_8 0) s_8 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_8 : treeBlockF 0 1 ch_8 = true := by decide +kernel
theorem nc_8 : ∀ i, 0 ≤ i → i < 1 → ch_8 i = true := fun _ h1 h2 => treeBlockF_at nb_8 h1 h2
theorem lb_8 : LowerBin m_8 s_8 g_8 4 :=
  lowerDagV5 (kn_nil) rc_8 nc_8 (by decide +kernel)

def m_9 : Nat := 0x4444444400000000
def s_9 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_9 : Nat := 0x4044400000000
def ep_9 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
def bds_9 : List (Nat × List Nat × Nat × Nat) := []
def cur_9 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_9 : Nat → Nat := fun _ => 0
def f_9 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_9 : Nat → Bool := dagCheckNodeV5 m_9 g_9 ep_9 1 1 bds_9 1 (dagTraceF m_9 s_9 3 f_9) cur_9 nh_9
set_option maxHeartbeats 0 in
theorem rc_9 : dagCheckRootsV5 m_9 g_9 ep_9 1 1 1 bds_9 (dagTraceF m_9 s_9 3 f_9) (cur_9 0) (nh_9 0) s_9 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_9 : treeBlockF 0 1 ch_9 = true := by decide +kernel
theorem nc_9 : ∀ i, 0 ≤ i → i < 1 → ch_9 i = true := fun _ h1 h2 => treeBlockF_at nb_9 h1 h2
theorem lb_9 : LowerBin m_9 s_9 g_9 4 :=
  lowerDagV5 (kn_nil) rc_9 nc_9 (by decide +kernel)

def m_10 : Nat := 0xff000000000000
def s_10 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_10 : Nat := 0x17000000000000
def ep_10 : Nat := 0x600000000000000120000000000000014000000000000
def bds_10 : List (Nat × List Nat × Nat × Nat) := []
def cur_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_10 : Nat → Nat := fun _ => 0
def f_10 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_10 : Nat → Bool := dagCheckNodeV5 m_10 g_10 ep_10 1 1 bds_10 1 (dagTraceF m_10 s_10 3 f_10) cur_10 nh_10
set_option maxHeartbeats 0 in
theorem rc_10 : dagCheckRootsV5 m_10 g_10 ep_10 1 1 1 bds_10 (dagTraceF m_10 s_10 3 f_10) (cur_10 0) (nh_10 0) s_10 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_10 : treeBlockF 0 1 ch_10 = true := by decide +kernel
theorem nc_10 : ∀ i, 0 ≤ i → i < 1 → ch_10 i = true := fun _ h1 h2 => treeBlockF_at nb_10 h1 h2
theorem lb_10 : LowerBin m_10 s_10 g_10 4 :=
  lowerDagV5 (kn_nil) rc_10 nc_10 (by decide +kernel)

def m_11 : Nat := 0xaaaa00000000
def s_11 : List Nat := [0x222200000000, 0xa0a00000000, 0xaa00000000]
def g_11 : Nat := 0x22a00000000
def ep_11 : Nat := 0x2800000000000002080000000000000220000000000000000000000000
def bds_11 : List (Nat × List Nat × Nat × Nat) := []
def cur_11 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_11 : Nat → Nat := fun _ => 0
def f_11 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_11 : Nat → Bool := dagCheckNodeV5 m_11 g_11 ep_11 1 1 bds_11 1 (dagTraceF m_11 s_11 3 f_11) cur_11 nh_11
set_option maxHeartbeats 0 in
theorem rc_11 : dagCheckRootsV5 m_11 g_11 ep_11 1 1 1 bds_11 (dagTraceF m_11 s_11 3 f_11) (cur_11 0) (nh_11 0) s_11 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_11 : treeBlockF 0 1 ch_11 = true := by decide +kernel
theorem nc_11 : ∀ i, 0 ≤ i → i < 1 → ch_11 i = true := fun _ h1 h2 => treeBlockF_at nb_11 h1 h2
theorem lb_11 : LowerBin m_11 s_11 g_11 4 :=
  lowerDagV5 (kn_nil) rc_11 nc_11 (by decide +kernel)

def m_12 : Nat := 0x2222222200000000
def s_12 : List Nat := [0x202020200000000, 0x22002200000000, 0x222200000000]
def g_12 : Nat := 0x2022200000000
def ep_12 : Nat := 0x220000000000002002000000000000202000000000000000000000000000000000000000000
def bds_12 : List (Nat × List Nat × Nat × Nat) := []
def cur_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_12 : Nat → Nat := fun _ => 0
def f_12 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_12 : Nat → Bool := dagCheckNodeV5 m_12 g_12 ep_12 1 1 bds_12 1 (dagTraceF m_12 s_12 3 f_12) cur_12 nh_12
set_option maxHeartbeats 0 in
theorem rc_12 : dagCheckRootsV5 m_12 g_12 ep_12 1 1 1 bds_12 (dagTraceF m_12 s_12 3 f_12) (cur_12 0) (nh_12 0) s_12 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_12 : treeBlockF 0 1 ch_12 = true := by decide +kernel
theorem nc_12 : ∀ i, 0 ≤ i → i < 1 → ch_12 i = true := fun _ h1 h2 => treeBlockF_at nb_12 h1 h2
theorem lb_12 : LowerBin m_12 s_12 g_12 4 :=
  lowerDagV5 (kn_nil) rc_12 nc_12 (by decide +kernel)

def m_13 : Nat := 0xa0a0a0a00000000
def s_13 : List Nat := [0x202020200000000, 0xa000a00000000, 0xa0a00000000]
def g_13 : Nat := 0x2020a00000000
def ep_13 : Nat := 0x208000000000002000800000000000000000000000000020200000000000000000000000000
def bds_13 : List (Nat × List Nat × Nat × Nat) := []
def cur_13 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_13 : Nat → Nat := fun _ => 0
def f_13 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_13 : Nat → Bool := dagCheckNodeV5 m_13 g_13 ep_13 1 1 bds_13 1 (dagTraceF m_13 s_13 3 f_13) cur_13 nh_13
set_option maxHeartbeats 0 in
theorem rc_13 : dagCheckRootsV5 m_13 g_13 ep_13 1 1 1 bds_13 (dagTraceF m_13 s_13 3 f_13) (cur_13 0) (nh_13 0) s_13 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_13 : treeBlockF 0 1 ch_13 = true := by decide +kernel
theorem nc_13 : ∀ i, 0 ≤ i → i < 1 → ch_13 i = true := fun _ h1 h2 => treeBlockF_at nb_13 h1 h2
theorem lb_13 : LowerBin m_13 s_13 g_13 4 :=
  lowerDagV5 (kn_nil) rc_13 nc_13 (by decide +kernel)

def m_14 : Nat := 0xc0c0c0c00000000
def s_14 : List Nat := [0x404040400000000, 0xc000c00000000, 0xc0c00000000]
def g_14 : Nat := 0x4040c00000000
def ep_14 : Nat := 0x408000000000004000800000000000000000000000000000000000000000004040000000000
def bds_14 : List (Nat × List Nat × Nat × Nat) := []
def cur_14 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_14 : Nat → Nat := fun _ => 0
def f_14 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_14 : Nat → Bool := dagCheckNodeV5 m_14 g_14 ep_14 1 1 bds_14 1 (dagTraceF m_14 s_14 3 f_14) cur_14 nh_14
set_option maxHeartbeats 0 in
theorem rc_14 : dagCheckRootsV5 m_14 g_14 ep_14 1 1 1 bds_14 (dagTraceF m_14 s_14 3 f_14) (cur_14 0) (nh_14 0) s_14 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_14 : treeBlockF 0 1 ch_14 = true := by decide +kernel
theorem nc_14 : ∀ i, 0 ≤ i → i < 1 → ch_14 i = true := fun _ h1 h2 => treeBlockF_at nb_14 h1 h2
theorem lb_14 : LowerBin m_14 s_14 g_14 4 :=
  lowerDagV5 (kn_nil) rc_14 nc_14 (by decide +kernel)

def m_15 : Nat := 0x5500000055000000
def s_15 : List Nat := [0x1100000011000000, 0x500000005000000, 0x55000000]
def g_15 : Nat := 0x100000015000000
def ep_15 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000000000000000000
def bds_15 : List (Nat × List Nat × Nat × Nat) := []
def cur_15 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_15 : Nat → Nat := fun _ => 0
def f_15 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_15 : Nat → Bool := dagCheckNodeV5 m_15 g_15 ep_15 1 1 bds_15 1 (dagTraceF m_15 s_15 3 f_15) cur_15 nh_15
set_option maxHeartbeats 0 in
theorem rc_15 : dagCheckRootsV5 m_15 g_15 ep_15 1 1 1 bds_15 (dagTraceF m_15 s_15 3 f_15) (cur_15 0) (nh_15 0) s_15 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_15 : treeBlockF 0 1 ch_15 = true := by decide +kernel
theorem nc_15 : ∀ i, 0 ≤ i → i < 1 → ch_15 i = true := fun _ h1 h2 => treeBlockF_at nb_15 h1 h2
theorem lb_15 : LowerBin m_15 s_15 g_15 4 :=
  lowerDagV5 (kn_nil) rc_15 nc_15 (by decide +kernel)

def m_16 : Nat := 0xf0f000000000
def s_16 : List Nat := [0x505000000000, 0x303000000000, 0xf000000000]
def g_16 : Nat := 0x107000000000
def ep_16 : Nat := 0x6000000000000000000000000000001020000000000000104000000000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_16 : Nat → Nat := fun _ => 0
def f_16 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 1 (dagTraceF m_16 s_16 3 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 1 bds_16 (dagTraceF m_16 s_16 3 f_16) (cur_16 0) (nh_16 0) s_16 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 1 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 1 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 4 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0x3030000030300000
def s_17 : List Nat := [0x1010000010100000, 0x30000000300000, 0x30300000]
def g_17 : Nat := 0x10000010300000
def ep_17 : Nat := 0x1020000000000000000000000010000000200000000000000000000000000000000000000010000010000000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_17 : Nat → Nat := fun _ => 0
def f_17 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 1 (dagTraceF m_17 s_17 3 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 1 bds_17 (dagTraceF m_17 s_17 3 f_17) (cur_17 0) (nh_17 0) s_17 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 1 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 1 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 4 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0xcccc00000000
def s_18 : List Nat := [0x444400000000, 0xc0c00000000, 0xcc00000000]
def g_18 : Nat := 0x44c00000000
def ep_18 : Nat := 0x4800000000000004080000000000000000000000000000044000000000
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cur_18 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_18 : Nat → Nat := fun _ => 0
def f_18 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 1 (dagTraceF m_18 s_18 3 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 1 bds_18 (dagTraceF m_18 s_18 3 f_18) (cur_18 0) (nh_18 0) s_18 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18 : treeBlockF 0 1 ch_18 = true := by decide +kernel
theorem nc_18 : ∀ i, 0 ≤ i → i < 1 → ch_18 i = true := fun _ h1 h2 => treeBlockF_at nb_18 h1 h2
theorem lb_18 : LowerBin m_18 s_18 g_18 4 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3333000000000000
def s_19 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_19 : Nat := 0x113000000000000
def ep_19 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_19 : Nat → Nat := fun _ => 0
def f_19 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 1 (dagTraceF m_19 s_19 3 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 1 bds_19 (dagTraceF m_19 s_19 3 f_19) (cur_19 0) (nh_19 0) s_19 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 1 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 1 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 4 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0x5555000000000000
def s_20 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_20 : Nat := 0x115000000000000
def ep_20 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := []
def cur_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_20 : Nat → Nat := fun _ => 0
def f_20 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 1 (dagTraceF m_20 s_20 3 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 1 bds_20 (dagTraceF m_20 s_20 3 f_20) (cur_20 0) (nh_20 0) s_20 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20 : treeBlockF 0 1 ch_20 = true := by decide +kernel
theorem nc_20 : ∀ i, 0 ≤ i → i < 1 → ch_20 i = true := fun _ h1 h2 => treeBlockF_at nb_20 h1 h2
theorem lb_20 : LowerBin m_20 s_20 g_20 4 :=
  lowerDagV5 (kn_nil) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xff0000000000
def s_21 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_21 : Nat := 0x170000000000
def ep_21 : Nat := 0x6000000000000001200000000000000140000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := []
def cur_21 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_21 : Nat → Nat := fun _ => 0
def f_21 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 1 (dagTraceF m_21 s_21 3 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 1 bds_21 (dagTraceF m_21 s_21 3 f_21) (cur_21 0) (nh_21 0) s_21 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21 : treeBlockF 0 1 ch_21 = true := by decide +kernel
theorem nc_21 : ∀ i, 0 ≤ i → i < 1 → ch_21 i = true := fun _ h1 h2 => treeBlockF_at nb_21 h1 h2
theorem lb_21 : LowerBin m_21 s_21 g_21 4 :=
  lowerDagV5 (kn_nil) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xf0f0
def s_22 : List Nat := [0x5050, 0x3030, 0xf0]
def g_22 : Nat := 0x1070
def ep_22 : Nat := 0x60000000000000000000000000000010200000000000001040
def bds_22 : List (Nat × List Nat × Nat × Nat) := []
def cur_22 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_22 : Nat → Nat := fun _ => 0
def f_22 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_22 : Nat → Bool := dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 1 (dagTraceF m_22 s_22 3 f_22) cur_22 nh_22
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 1 bds_22 (dagTraceF m_22 s_22 3 f_22) (cur_22 0) (nh_22 0) s_22 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_22 : treeBlockF 0 1 ch_22 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 1 → ch_22 i = true := fun _ h1 h2 => treeBlockF_at nb_22 h1 h2
theorem lb_22 : LowerBin m_22 s_22 g_22 4 :=
  lowerDagV5 (kn_nil) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xc000c000c000c00
def s_23 : List Nat := [0x400040004000400, 0xc0000000c00, 0xc000c00]
def g_23 : Nat := 0x40004000c00
def ep_23 : Nat := 0x400080000000400000008000000000000000000000000000000000000000000000000000000040004000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := []
def cur_23 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_23 : Nat → Nat := fun _ => 0
def f_23 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_23 : Nat → Bool := dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 1 (dagTraceF m_23 s_23 3 f_23) cur_23 nh_23
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 1 bds_23 (dagTraceF m_23 s_23 3 f_23) (cur_23 0) (nh_23 0) s_23 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_23 : treeBlockF 0 1 ch_23 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 1 → ch_23 i = true := fun _ h1 h2 => treeBlockF_at nb_23 h1 h2
theorem lb_23 : LowerBin m_23 s_23 g_23 4 :=
  lowerDagV5 (kn_nil) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xcc00cc
def s_24 : List Nat := [0x440044, 0xc000c, 0xcc]
def g_24 : Nat := 0x4004c
def ep_24 : Nat := 0x480000000000000000000000000004000800000000000000000000000000040040
def bds_24 : List (Nat × List Nat × Nat × Nat) := []
def cur_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0x7 2 3 1 1 3 7 4 15
def nh_24 : Nat → Nat := fun _ => 0
def f_24 : Nat → Nat × Nat := unpackForestF 0x7 1 3
def ch_24 : Nat → Bool := dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 1 (dagTraceF m_24 s_24 3 f_24) cur_24 nh_24
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 1 bds_24 (dagTraceF m_24 s_24 3 f_24) (cur_24 0) (nh_24 0) s_24 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_24 : treeBlockF 0 1 ch_24 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 1 → ch_24 i = true := fun _ h1 h2 => treeBlockF_at nb_24 h1 h2
theorem lb_24 : LowerBin m_24 s_24 g_24 4 :=
  lowerDagV5 (kn_nil) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xff00ff0000000000
def s_25 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_25 : Nat := 0x100170000000000
def ep_25 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_8, s_8, 4, g_8), (m_21, s_21, 4, g_21), (m_6, s_6, 4, g_6), (m_7, s_7, 4, g_7)]
def cc_25_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_25_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_25 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_25_1 (Nat.sub p 32)) (cc_25_0 p) (Nat.blt p 32)
def hc_25_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_25_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_25 : Nat → Nat := fun p => Bool.rec (hc_25_1 (Nat.sub p 32)) (hc_25_0 p) (Nat.blt p 32)
def f_25 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_25 : Nat → Bool := dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 43 (dagTraceF m_25 s_25 6 f_25) cur_25 nh_25
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 43 bds_25 (dagTraceF m_25 s_25 6 f_25) (cur_25 0) (nh_25 0) s_25 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_0 : treeBlockF 0 32 ch_25 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_25_1 : treeBlockF 32 43 ch_25 = true := by decide +kernel
theorem nj_25_1 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_25_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_25_1 h1 h2)
theorem nc_25 : ∀ i, 0 ≤ i → i < 43 → ch_25 i = true := nj_25_1
theorem lb_25 : LowerBin m_25 s_25 g_25 7 :=
  lowerDagV5 (kn_cons lb_8 (kn_cons lb_21 (kn_cons lb_6 (kn_cons lb_7 (kn_nil))))) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0xffff000000000000
def s_26 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_26 : Nat := 0x117000000000000
def ep_26 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_10, s_10, 4, g_10), (m_20, s_20, 4, g_20), (m_19, s_19, 4, g_19)]
def cc_26_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_26_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_26 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_26_1 (Nat.sub p 32)) (cc_26_0 p) (Nat.blt p 32)
def hc_26_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_26_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_26 : Nat → Nat := fun p => Bool.rec (hc_26_1 (Nat.sub p 32)) (hc_26_0 p) (Nat.blt p 32)
def f_26 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_26 : Nat → Bool := dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 43 (dagTraceF m_26 s_26 6 f_26) cur_26 nh_26
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 43 bds_26 (dagTraceF m_26 s_26 6 f_26) (cur_26 0) (nh_26 0) s_26 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_0 : treeBlockF 0 32 ch_26 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_26_1 : treeBlockF 32 43 ch_26 = true := by decide +kernel
theorem nj_26_1 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_26_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_26_1 h1 h2)
theorem nc_26 : ∀ i, 0 ≤ i → i < 43 → ch_26 i = true := nj_26_1
theorem lb_26 : LowerBin m_26 s_26 g_26 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_10 (kn_cons lb_20 (kn_cons lb_19 (kn_nil))))) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0xffff00000000
def s_27 : List Nat := [0x555500000000, 0x333300000000, 0xf0f00000000, 0xff00000000]
def g_27 : Nat := 0x177f00000000
def ep_27 : Nat := 0x6800000000000006080000000000001220000000000000144000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_16, s_16, 4, g_16), (m_21, s_21, 4, g_21), (m_18, s_18, 4, g_18), (m_11, s_11, 4, g_11)]
def cc_27_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_27_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_27 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_27_1 (Nat.sub p 32)) (cc_27_0 p) (Nat.blt p 32)
def hc_27_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_27_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_27 : Nat → Nat := fun p => Bool.rec (hc_27_1 (Nat.sub p 32)) (hc_27_0 p) (Nat.blt p 32)
def f_27 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_27 : Nat → Bool := dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 43 (dagTraceF m_27 s_27 6 f_27) cur_27 nh_27
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 43 bds_27 (dagTraceF m_27 s_27 6 f_27) (cur_27 0) (nh_27 0) s_27 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_0 : treeBlockF 0 32 ch_27 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_27_1 : treeBlockF 32 43 ch_27 = true := by decide +kernel
theorem nj_27_1 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_27_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_27_1 h1 h2)
theorem nc_27 : ∀ i, 0 ≤ i → i < 43 → ch_27 i = true := nj_27_1
theorem lb_27 : LowerBin m_27 s_27 g_27 7 :=
  lowerDagV5 (kn_cons lb_16 (kn_cons lb_21 (kn_cons lb_18 (kn_cons lb_11 (kn_nil))))) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0xff00ff00000000
def s_28 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_28 : Nat := 0x17007f00000000
def ep_28 : Nat := 0x68000000000000000000000000000600080000000000120020000000000014004000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_10, s_10, 4, g_10), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
def cc_28_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_28_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_28 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_28_1 (Nat.sub p 32)) (cc_28_0 p) (Nat.blt p 32)
def hc_28_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_28_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_28 : Nat → Nat := fun p => Bool.rec (hc_28_1 (Nat.sub p 32)) (hc_28_0 p) (Nat.blt p 32)
def f_28 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_28 : Nat → Bool := dagCheckNodeV5 m_28 g_28 ep_28 1 1 bds_28 43 (dagTraceF m_28 s_28 6 f_28) cur_28 nh_28
set_option maxHeartbeats 0 in
theorem rc_28 : dagCheckRootsV5 m_28 g_28 ep_28 1 1 43 bds_28 (dagTraceF m_28 s_28 6 f_28) (cur_28 0) (nh_28 0) s_28 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_0 : treeBlockF 0 32 ch_28 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_28_1 : treeBlockF 32 43 ch_28 = true := by decide +kernel
theorem nj_28_1 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_28_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_28_1 h1 h2)
theorem nc_28 : ∀ i, 0 ≤ i → i < 43 → ch_28 i = true := nj_28_1
theorem lb_28 : LowerBin m_28 s_28 g_28 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_10 (kn_cons lb_1 (kn_cons lb_3 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0xf0f0f0f000000000
def s_29 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_29 : Nat := 0x10107000000000
def ep_29 : Nat := 0x1060000000000010006000000000000000000000000000101020000000000010104000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_16, s_16, 4, g_16), (m_4, s_4, 4, g_4), (m_2, s_2, 4, g_2)]
def cc_29_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_29_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_29 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_29_1 (Nat.sub p 32)) (cc_29_0 p) (Nat.blt p 32)
def hc_29_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_29_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_29 : Nat → Nat := fun p => Bool.rec (hc_29_1 (Nat.sub p 32)) (hc_29_0 p) (Nat.blt p 32)
def f_29 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 43 (dagTraceF m_29 s_29 6 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 43 bds_29 (dagTraceF m_29 s_29 6 f_29) (cur_29 0) (nh_29 0) s_29 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_0 : treeBlockF 0 32 ch_29 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29_1 : treeBlockF 32 43 ch_29 = true := by decide +kernel
theorem nj_29_1 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_29_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_29_1 h1 h2)
theorem nc_29 : ∀ i, 0 ≤ i → i < 43 → ch_29 i = true := nj_29_1
theorem lb_29 : LowerBin m_29 s_29 g_29 7 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_16 (kn_cons lb_4 (kn_cons lb_2 (kn_nil))))) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0xf0f0f0f00000000
def s_30 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_30 : Nat := 0x107070f00000000
def ep_30 : Nat := 0x608000000000006000800000000000000000000000001020200000000000104040000000000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_8, s_8, 4, g_8), (m_14, s_14, 4, g_14), (m_13, s_13, 4, g_13)]
def cc_30_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_30_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_30 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_30_1 (Nat.sub p 32)) (cc_30_0 p) (Nat.blt p 32)
def hc_30_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e56655092040a6ad8c0011820539b81622002630805682cb74a008803a6b2b0810 15 32767 6 63
def hc_30_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e754ae0732b4dad55068b56 13 8191 6 63
def nh_30 : Nat → Nat := fun p => Bool.rec (hc_30_1 (Nat.sub p 32)) (hc_30_0 p) (Nat.blt p 32)
def f_30 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_30 : Nat → Bool := dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 43 (dagTraceF m_30 s_30 6 f_30) cur_30 nh_30
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 43 bds_30 (dagTraceF m_30 s_30 6 f_30) (cur_30 0) (nh_30 0) s_30 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_0 : treeBlockF 0 32 ch_30 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_30_1 : treeBlockF 32 43 ch_30 = true := by decide +kernel
theorem nj_30_1 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_30_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_30_1 h1 h2)
theorem nc_30 : ∀ i, 0 ≤ i → i < 43 → ch_30 i = true := nj_30_1
theorem lb_30 : LowerBin m_30 s_30 g_30 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_8 (kn_cons lb_14 (kn_cons lb_13 (kn_nil))))) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xcccccccc00000000
def s_31 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_31 : Nat := 0x4044c00000000
def ep_31 : Nat := 0x448000000000004004800000000000404080000000000000000000000000004044000000000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_18, s_18, 4, g_18), (m_9, s_9, 4, g_9), (m_14, s_14, 4, g_14)]
def cc_31_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_31_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_31 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_31_1 (Nat.sub p 32)) (cc_31_0 p) (Nat.blt p 32)
def hc_31_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_31_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_31 : Nat → Nat := fun p => Bool.rec (hc_31_1 (Nat.sub p 32)) (hc_31_0 p) (Nat.blt p 32)
def f_31 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_31 : Nat → Bool := dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 43 (dagTraceF m_31 s_31 6 f_31) cur_31 nh_31
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 43 bds_31 (dagTraceF m_31 s_31 6 f_31) (cur_31 0) (nh_31 0) s_31 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_0 : treeBlockF 0 32 ch_31 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_31_1 : treeBlockF 32 43 ch_31 = true := by decide +kernel
theorem nj_31_1 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_31_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_31_1 h1 h2)
theorem nc_31 : ∀ i, 0 ≤ i → i < 43 → ch_31 i = true := nj_31_1
theorem lb_31 : LowerBin m_31 s_31 g_31 7 :=
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_18 (kn_cons lb_9 (kn_cons lb_14 (kn_nil))))) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0x3333333300000000
def s_32 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_32 : Nat := 0x113133300000000
def ep_32 : Nat := 0x1220000000000012002000000000010202000000000000000000000000000110100000000000
def bds_32 : List (Nat × List Nat × Nat × Nat) := [(m_7, s_7, 4, g_7), (m_19, s_19, 4, g_19), (m_2, s_2, 4, g_2), (m_12, s_12, 4, g_12)]
def cc_32_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_32_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_32 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_32_1 (Nat.sub p 32)) (cc_32_0 p) (Nat.blt p 32)
def hc_32_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_32_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_32 : Nat → Nat := fun p => Bool.rec (hc_32_1 (Nat.sub p 32)) (hc_32_0 p) (Nat.blt p 32)
def f_32 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 43 (dagTraceF m_32 s_32 6 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 43 bds_32 (dagTraceF m_32 s_32 6 f_32) (cur_32 0) (nh_32 0) s_32 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_0 : treeBlockF 0 32 ch_32 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32_1 : treeBlockF 32 43 ch_32 = true := by decide +kernel
theorem nj_32_1 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_32_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_32_1 h1 h2)
theorem nc_32 : ∀ i, 0 ≤ i → i < 43 → ch_32 i = true := nj_32_1
theorem lb_32 : LowerBin m_32 s_32 g_32 7 :=
  lowerDagV5 (kn_cons lb_7 (kn_cons lb_19 (kn_cons lb_2 (kn_cons lb_12 (kn_nil))))) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0xaaaaaaaa00000000
def s_33 : List Nat := [0x2222222200000000, 0xa0a0a0a00000000, 0xaa00aa00000000, 0xaaaa00000000]
def g_33 : Nat := 0x2022a00000000
def ep_33 : Nat := 0x228000000000002002800000000000202080000000000020220000000000000000000000000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3), (m_11, s_11, 4, g_11), (m_12, s_12, 4, g_12), (m_13, s_13, 4, g_13)]
def cc_33_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_33_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_33 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_33_1 (Nat.sub p 32)) (cc_33_0 p) (Nat.blt p 32)
def hc_33_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_33_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_33 : Nat → Nat := fun p => Bool.rec (hc_33_1 (Nat.sub p 32)) (hc_33_0 p) (Nat.blt p 32)
def f_33 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_33 : Nat → Bool := dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 43 (dagTraceF m_33 s_33 6 f_33) cur_33 nh_33
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 43 bds_33 (dagTraceF m_33 s_33 6 f_33) (cur_33 0) (nh_33 0) s_33 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_0 : treeBlockF 0 32 ch_33 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_33_1 : treeBlockF 32 43 ch_33 = true := by decide +kernel
theorem nj_33_1 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_33_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_33_1 h1 h2)
theorem nc_33 : ∀ i, 0 ≤ i → i < 43 → ch_33 i = true := nj_33_1
theorem lb_33 : LowerBin m_33 s_33 g_33 7 :=
  lowerDagV5 (kn_cons lb_3 (kn_cons lb_11 (kn_cons lb_12 (kn_cons lb_13 (kn_nil))))) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5555555500000000
def s_34 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_34 : Nat := 0x115155500000000
def ep_34 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6), (m_20, s_20, 4, g_20), (m_4, s_4, 4, g_4), (m_9, s_9, 4, g_9)]
def cc_34_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_34_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_34 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_34_1 (Nat.sub p 32)) (cc_34_0 p) (Nat.blt p 32)
def hc_34_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_34_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_34 : Nat → Nat := fun p => Bool.rec (hc_34_1 (Nat.sub p 32)) (hc_34_0 p) (Nat.blt p 32)
def f_34 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_34 : Nat → Bool := dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 43 (dagTraceF m_34 s_34 6 f_34) cur_34 nh_34
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 43 bds_34 (dagTraceF m_34 s_34 6 f_34) (cur_34 0) (nh_34 0) s_34 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_0 : treeBlockF 0 32 ch_34 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_34_1 : treeBlockF 32 43 ch_34 = true := by decide +kernel
theorem nj_34_1 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_34_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_34_1 h1 h2)
theorem nc_34 : ∀ i, 0 ≤ i → i < 43 → ch_34 i = true := nj_34_1
theorem lb_34 : LowerBin m_34 s_34 g_34 7 :=
  lowerDagV5 (kn_cons lb_6 (kn_cons lb_20 (kn_cons lb_4 (kn_cons lb_9 (kn_nil))))) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0x6666000066660000
def s_35 : List Nat := [0x2222000022220000, 0x606000006060000, 0x66000000660000, 0x66660000]
def g_35 : Nat := 0x6000004260000
def ep_35 : Nat := 0x420000000000000000000000006000000220000000600000404000000000000000000000000000000000000
def bds_35 : List (Nat × List Nat × Nat × Nat) := []
def cur_35 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xb9710f 4 15 2 3 6 63 8 255
def nh_35 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_35 : Nat → Nat × Nat := unpackForestF 0x1e788f 1 6
def ch_35 : Nat → Bool := dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 3 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 3 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_35 : treeBlockF 0 3 ch_35 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 3 → ch_35 i = true := fun _ h1 h2 => treeBlockF_at nb_35 h1 h2
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_nil) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0x3030303030303030
def s_36 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_36 : Nat := 0x10103010301030
def ep_36 : Nat := 0x1020000000001020000000000010002000200020000000000000000000000000000000000010100010001000
def bds_36 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_36 : Nat → List (Nat × Nat) := fun _ => []
def nh_36 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_36 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 0 bds_36 (dagTraceF m_36 s_36 4 f_36) (cur_36 0) (nh_36 0) s_36 4 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 0 (dagTraceF m_36 s_36 4 f_36) cur_36 nh_36 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_36 : LowerBin m_36 s_36 g_36 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xcccc0000cccc
def s_37 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_37 : Nat := 0x44c00000c4c
def ep_37 : Nat := 0x800000000000000000000000048000000400000040800000c0800000000000000000000044000000040
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 4, g_18)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x3333000033330000
def s_38 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_38 : Nat := 0x113000011330000
def ep_38 : Nat := 0x1020000000000000000000000012000000220000010200000000000000000000000000000110000011000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_38 : Nat → List (Nat × Nat) := fun _ => []
def nh_38 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_38 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 0 bds_38 (dagTraceF m_38 s_38 4 f_38) (cur_38 0) (nh_38 0) s_38 4 = true := by decide +kernel
theorem nc_38 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 0 (dagTraceF m_38 s_38 4 f_38) cur_38 nh_38 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_38 : LowerBin m_38 s_38 g_38 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0x5555000055550000
def s_39 : List Nat := [0x1111000011110000, 0x505000005050000, 0x55000000550000, 0x55550000]
def g_39 : Nat := 0x115000015150000
def ep_39 : Nat := 0x1400000000000000000000000014000000000000010400000404000001100000101000000000000000000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0x5500550055005500
def s_40 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_40 : Nat := 0x100150015001500
def ep_40 : Nat := 0x1400000000001400000000000000000000000000010004000400040001001000100010000000000000000000
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xff000000ff00
def s_41 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_41 : Nat := 0x170000001f00
def ep_41 : Nat := 0x800000000000000000000000000000000000000060000000e0000001200000010000000140000001000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_21, s_21, 4, g_21)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_21 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xaaaa0000aaaa
def s_42 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_42 : Nat := 0x22a00000a2a
def ep_42 : Nat := 0x800000000000000000000000028000000200000020800000a0800000220000000200000000000000000
def bds_42 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_42 : Nat → List (Nat × Nat) := fun _ => []
def nh_42 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_42 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 0 bds_42 (dagTraceF m_42 s_42 4 f_42) (cur_42 0) (nh_42 0) s_42 4 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 0 (dagTraceF m_42 s_42 4 f_42) cur_42 nh_42 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_42 : LowerBin m_42 s_42 g_42 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xff000000ff000000
def s_43 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_43 : Nat := 0x100000015000000
def ep_43 : Nat := 0x1400000000000000000000000000000000000000010000000400000001000000100000000100000015000000
def bds_43 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_43 : Nat → List (Nat × Nat) := fun _ => []
def nh_43 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_43 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 0 bds_43 (dagTraceF m_43 s_43 4 f_43) (cur_43 0) (nh_43 0) s_43 4 = true := by decide +kernel
theorem nc_43 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 0 (dagTraceF m_43 s_43 4 f_43) cur_43 nh_43 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_43 : LowerBin m_43 s_43 g_43 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xff000000ff0000
def s_44 : List Nat := [0x55000000550000, 0x33000000330000, 0xf0000000f0000, 0xff0000]
def g_44 : Nat := 0x17000000370000
def ep_44 : Nat := 0x20000000000000000000000000000000000000000600000004000000120000003200000014000000040000
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xf000f000f000f0
def s_45 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_45 : Nat := 0x10007000300070
def ep_45 : Nat := 0x20000000000060000000400000000000000000000000000000000000100020003000200010004000000040
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xf0f00000f0f00000
def s_46 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_46 : Nat := 0x10000010300000
def ep_46 : Nat := 0x1020000000000000000000000010000000200000000000000000000000100000103000000010000010000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_17, s_17, 4, g_17)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_17 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0x4444444444444444
def s_47 : List Nat := [0x404040404040404, 0x44004400440044, 0x444400004444, 0x44444444]
def g_47 : Nat := 0x4044404040444
def ep_47 : Nat := 0x400000000000440000000400004004000000040000404000404040000000000000000000000000000000000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0x5a005a005a005a00
def s_48 : List Nat := [0xa000a000a000a00, 0x1200120012001200, 0x5a0000005a00, 0x5a005a00]
def g_48 : Nat := 0x120010001a00
def ep_48 : Nat := 0x100008000000120000000a000000000000000000000000000000000000001200100010000000000000000000
def bds_48 : List (Nat × List Nat × Nat × Nat) := []
def cur_48 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc61 0xa9610f 4 15 2 3 6 63 8 255
def nh_48 : Nat → Nat := unpackHintV5 0xd12c415002 0x0 10 1023 5 31
def f_48 : Nat → Nat × Nat := unpackForestF 0x1a708f 1 6
def ch_48 : Nat → Bool := dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 3 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 3 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_48 : treeBlockF 0 3 ch_48 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 3 → ch_48 i = true := fun _ h1 h2 => treeBlockF_at nb_48 h1 h2
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_nil) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xaaaaaaaaaaaaaaaa
def s_49 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_49 : Nat := 0x2022a00220a2a
def ep_49 : Nat := 0x2008000000022800000a0800020028002200200002020800000a0800020220002200200000000000000000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_33, s_33, 7, g_33)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 7 f_49) (cur_49 0) (nh_49 0) s_49 7 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 7 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 8 :=
  lowerDagV5 (kn_cons lb_33 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x5555555555555555
def s_50 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_50 : Nat := 0x115155515151555
def ep_50 : Nat := 0x1400000000001440000000400014004000000040010404000404040001101000101010000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := [(m_34, s_34, 7, g_34)]
def cur_50 : Nat → List (Nat × Nat) := fun _ => []
def nh_50 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_50 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 0 bds_50 (dagTraceF m_50 s_50 7 f_50) (cur_50 0) (nh_50 0) s_50 7 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 0 (dagTraceF m_50 s_50 7 f_50) cur_50 nh_50 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_50 : LowerBin m_50 s_50 g_50 8 :=
  lowerDagV5 (kn_cons lb_34 (kn_nil)) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0xf0f0f0f0f0f0f0f0
def s_51 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_51 : Nat := 0x10107010301070
def ep_51 : Nat := 0x1020000000001060000000400010006000200060000000000000000000101020103010200010104010001040
def bds_51 : List (Nat × List Nat × Nat × Nat) := [(m_29, s_29, 7, g_29)]
def cur_51 : Nat → List (Nat × Nat) := fun _ => []
def nh_51 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_51 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 0 bds_51 (dagTraceF m_51 s_51 7 f_51) (cur_51 0) (nh_51 0) s_51 7 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 0 (dagTraceF m_51 s_51 7 f_51) cur_51 nh_51 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_51 : LowerBin m_51 s_51 g_51 8 :=
  lowerDagV5 (kn_cons lb_29 (kn_nil)) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0xff00ff00ff00ff
def s_52 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_52 : Nat := 0x17007f0037007f
def ep_52 : Nat := 0x20000000000068000000480000000000000000000600080004000800120020003200200014004000040040
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 7 f_52) (cur_52 0) (nh_52 0) s_52 7 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 7 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xf0f0f0f0f0f0f0f
def s_53 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_53 : Nat := 0x107070f05070f0f
def ep_53 : Nat := 0x40008000000060800000a080006000800020000000000000000000001020200000200000104040005040000
def bds_53 : List (Nat × List Nat × Nat × Nat) := [(m_30, s_30, 7, g_30)]
def cur_53 : Nat → List (Nat × Nat) := fun _ => []
def nh_53 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_53 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 0 bds_53 (dagTraceF m_53 s_53 7 f_53) (cur_53 0) (nh_53 0) s_53 7 = true := by decide +kernel
theorem nc_53 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 0 (dagTraceF m_53 s_53 7 f_53) cur_53 nh_53 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_53 : LowerBin m_53 s_53 g_53 8 :=
  lowerDagV5 (kn_cons lb_30 (kn_nil)) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0xffff0000ffff
def s_54 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_54 : Nat := 0x177f00001f7f
def ep_54 : Nat := 0x800000000000000000000000068000000600000060800000e0800001220000010200000144000001040
def bds_54 : List (Nat × List Nat × Nat × Nat) := [(m_27, s_27, 7, g_27)]
def cur_54 : Nat → List (Nat × Nat) := fun _ => []
def nh_54 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_54 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 0 bds_54 (dagTraceF m_54 s_54 7 f_54) (cur_54 0) (nh_54 0) s_54 7 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 0 (dagTraceF m_54 s_54 7 f_54) cur_54 nh_54 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_54 : LowerBin m_54 s_54 g_54 8 :=
  lowerDagV5 (kn_cons lb_27 (kn_nil)) rc_54 nc_54 (by decide +kernel)

def g_55 : Nat := 0x117177f15371f7f
def ep_55 : Nat := 0x142008000000166800000a4800160068002200600106060804040e0801121220103210200114144015041040
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_32, s_32, 7, g_32), (m_54, s_54, 8, g_54), (m_26, s_26, 7, g_26), (m_52, s_52, 8, g_52), (m_25, s_25, 7, g_25), (m_53, s_53, 8, g_53), (m_50, s_50, 8, g_50), (m_51, s_51, 8, g_51), (m_31, s_31, 7, g_31), (m_49, s_49, 8, g_49), (m_23, s_23, 4, g_23), (m_24, s_24, 4, g_24), (m_33, s_33, 7, g_33), (m_29, s_29, 7, g_29), (m_34, s_34, 7, g_34), (m_46, s_46, 5, g_46), (m_39, s_39, 5, g_39), (m_43, s_43, 5, g_43), (m_44, s_44, 5, g_44), (m_38, s_38, 5, g_38), (m_36, s_36, 5, g_36), (m_41, s_41, 5, g_41), (m_45, s_45, 5, g_45), (m_28, s_28, 7, g_28), (m_27, s_27, 7, g_27), (m_37, s_37, 5, g_37), (m_40, s_40, 5, g_40), (m_17, s_17, 4, g_17), (m_22, s_22, 4, g_22), (m_42, s_42, 5, g_42), (m_47, s_47, 5, g_47), (m_48, s_48, 5, g_48), (m_35, s_35, 5, g_35)]
def cc_55_0 : Nat → List (Nat × Nat) := unpackCursorV5 0x9e74f027813429a04b0a58124292049023851c08e0450a2811408a04502281140822410208104082041020810407a23d000f8001 0x23d6f116b588759c41ac61fc6f0f63587719c398c61bc5f0d62d86515c2f8a61701807c0a01a0980602c0a83e030130240d80502c0a85e0100b0241580b04c068660302f0161180302c030660142b0081380306d6d45fb662ddb115ed78a76b35fb55adda8d5ed36a76934fb45a5d9cd1ecb6876025fad52dd4695e904a743a4f9e125cde91e654872e23f94d1dc908de394670e15f7fcadba855da52a6c494f5b8a5a8651d182867e93f3489d96c4dc9a2663f92f1909589249c1e2460e85f0702d83615c1a0a60c84f0602582e11c160860a03f04c1d8220dc100660782f0381581409c090460401f01c0d80405c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_55_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88202801e2781c2701a2681825c5614cd21444e3380e0380e0380e0380e0380e0380e0344d03040c 0x3e2894014f0be4e053a2893014e0aa4a053628920148c2e4617342d9986c880a420d210698944c0224005230b90834b62fd916eb8af5453a5afd0d6e76af335395a7c8d2e268f0343 10 1023 4 15 11 2047 17 131071
def cc_55_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x84610806007c5f0785e0745d0705c06c5b0685a06818260180588ac2808220062180421002208002 0xbedc2eb58b6da2cb48aedc2ab48a6d628b489ed82706c98d225844c55bf056bbd59ee563b51bec46bad19ea463a517e845b9b15e54539059168148c5516014885f15814845515014805914814 10 1023 4 15 11 2047 18 262143
def cc_55_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xe06c761a1d06472181c05c6e161b0546a141a04c66121904820500803885820088400200 0xfc593e154f45f3c154ec593a144e45f38144dc5536144d45b3486cce5133044fb5bfdd6bf359fbd63eb1bf9c6be319f7c63db17f5c5bd115f2c53c6da30b58 9 511 4 15 11 2047 18 262143
def cc_55_4 : Nat → List (Nat × Nat) := unpackCursorV5 0xa02719c2616b1a064590605805c5705856054550505404c530485204451040500400e2380e03080c 0x9e2d9384d2d2b7d956bb0acf5b58eadb7d4b6ba76cf48d8e89afcfb5b9d6af36d4e65324ba54954f926952453247a448d4f916912252a43a44854d9081b209224084498adf2d5ae52b3c9563908df1d1ae3233c5463888bf0d16e0e2bc0453 10 1023 4 15 11 2047 19 524287
def cc_55_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xf078385c0d8e8741916e34182c058ac142a048a05007138184c051281406430108804002 0x2f92e5e824bb06975182e12e6856fcead79959f2ab1e426fc64d78899f0531dfa5fbc4b77295edd29da964b32a9625f2bd23d7154ac2c9544d2a0be53134a506946552849a50034 9 511 4 15 11 2047 19 524287
def cc_55_6 : Nat → List (Nat × Nat) := unpackCursorV5 0x98260982609825194250906409018c2b8a024490204801c4701846014450104400c4300c01204001 0x368126b824e18bfc116f7e2bef453dd4bfb896f6d2beca53d849fac92f5523ea243fbadff35afdeb3fad63f36dfe2dafbdb3f6363ea6bfced6f95abf1b53e2031a6053463467c58cd8e197163263463a5cc58e186973081260458 10 1023 4 15 11 2047 19 524287
def cc_55_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xa85ec781c2701a268182601625814250122481023c4e12ccb0248811c44310022080020000000000 0x7fa448b56f8a56b89567885638726f8626b8526783a6382a5f8125b802577f2537e164708147d154700147c17c6f8147b1546f0147a1646e814791346e0147817c6d8146d0246d02477134768346c814759546c0146b8246b82474934740346b0147316c6a814721346a014 10 1023 4 15 11 2047 20 1048575
def cc_55_8 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a02809c5bc378d0304c02c4b0284a024490204801c4701846018042100310c0300481000400 0x8d82493b5f9335b92b579235391a5f9125b90a578fa538f23f8ea3b8e2378d233a0c6f9fc6b9ec679dc639cb6f9bb6b9ab67993639834f9734b9634794b43940188c8148bb648ab5489b7c88b5487b6486a4485b7c84a448402483354822448182480b6c 10 1023 4 15 11 2047 20 1048575
def cc_55_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xd99b25eb95aa4e991a0bd66c15284480d15221c20408102040810201 0x27d7c928527944920527564918527134910526d7c908524024900926934998d23e1498d123c1497cd23a1496d7238148d892362495cd254348d0524024 7 127 2 3 9 511 18 262143
def cc_55_10 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8691a06809c66189211842107c9f0785e0745c16c5a164590605714d121481204084c1002208002 0xadb44af45cad340adb4cad454afb4faeb4bae347acb43ac570ab26caa824a9b6ca8a6ca7378a5b64a747ca5360a5b6ca5474a7b6fa6b6ba6367a4b63a4460a326ca2824b636fb536bb3367b2363b126fb026baba67aa263a923fa823ba3a37a2233a116493814a014493014 10 1023 4 15 11 2047 20 1048575
def cc_55_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xf0747a1c1e070345a0c8e430380b8dc2e1524e2410280389c0e052209006230108802201 0xbf134be17cbd134bc834bb944ba934b995cb8934b8034c3c6fc2c6bc1c67c0c63bfb6fbeb6bbdb67bc363bb34fba34bb9347b7b43b6d68b5b6cb4a4fb4247b3d70b2b6cb1d68b0a6caf358 9 511 4 15 11 2047 20 1048575
def cc_55_12 : Nat → List (Nat × Nat) := unpackCursorV5 0xe870781b1d86874191c8642e570b0d46a141a04c6613089170a041200c46021100442001 0xcf354ce464cd254cc47ccb254ca824c985cc9354c8254c7458c6254c5824d1b6fd0b6bcfb67ceb63cda6fcca6bcba67ca263c8a3fc7a3bc6a37c5233c4164c3144c217cc1144c0164 9 511 4 15 11 2047 20 1048575
def cc_55_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8282a02629464184e108421084201801f17c1f0785e0781e0781e0781d14703e0c0210801104001 0xdf134d5014de15cd4814d4024d4024dd134dc834d3814da05cd9034d7824d4024db34fdab4bd9b47d8b43d824fd724bd6a47d6243d5a3fd523bd4a37d3a33e945fe845be6c57e5453e435fe2b5be1b57e0b53dfb4fdeb4bddb47dc343db818d3014d2464d1354d047c 10 1023 4 15 11 2047 20 1048575
def cc_55_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xc4701c02f1b86a4a4690a42726f1b0649905c961545234450134cd02c8a124463180421002208002 0xefc6cedb50ee35cedc64f035fef35beeb57ed353ecc70eba7ceb024feb4ffdb4bf8b47f7343f624ff4a4bf3a47f2a43f1a3ff0a3bec237eaa33e9954db014e8944da814da05cda05ce796ce706cd9814d9034d9034e6144e5844d8814e4954d8014d7824d7824e3934e3034d7014e216cd6814e1134d6014e0144d5814 10 1023 4 15 11 2047 20 1048575
def cc_55_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xc8c1c0b9b1a9a1999891896c685a58584a484140403230292821201918110901 0xff47cfe37cfca58fb244fcb5cfaa40fb24cfab54fd24ffc24bfba47fa243f9d70f905cf837cf7834f6c7cf5a7cf5024f4570f327cf237cf127cefb68ee354 8 255 3 7 11 2047 20 1048575
def cc_55_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8282731c06c5b0685a068182601805896054550541324c1214811144101400f13c0e1380e03080c 0x21f4c90f0248dda7c6ad2e3268f17b438b527c5492e2848f132438911fc448ee2046f0ea3386caa432512172d90b06c850a2426112112a9079348381a4185b20a269041448189a408572022690083486a2fc3116e158af09453841afc1ad6e0b6af04b5381da7c0ad2e0368f00343 10 1023 4 15 11 2047 21 2097151
def cc_55_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xa0280a0280730ee380d1340c1300c0288a028082200711c07014850104400c430084200441000400 0x8fa2fc7b16e3c8af1dc538782fc0216dd60aedc85362c27ae012d4508e9504391ab7c895ae42acf20563874b7c005add52cedc163628afade56d442ae949538fc14474092388c91b3648d2b4466172316c9180348ba324589922b04914d6889d3244ad92234c910c68 10 1023 4 15 11 2047 21 2097151
def cc_55_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xdc361ab2a0a4690a06809c670985ac68191641816018058951541412308018860108400882000800 0x4bcd5263adf30d6b97eb3cbb58e242df0396b78cb3b7e58d912bebb15b548aba6054e5b4c92ca5495d3e4aa9525aadf2c56b95ab3ca958e222df0296b784b3b7a58d8f2beba15b540aba5c54e528d1284589389fc9a4de4c8e125458946b7c9f5ae4bacf24d63880b7c065add82cedd963634afae456d472ae9615391d3247c092454a91e82490d3e478092414a91d824 10 1023 4 15 11 2047 21 2097151
def cc_55_19 : Nat → List (Nat × Nat) := unpackCursorV5 0xf83e0f83e0f832c93a408c63088620846108054c501314c12148111441013c43c0c0210801104001 0x27d6bf3e35b9edabcf4d4e2b0bf0705b7a82bb8c14d0307e7403b2f41b9400ce858df41c6ba0633cff18e2a2df0696b7a4b3b8a58d0229e7394b2f0a393e50e7e0513c8249deb44eadb273ae138b6c9d9b7ce8dae726cf383638a0b7c165ade72cee19634009f9ca4ecb926e4e9339b9324d89126a4f93413799d224db1be6b8d734c6799a31c4c5be092d6f2967704b19fc53ce32965b94726ca1cc8d92626a93037c 10 1023 4 15 11 2047 21 2097151
def cc_55_20 : Nat → List (Nat × Nat) := unpackCursorV5 0xf47c1e4f81dc743d0340d0340cc730c866c639805c57058560545505048c20062180421002208002 0x2950b94a95ca793653a1b29404949834a4c9a5369129a08949024a54ae5264d29769f4b34ba51a3d24d0d9509ebc84b55423a6610d0807e7683b3081b94a0cea18bf4fc5ba722bd3314d942bebc15b550aba6454d0729e7614b304a394850e9805148824a3e3251ad528b8f944b54a39b7d18dae8a6cf443638b4b7c205adec2cee41634149f9d44ecbf26e51133a19324fa092844893e024a093e4f6092804893d024 10 1023 4 15 11 2047 21 2097151
def cc_55_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xc4710c0700c02e2b82e0b0a0c801f17c1e1745c16c5a1681916054450122481204084c1002208002 0x2bf4a95ea44aed365741b2b84895b844afa2fd7916eb98af5b453664afafa56d602ae9b953430a79e252cc628e54943ad23e564df2af2b156144abd2e556502ac29955a54ac0a7d5c52ead28f55143aa6b8550172a66f952834acda7d62d2ea768f5234365ca7af652d5728e9a9434289f9de4ecc426e53933a892a52e092a04894b024 10 1023 4 15 11 2047 21 2097151
def cc_55_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2ca6c9ac8ec82c76c6ac5ec52c46c3ac3a02ce2c020c12e1201111101011001000e20e00e00c200c000 0x26347f2d23b9451bc8c8cd1627e7d93b3409b9684cc9825e3e92b1889388e48e6147f2c23b93d1bc888cd1427e7c93b3389b9644cc9625e3d92b1809388a48e5f47f2b23b92d1bc848cd1227e7b93b3309b9604cc9425e3c92b1789388648e5d47f2a23b9251bc808cd1027e7a93b3289b95a4cc9225e3b92b1709388248e8e49f42a4b9d923cda90da329ec394b5b0a3a8250c9025e3a92b1689387e48e8c4bf41a5b9d12bcd694da12bec295b5a8aba7e54c8e25e3992b1609387a48e8a49f40a4b9c923cd290d9f29ec194b598a3a7a50c8c25e3892b1589387648e884bf3fa5b9c12bccc94d9d2bec095b590aba7654c8a25e3792b1509387248ec94df5f26bacd33d4298e372df0d16b7f4b3ba458c8825e3692b1489386e48ec74df5e26bac533d3e98e352df0c16b7ecb3ba058c8625e3592b1409386a48ec52bf5d15baa0abd3a54e330bf0b05b7c82bb9c14c8403e3481b1380b86604ec44df5ca6ba9d33d3898e322df0a96b7c4b3b9a58c8325e3412b1349386448ed00b967850b08afd6e56ea52af4d1538c02fc2616def0aee58532040f8cc06c4b02e18013b0537d6c9aea44cf4ca638bcb7c245adee2cee5163200978ca4ac4a24e17923b341c5980d2ca8c964364b1ab458a172c36c961034b25a7d8ed2ec468f60b4366ca7afe52d6228e9c9434389f9e64ecc826e55933 12 4095 4 15 11 2047 21 2097151
def cur_55 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_55_22 (Nat.sub p 704)) (cc_55_21 (Nat.sub p 672)) (Nat.blt p 704)) (cc_55_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (cc_55_19 (Nat.sub p 608)) (cc_55_18 (Nat.sub p 576)) (Nat.blt p 608)) (cc_55_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (cc_55_16 (Nat.sub p 512)) (cc_55_15 (Nat.sub p 480)) (Nat.blt p 512)) (cc_55_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (cc_55_13 (Nat.sub p 416)) (cc_55_12 (Nat.sub p 384)) (Nat.blt p 416)) (cc_55_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_55_10 (Nat.sub p 320)) (cc_55_9 (Nat.sub p 288)) (Nat.blt p 320)) (cc_55_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (cc_55_7 (Nat.sub p 224)) (cc_55_6 (Nat.sub p 192)) (Nat.blt p 224)) (cc_55_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (cc_55_4 (Nat.sub p 128)) (cc_55_3 (Nat.sub p 96)) (Nat.blt p 128)) (cc_55_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (cc_55_1 (Nat.sub p 32)) (cc_55_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def hc_55_0 : Nat → Nat := unpackHintV5 0xaec517a70deea22d389a3dfc95912b905d4d8b7d3886494d81553d7b71797381fc6ea13868bd7960cdfc5c01335449ee4f3545464e3a40218b373a3a2f120a2a652b252d4e20054a1a157c1579270f897c09798404ad3300012b000000000000 0x61c187061c187061c1876666665a41bee3750fa8bc4544ea174ad5555555552d54550003c2e05cb8172e6c78f366c59b266c59b265c0b9b0e3c39b061c39b061c39700eac3d30e6e1f1b68db45c2575783d4e079ec78f01e3c780271381c0e44000f1e3c780070e1c380070e1c3d500555503cf6000000001c008078000013005801c0060402000003c780f2e0f078f163c78f163c98f1e3c79702e3c1870e3c1870e3c38f0e5c03ab0f4c38f687b43e1f17095d5e0f53878f363c7803cf6009c4e071387213c001b1e3cd80070e1c380070e1c3d50055550003cf6000000001b000002600b003800c08040000007805c04ead7a700058004d3875e1c00060007561e9874f2f80040095d5e0f538000f6000000000000274e9d380070e1c380070e1c3d50055550001ec000158000101b00780013005801c006040200003c02e0002756bd382c0026009c3af0e030003802b0f4c3a797c200400aeaf07a9c0000001ec0000000013a74e9c003870e1c003870e1ea802aaa800000f62b00000e0006c01e0004c0160070018100800000000b262c98002c00f613264c984c00f602c00001187461c0000987161c9830e4c1874f2f8004009c2e271383c8e0b85c593164c5813266c98f263c993265c00993013875e1cb807261c587260c387260c3874f2f8b844e1713689b41ea72713800ac167b162c058b161c0e42b800162c58b000e1c387000e1c387aa00aaaa00000059ec000038001b0078000002c03800c08040000000058b162c000164c00017ec58b162c00017ec000461d1870180000b0e2c38b0e2c3a797c00002d85b0b85c1e4705c2e2c58b1e2c58b362c5800b2e2c58b162c05809c3af0e5c038b061c38b061c38b0e2c3a797c5c216d0b685c2e0f539389c05602c593162c0167b0e2b0e44000b262c980070e1c380070e1c3d5005555000000002cf6000101b0078000004c03800c0804000b85d3ab5e9cb817061c1870601c187061c39b0e1c38f0e1c397000e1c3930e1c38b0e1c04f2f8b84aeaf0781c1da0ed07038001c0e00cf60c1803060e20013a74e9c00183060c00183060ea802aaa8013800000ac019ec000203600f0000009802c006100800003c783cb83c1e3c58f1e2c78f1e3c79702e0c183060c187061c183060c1830e0fd830060c183060c183060c18707ec183060c1803060c183007b0f61f0f8b84aeaf03606c0e070000f0003eacfa700058003060c1807b001800003060c183061c183060c0003d800c183060c04f2f8004015c7e070381c0e0b85c58b1e2c58b162c0597162c58b1602c0060c18306000c183060c1830e0c383060c183061c1fb060c1830600c183060c1830e0fd83060c1809e5f17085b0b6170b81c0e070382e174ead7a72e05c183061c183061c18300061c183061c183061c183060c1803060c183013cbe2e12babc0da06d0381c1c0e1c000e1c0e1c060c383060033dc078004e9d3a700061c18700061c187aa00aaaa00000000019ec003600f0000009802c00e100800170ba756bd39702e9c3af0e5c03ab0f4c3b321333346ea1f51700a89d42ea0f503a02200222204f6a0a80274e9d380070e1c380070e1c3aa802aaa802700005600001c13d8006c01e0000013005801c0060200000f01e0f078f1e3c78f263c78f1e5c0b8f061c7830e3c38f0e5c03a30e8c3aaaccaab3ed05556555567daaa0aaaa8003c000013ab5e9c0026008c3a30e030000461d18755000180007dacaaaaa8000fb005555002e17164c5931604c9931e4c79326004c0461d1872e01c987161c9830e4c1875550659f6aab32aaaaaa0aaacfb5555002e174ead7a72e05c1830e0c18306000c183060c187060c1830600c183060c0595506595555995567daaa0aaaaacfb55002e174ead7a72e05d3875e1cb807561e9875656500656565656554155550228082228a165013d80274e9d380070e1c380070e1c3b3003333000000000009ec3600f0000009802c00e0030200 24 16777215 10 1023
def hc_55_1 : Nat → Nat := unpackHintV5 0xc371a4b97e7db32596a8b69ca181cd97d66b91e57c88ce4683914f7c45d377015172512c6a52006391b05d7986546a445198b44ced2b46b18f41bd3d3b818f3491bc2da1bc267dc91f8dbc19518f14a52b1170cd0cad3108d8f502719a00009c 0x1e3c78f162e162c78b262c9d50b1747cbb31987cb93275540c3830e0c3830e0c3830e0c1a83061d6666665a5a66aaaaaaa8a8aa961e3c78f163c5fb162c78f164c593162c58f2e3c1e0f1e3c98f061c187061c187061c187060c387060c3876666665a5a5a41bee1f50fa8bc4544e2750b85d43e1f550faa95aaaaaaaaa2a2aa5aa84f540f1f5547c3e5cf87cb8f1e3c78b175542c5c2c58b162c1830e8306a0c3830e0c3830e0c3830eb4b4cccccccd5151555555552c2c58f160b162c165c78f1e3c58b162c58b162c78bf62c58b160c1870e0c1870e0c3830e0c3830e0c3830e8b5a5aa6666665a41bee175542e17550f8dd43e1f51788a85c4ea170ba56aa8a8aaaaaaaa96aa13d506c78f362c58f1e2c78bf70b262c98b175547cbb31987cb8f1f5540c3830e0c3830e0c3830e0c1a83061d6666665a5a5a41beeaaaaaaa8a8aa96363c79b162c78f163c5fb164c593162c5932e4c2613263c78f061c187061c187061c187060c387060c3876666665a5a5a41bee3750fa8bc4544ea1751389d544eaa56aaaaaaaa8a8aa96aa13d50170b9f367c79f1e7cd93260142c58b17000b8a0a061c1870601c1835060c3a0c3830ecc84b4b4cccd10014141111108170b8b362c58b1e2c58b262c58b162c05fb0162c0061c1870601c1830e1c1830e1c187061d99096969996906fb8dd43ea2f17008a85c2eaa175542ea174ad51001414111110944150000b262c982c00f9b3e3cf8f3e6c0000993aaa061c18700061c18705006600660a00640000000000000000164c593017ec003600f00026030e0c380030e0c3801c060cc00cc0420b4837dc6ea1f400011389d42e17400141002b5000000000000000001007cd9f1e7c79f360000002c58b162c5d5500030e0c3800280030e0c3b300050033320007c000000000000000000162c58b0000061c1870000061c187660000665a41bee3750fa08000000021750ba56a007806c000162c58b0160002fd830e0c3803060001c380030e0c3b302800500332d20df71ba87d04000014117000085c4ea170ba56a0000000800000000000800b85c593164c58b0017ee3e6cf8f3e3cf9b162c0282aa0187061c1807061c187060d41830eb321332d2d2d20df744004451047e088840b85c593164c5845cb972e2c20a061c1870601c187061c187061d990999996906fb8dd43ea2e01513a85d45e2f517a95a82e17164c593162c005fb266c98f263c993162c5800c3830e0c03830e0c383061c383061c3b321332d2d2d20df71ba87d45c02a2750ba89c4eaa27552b544004451144e08884a20a80013a74e9c00187061c00187061d9801999800000000002e03cf60001b1e3cd804c160000c3830e00701800030e0c3b301080033325501100055204003cf603c7803cb8f1e3c78f2e05c78b1e4c78b1e3c187061c1807060c387060c387061c18766425a5a6666aa82aaaaaa4a8601e00003cf60b00098f1e3c780003060001c3830e0c380030e0c38801330033321001550055204000f1e0f3d803c78f363c79b2e05cb8b2e4cb8b2e4c187061c1807060c387060c387061c18766425a5a6666aa82aaaaaa4a86164c59b1e3cd8b0597160b162c78bf62c58b162c58b162c58b061c187060c387060c387061c187061c187665a5a666666aaaaaaaaaa6a961e3c78f163c5fb162c78f164c593162c58f2e3c1e0f1e3c98f061c187061c187061c187060c387060c3876666665a5a66aaaaaaaaaa6a96162c78b058b160b2e3c78f1e2c58b162c58b163c5fb162c58b060c387060c387061c187061c187061c18745ad2d5333333335555555555354b1b1e3cd8b163c78b1e2fd8b262c98b162c997261309931e3c7830e0c3830e0c3830e0c383061c383061c3b333332d2d335555555555354b05c2e2cd8b162c78b162c98b162c58b017ec058b00187061c1807060c387060c387061c18766425a5a6666aa82aaaaaa4a8600164c593017ec003600f00026030e0c380030e0c3801c060cc00cc0420c9540154044081008d1a34600002c58b162ea00061c1870100061c1876602006664007806c000162c58b0160002fd830e0c380c000e000c3830ecc200400ccc954100050055204005c2e2c98b262c2468d1a316115030e0c38300e0c3830e0d061d99099999982e17164c593162c005fb266c98f263c993162c5800c3830e0c03830e0c383061c383061c3b321332d2d3355415555544ea4a86061c187061c187061c18766666666aaaaaa6a96 24 16777215 10 1023
def hc_55_2 : Nat → Nat := unpackHintV5 0xec41bbe599aadb1aa0d3d1d2c906b3c185e0b702a1af5de9a4daa19d91d29222dc8b79aa81d26a7cb94675cdbb70655a6bcd2664c9c15e21aa57f98a4d6ea3486d4043314f3be5d335f57c2cde4627c5461ffdf21969a510863909f5a400027d 0xf00001e7b058004c78f1e3c001400001547aa3c0001516a93018000c183060c00183060d61001550055555506fb0000000000000000000789b1e3cd9702e0c183060c0183060c1a2a82800f1e8c99f167c5a3260c1d0381835541555555552e0f000b85c06030b9702e5c110078f079ec01e3c79b1e3cd9702e5c597265c59726a8f54da82025d2eaa975552e97545aa4c183060c1803060c197061c183060c183060c18359550552ecaaaaaaaaa0df65c1e00172e05cb8170b8970500603110d8f1e6d162c58b162c583060c183060c183060c1aaa93267cbbb1d87cba8b16aa0c1d038183555555555555370f8fc9e170b81c0e4e8e13a3855164c59b1e3cd8b0597160b162c78bf62c58b162c58b162c58b547aa6d5516aaa2d16a8897545a2d51693060c183060c183060c183060c183060c18359555555555555541becdc3e162e05a383f2785c2e53a2a0381caa3c78f1e2c7a2c78f164c593060c183060c183060c1835162d55d97763b1d97555264c183a070306aaaaaaaaaaaa3e1f2b95c4e170381cad1c2b470aa3c78f1e2c78bf62c58f1e2c98b262c58b1e5c783c1e3c7931ea8f547aa225d516a935547aaa8f4783060c183060c183060c183060c183060c1acaaaaaaaaaaaaaa0df63e1f2b95c4e170f1f03d1c2ad1501c0e551e3c78f162c5a2c78b162c583060c183060c183060c1a8f1eaa7cbbb1d87cba8b16aa0c1d0381835555555541aaaa8f87c7e5f0b85c0e072f470bd1c2a8b163c582c58b05971e3c78f162c58b162c58b1e2fd8b162c5aaa2d16aa8b551ea8f5444baa2d5160c183060c183060c183060c183060c18306b2aaaaaaaaaaaaa837d8b4702c5c0f87c7e5f0b85caf4540703954d8f1e6c58f168b262c983060c183060c183060c1aaa8b16ecbbb1d8ecbaaa8f1e0c1d038183555555555555370f93c9e270b81c0e4e8e13a3855363c79b162c78f163c5fb164c593162c5932e4c2613263c78f547aa6d5112ea8b45aa4d26aa935552693060c183060c183060c183060c193061c183060c18359555555526caaaaaaa0df66e1f2793c4e17132704d1c29d1501c0e550b85c58b162d0160c183060c0183060c1a3368c7a31e8cda801326a08a0c1d0381835541555555552e17000582c06030b9702e5c1102e17166c58b163c58b164c58b162c580bf602c580a8f54da8025d5516aaa2d16a8b54583060c1830060c183060c183060c18306b2aa0aaaaaaaaaa837d970b8002c580b2e02c1625c140180c4400164c59300060c18300060c1833e6cf8f3e3cf9b0000555264c28015401554540000000000000000000593164c05fb000d803c00098a8f54d80002a2d526000828003060c18003060c1800c060b2a802a80882aaa837d800000000000000000000b162c58003060c18003060c1bb36ec7bb1eecd800028b16aa1400aa00aaaa20df6a000000000000000000000002c58b160000a8f54d800000002a2d5160c1830600000c18306b2a80002aaaaa837d803c0360000b162c580b00017ed51ea9b050000040001516a8b060c183018000c00183060d65510010055555506fb000000080000000000002e17164c59316083060c1830060c183068cda31e8c7a336a002c5a2a8030740e060d550555555554b85c00260b0180c2e5c0b970440b85c593164c5825cb972e2c0b80b26a8f54da8025d516a9354baa5c183060c1803060c183060c183595505555555541bec2e17164c593162c005fb266c98f263c993162c580a8f54da8025d516a935549aaa934983060c1830060c183060c183260c383060c18306b2aa0aaaa4d955555541becb85c00260b099309913265c12e0a00c06222a3d536a8897545aa4c183060c183060c183060d6555555555506fba753a9d4ea7539a68a80e072a972f55403c00000363c79b3e2e1933e2e19300061c187050000061c187660a00006664000000000000000b80f3d80006c78f3601305800030e0c3801c060000c3830ecc042000ccb4837dc6e3750f87d00050400000113a85d2b500000000000000000100100fa80a2e5c02878f1e3cb8173e2cf933e2cf93061c1870601c1835060c3a0c3830ecc84b4b4cccd100141411111080f3d80f1e00f2e3c78f1e3cb8171e2c7931e2c78f061c1870601c1830e1c1830e1c187061d99096969996906fb87d43ea2f17008a87c3eaa1f5544ea174ad510014141111109441500f1f5540000007c5b7267c5b7263c78f1e00000a0c3830e000c3830e0014cc00ccc80000000000000003c000079ec1600131e3c78f000060c000387061c18700061c18710026600665a41bec200000a87c6ea1f0fa08b800044ea174ad4000000000000000004000f1e0f3dc15503c78051b1e3cd9702e7c59f267c59f260c3830e0c038306a0c1874187061d99096969996906fba20028282222210078f079ec01e3c79b1e3cd9702e5c597265c597260c3830e0c0383061c383061c3830e0c3b3212d2d332d20df71ba87d45c02a2f17aa8bd5513a85d2b5440050504444425105404c9d551b1e3cd9f0f973e1f2f0b1e2c58baa162e858b162c187061c1835060c3a0c3830e0c3830eccb4b4cccccd5551515555552c2c98b363c79b160b2e2c162c58f17ec58b162c58b162c58b160c3830e0c1870e0c1870e0c3830e0c3830eccb4b4ccccb4837dc6e3750f87d42e17550baaa2f1150ba85d2b55554545555554b5509ea8 24 16777215 10 1023
def hc_55_3 : Nat → Nat := unpackHintV5 0xd7cd46d0e1bbcb0178c23633bd1d46b5e9cdaff97ca6fa40a0a19697226090c996874a6080cd9f774e6070e59a67326d615178588633536d464c81bb47454f42ad263b61d335717c2f857b265a4b220d131cf54615d5c80ef5b8054e6a000153 0x5cbd550000001b1e3cdc3170c9c3170c98003060c180280003060c1b305000033230000000000000005c079ec000363c79b00982c000183060c00603000060c183660210006641bed6a3750fa000a080000022750ba56a000000000000000000207d405172e0143c78f1e5c0b9f168c99f168c983060c1830060d060d4183060c18366425a5a66668800a0a0888884079ec078f007971e3c78f1e5c0b8f163c98f163c783060c1830060c183060c183060c18306cc84b4b4cc837dad43ea1f51700a87c3eaa1f5544ea174ad51001414111110941403c7d550000003716dc9b716dc98f1e3c780280003060c18003060c18005330033230000000000000000f00001e7b058004c78f1e3c000183000061c183060c00183060c400998019906fb5a0800002a1f50fa000089d42e95a80000000000000000001e415503c78051b1e3cd9702e7c5a3267c5a3260c183060c018341835060c183060d990969699965a20028282222210078f079ec01e3c79b1e3cd9702e5c597265c597260c183060c0183060c183060c183060c1b3212d525d699906fb5a8dd43ea2e015178bd545eaa89d42e95aa200282822222128280993aaa363c79b961f2f2c3e5e162c5d50b1742c58b160c183060d060d4183060c183060c183665a5a666666aaa8a8aaaaaa96164c59b1e3cd8b0597160b162c78bf62c58b162c58b162c58b060c183060c183060c183060c183060c183665a5a666641bed6a3750fa85c2eaa175545e22a1750ba56aaaa8a8aaaaaa96a8a81e3c78f170b1e2c98b27542c5d332ecc66332e4c9d5503060c183060c183060c18341835060d99999969699aaaaaaaa2a2aa5878f1e3c58f17ec58b1e3c593164c58b163cb8f0783c78f263c183060c183060c183060c183060c183060d999999696906fb5a87d43ea2f11513a85d43e1f550faa95aaaaaaaaa2a2aa5aa2a078faaa6e1f2edc3e5c78f1e3c58baaa162e162c58b16a0c1834183060c183060c183060c1835a5a66666641cd5454555555554b0b163c582c58b05971e3c78f162c58b162c58b1e2fd8b162c583060c183060c183060c183060c183060c1ad2d33333320df6b50baaa170baa87d43ea2f1150ba85d2b55454555555554b54541b1e3cd8b1e2e164c593162eaa9997663319971e3eaa8183060c183060c183060c1a0c1a8306ccccccb4b4b2d5555555151552c6c78f362c58f1e2c78bf62c98b262c58b265c984c264c78f1e0c183060c183060c183060c183060c18306ccccccb54935a41bed6a3750fa8bc4544ea1751389d544eaa56aaaaaaaa8a8aa96a8a80b85d19b463d18f466c99300a162c58b805c50503060c1830060d060d4183060c18366425a5a66668800a0a08888840b85c59b162c58f162c593162c58b1602fd80b16003060c1830060c183060c183060c18306cc84b4b4cc837dad46ea1f51700a85c2eaa175542ea174ad5100141411111094140002c98b26007cd9f1e7c79f3600004c9d5503060c18003060c1802833003305002300000000000000000b262c980bf6001b007800130183060c00183060c006030660066021041bed6a3750fa000089d42e8002820056a000000000000000000866e18f863e19b000000162c58b162eaa800183060d400000183060d98002801990634000000000000000000002c58b1600000c1830600000c18306cc0000cc837dad46ea1f4000000010ba85d2b5003c0360000b162c580b00017ec183060c0183000061c00183060d984008019906fb5a8dd43e8200000a000085d42e95a800000020000000000000b85c593164c5848cda31e8c7a3362c5805055403060c1830060c183060d060d41836642665a5a596880088a0a088840b85c593164c5845cb972e2c20a060c1830600c183060c183060d9909999906fb5a8dd43ea2e01513a85d45ea2f4ad4170b8b262c98b16002fd93364c7931e4c98b162c0060c1830600c183060c183060c183060d9909996a926b4837dad46ea1f51700a89d42ea2713aa89d54ad5100111445138222128280183060c183060c183060d99999906fb5a8dd43ea2f11513a85d2b5555555554b5454001b1e3cd8003060c18003060c1aaa972e0000ec9bb16ec5bb261400aa00aaa2a000000000000000001701e7b0000d8f1e6c0260b000547aa6c0010500000004baa2d5260c183060030180003060c1acaa022000aaaaaa0df60000000000000000000f41e3c78f1e3cb817060c1830600c183060d4115400b97464cf8b3e2d193060e81c0c1aaa0aaaaaaaa8f078005c2e030185cb8172e0880f3d80f1e00f2e3c78f1e3cb8171e2c7931e2c78f547aa3d4012eaa8f5551e8f545aa4c183060c1803060c183060c183060c18359550555555555541bec783c001e3c079702e1712e0a00c06220003c78f1e3c00183060c00183060d478f550000764dd8b762dd930a00550055545500000000000000000 24 16777215 10 1023
def hc_55_4 : Nat → Nat := unpackHintV5 0xe5fd46de75e2d7e1a5cf1633cac913c5b146bec5bbb81daaae766aa94d4aa261bb9b95b3917e868a35d27fb2a17869d26de6a1669dd25be6ae5479db4986bd42ddaa39366a341d462d31bb28094a2371261c4dc91581b30f598a050296000140 0x7cd9f1e7c79f360000002c98b26000a000c183060c1d550003060c1b3000500323300000000000000003c0360000b262c982c0026000c1830600c0001fb060c1836605000a005a45bed9a3750fa0800002822e0000ac0e0f50381d54000000000000000000170b8b262c98b0260c3830e0c18003f7030e0c3bb36ec7bb1eecd8306014a1c3870e1d0aa866425a45bee665a5a88008888a0a0840b85c593164c5813061c187060c001fb061c1870e6c3870e3c387060c187261c387161c380cc84b48b7db32d2d46ea1f51700a560f503a83c1eaa0f55551001111141410941402c98b262c98b264c58b26ccccb48b7db346ea1f51788a560f503aaaaaaaaaaa5aa2a0b97555000000363c79b3e2df933e2df9300061c1870a0000061c187550050005515000000000000000b80f3d80006c78f3601305800030e0c3801c060000c3830e9b547a80028200000093545ab2aa022000aa837daaaa00000000000000000020f54052e5c01478f1e3cb8173e2cf933e2cf93061c1870601c183a060c3c0c3830eaa82aaaaaaaa1c0e00070e01c38070381c062203cf603c7803cb8f1e3c78f2e05c78b1e4c78b1e3c187061c1807060c387060c387061c18747aa3d52e00a8f47aaa3d5549aa2d59554155555541bed5550e0700038700e1c0381c0e031410e0883c7aaa8000001f16fc99f16fc98f1e3c7800005030e0c380030e0c3a8002a802a8aa8000000000000000f00001e7b058004c78f1e3c00060007061c18700061c187040000151ea8f5000049aa2d59100155005541bed55500000000000000000007882aa0f1e00a6c78f365c0b9f167c99f167c9830e0c38300e0c1d03061e061c1875541555555506a87038001c38070e01c0e070188803c783cf600f1e3cd8f1e6cb8172e2cb932e2cb93061c1870601c1830e1c387065c1830e1c187061d36a8f54b802a5d2eaa9755526a8b565550555555506fb5554381c000e1c038700e070380c50438221326aaa6c78f367c3e5cf87cba2c58b55162d458b162c187061c183a060c3c0c3830e0c3830eaaaaaaaaaaaa1e0f070f01c3c0783c1e0f0781caa2c98b363c79b160b2e2c162c58f17ec58b162c58b162c58b160c3830e0c1870e0c1870e0c3830e0c3830e9b547aa2d16aa8b5552e88a8b545ab2aaaaaaaaaa837daaaa1e0f070f01c3c0783c1e0f0781ca8874551e3c78f168b1e2c98b26aa2c5a9f2efc7e1f2e4c9aaa830e0c3830e0c3830e0c3830740c18795555555555543c1e0f0783c1e0e1e038780f0395478f1e3c58f17ec58b1e3c593164c58b163cb8f0783c78f263c187061c187061c187061c1830e1c1830e1d1ea8f54ba22a4d516a8f47aaa3d5565555555555506fb55543c1e0f0783c1e0e1e038780f039510e8aa3c7aaa9f0f973e1f2e3c78f1e2c5aaa8b168b162c58b060c3c0c1d030e0c3830e0c3830e0c3aaaaaaaaaaaa870f01c3c0783c1e0f0783c1e072a8b163c582c58b05971e3c78f162c58b162c58b1e2fd8b162c583061c383061c3830e0c3830e0c3830e0c3a2d5545a2d551ea8f54ba22a2d516acaaaaa2d955555506fb555438780e1e03c1e0f0783c1e0f039510e8aa6c78f362c78b4593164c58b5553e5df8fc3e5c78f555061c187061c187061c187060e81830f2aaaaaaaaaa83543c1e0f0783c1e0e1e038780f03954d8f1e6c58b1e3c58f17ec593164c58b164cb930984c98f1e3c187061c187061c187061c1830e1c387064c1830e1d36a8f54ba22a4d516a9349aaa4d5565555555555506fb55543c1e0f0783c1e0e1e038780f039510e8aa170b9f367c79f1e7cd932600a2c58b1680b4505061c1870601c183a060c3c0c3830eaa82aaaaaaaa1c0e00070e01c38070381c062205c2e2cd8b162c78b162c98b162c58b017ec058b00187061c1807060c387060c387061c1874daa3d52e00a8b45aaa2d5545aa2d59554155555541bed5550e0700038700e1c0381c0e031410e088002c98b26007cd9f1e7c79f3600004c9aaa830e0c380030e0c385002a802a80280a80000000000000000b262c980bf6001b007800130187061c00187061c00e0304daa3d4000126a8b5000504019550055011041bed5550000000000000000003e6cf8f3e3cf9b000000162c58b162d55400187061c002800187061d55400001545540000000000000000000058b162c0000187061c0000187061d36a8f50000000045aa2d595500005541bed555007806c000162c58b0160002fd830e0c380c000e000c3830e9b547a8200000a00008b545ab2aa0a000c00aa837daaaa000000100000000000005c2e2c98b262c13e6cf8f3e3cf9b162c0141550187061c1807061c187060e81830f2aa0aaaaaaa8354381c000e07038700e1c0380c440b85c593164c5825cb972e2c038070e0c3830e0c03830e0c3830e0c3a6d51ea9700549aa2d52ea975655505555506fb55542e17164c593162c005fb266c98f263c993162c5800c3830e0c03830e0c383061c3870e0c983061c3a6d51ea9700549aa2d526935549aaacaaa0aaaaaaa0df6aaa87038001c0e070e0720e4c3807018a087044061c187061c187061c1874daa3d52e88a93545ab2aaaaaa837daaaa1e0f0783c1e0f0781ca887455 24 16777215 10 1023
def hc_55_5 : Nat → Nat := unpackHintV5 0xd3294ace9126c78dc1c458cdbee15eb7f5bbb14daaa6baa5a1b9409c7d4f9549cd8f597c865a408141467971f478b03072399e696e3362dda45916725285a448be7242659637b2ad307dcd2a059e205a6b1a697c116a400c2d4f074d380001d3 0x162c58b003e6cf8f3e3cf9b00000a00061c187000061c1875550e1d540145400154000000000000000151ea9b0000162c58b0058187061c0106aa87061c1870000000000005500555516fb550000547aa6c000058b162c016061c187007ec0106aa87061c1870d803c00100044001600b0038aa00aaaa2df6aa02200000000000000040000000b162c58023468d1801003060c18003060c1835554014501540058b162c00f9b3e3cf8f3e6c00002800183060c000183060c18355555005445a8002a80000000007c00000007806c000547aa6c14000010000162c58b058002c016060c1830060000fda0d55060c18306aa200200aaaa2df6aa000000000000000000170b8b162c58b0167cd9f1e7c79f36a000c1870f41e0e1c187061c1820c3830ea8a0aa82aaaaaaaa1c0e00070381c38070e01c062205c2ea8f54da8025c58b162c580b58187061c1830007ed41835550e1c187061c39b0e1c38f0e1c18306a1d555543870e2c3930e1c38b0e2c38701550555545bed5550ecaaa1c0e0021c140381c0e03038700e1c11151ea9b5444b8b162c58b162c5ac8355438b162c5aaaaaaaa8b7daad7abd5eaf35d1505c2eaf57954b97aaa01e000000b1e2c98280001b1e3cdc3070c3c3070c38013162c9b305000032330000000000000005c079ec000163c59300982c000d8f1e6c00e03000262c593660210005a45bed9a371ba87c3e800282000000560f503aa8000000000000000000201f50145cb8050b1e2c78b0262c5a8b163d1e3c78f2e05db833e1db833e1c98b164d99096969999a200282822222101e7b01e3c01e5c78b1e2c78b0262c58f262c58f1e3c78f1e5c0b8f063c38f063c393162c9b3212d2d2d22df6cd0fa87d45e2e01150f87d543eaa560f503aaa20028282222212828078faaa0000000005163c58f006e0db876e0db871e3c78f00262c593000a660064660000000000000001e00003cf602c580013262c78b1e000300038f1e3c78013162c982800533002d22df6cc100000543e3750f87d045c0001583d40eaa000000000000000000f60f0e0cfb7b01e3c1e7b82aa078f00a163c5931604c58b5162c9a6c78f365c0bf7067c3833e1c98b164d990969696916fb99a20028282222210078f079ec01e3c78b1e2c98b0262c593262c593266c78f365c0b97065c397065c393162c9b3212d2d2d22df6cd1ba87d45c02a2f17aa8bd54ac1ea0755440050504444425050070f5546c78f36fc7e5df8fcb8b1e2c98306a0c1834593164e063c18307540c1d03060c183060c1b32d2d3333335554545555554b030e0cd8f1e6c180cb830183163c593060c193062c183164c593063c1fb060c183060c183060c183060c1b32d2d332d22df6cd1b8dd43e1f50381d540eaa8bc452b03a81d555551515555552d51503c78f1e2c78b1e2c98b260c1c0c187061c187061c187aa060e8f976e370f9750e1c3870e870f554ccccccccb4b55555555551512c3c78f1e2c78b1e2c98b260c783f60c1870e0c3830e0c3830e0c1830e5c381c0e1c3930e1c38b0e1c3870eccccb48b7db32d2d43ea1f51788a560f07a81c0ea0f07aa83d5555555555554544b5454070f554dc6e5db8dcb8f1e3c783060d060d458f163c593164c183aaa060e060c183060c18306b4b4cccccccd5151555555552c0c1870603060c065c78f1e3c183162c183060c183264c58f163c593164c183060c183060c783f60c183060c18306835a5aa66665a45bed9a075540e07550f8dd43e1f51788a560707a81c0eaaa8a8aaaaaaaa96a8a8363c79b163c593164c593060c387063c1fb8187061c187061c183aaa3e5dd8ec3e5d43870e1c3a1c3d5533332d22df7332d2d5555555554544b1b1e3cd8b1e2c98b262c9830e0e061c187061c187075070e1c3870e1c387a999996916fb66668dd43ea2f114ac1ea07507a83d546c78f362c78b262c98b260c1870e0c783f60c3830e0c3830e0c1830e5c381c0e1c3930e1c38b0e1c3870eccccb48b7db32d2d46ea1f51788a560f503a83c1eaa0f55555555555554507a25aa2a02e177e6df8f7e3df9b0e1c028593164c5813060d41830683060c1c000e2828183060d99096969999a200282822222102e17066c183063c183061c18b262c98b0260c183260c583060c1830600fd80306003060c1b3212d2d2d22df6cd1ba87d45e2e01150381d540eaa5607503aaa20028282222212828000593164c00187061c06000c3830e8cda31e8c7a3360000a0001c3d5533003233050000000000000000000b262c980030e0c380030e0c38000000033002d22df6cc011ba87d00002b0783d40e07400015000b262c980030e0c3803f6000c3830e1b00780013005801c66005a45bed9808423750fa0000560f07a81c0e80028200a80000000000800000000 24 16777215 10 1023
def hc_55_6 : Nat → Nat := unpackHintV5 0xda799cd389bccc99bcc5a9bcc14918ba2dc7b3f18fb0bccdabf931a74d2ba0dd9c9e6c9c9a111794e94a8dfdbb8755aa7d667c77ed5e7101bb6a59aa5fc6a5587dd24dfaa146b1d23c2ea13495e62a12a122c9d21c01b2109ada09f1aa00027c 0x78f079ec01e3c78b162c58b0162c58b162c58b166c78f365c0b97065c397065c38b162c5b3212d525d69999aaa0aaaaa92aa18187066c78f360c065c180c18b162c583060c583160c18b162c5831e0fd83060c183060c183060c183060d99696999999aaaaaaaaa9aaa5878f1e3c58b162c58b162c18f07ec1830e1c187061c187061c183061cb870381c387161c387161c3870e1d99999999696aaaaa9aaaaaaa581830e0c060c180cb8f1e3c783160c183060c58b162c58b162c583060c183060c18f07ec183060c183060d69699999999aaaaaaaaa9aaa58d8f1e6c58b162c58b162c18707030e0c3830e0c383a8f9f3e7c3874387a99999999998d8f1e6c58b162c58b162c1830e1c18f07ec187061c187061c183061cb870381c387161c387161c3870e1d99999999696aaaaa9aaaaaa0f54b05c2e0cd83060c783060c383162c58b1602c183062c18b060c183060c01fb0060c0060c18366425a5a6666aa82aaaaa4aa8600162c58b00061c18700061c187468d1a300040f53300233310000b162c580030e0c3803f6000c3830e1b0078000b005801c660046660210aa0004aa00a0820001e01b000058b162c16000b00060c1830060000fd83060c1b308010023335510010002554005c2e2c58b162c05830e0c38306000fd830e0c387361c3871e1c383060c38b0e1c38b0e1c0664266665aa43ad554152555555430b162c58b162c58b162c5b3333333555553554b0b162c58b162c58b162c5b33322df6b4cd1ba87d45e229583d40eaaaaaaaaaa96aa2a8000162c58b005552e5c00002800d8f1e6c0058b162d9833e1d9833e1d540145400154000000000000002e03cf60002a3d536000828000000b162c5802c16000b1b1e3cd801c060008355438b162c5aa8088002aaa8b7daa800000000000000000083c58b162c580b50455002e5c58ba170b163c78f1e5c0b8b162c59f067c39f067c3aaa0aaaaaaaa8f078002c16172e05cb8170b8880f3d80f1e00f2e3d51e8f547a6d4012eaa8f5551e8f162c58b1602c58b162c58b162d61e3c78f2e05c7831e1c7831e1d06aa87162c58b55415555555516fb551e0f00078f01e5c12e0a02c16170b8880002c58b1600a3c7aa800005000f1e3c7800b162c5b3067c3b3067c3aa802a88b7da8002a8000000000000000f00001e7b0500000551ea8f0000058002c58b162c016018001c78f1e3c0106aa87162c58b10015500555516fb550000000000000000000788b162c58b0168aa0a003c78b1742e162cd8f1e6cb817162c58b3e0cf873e0cf875541555555552e0f000582c2e5c0b9702e17110078f079ec01e3c7aa3d1ea9b4da8025d552eaaa5d2e2c58b162c058b162cb8b262c58b162c5ac6c78f365c0b97065c397065c3a0d550e2c58b16aa82a976555555516fb552e0f000b9702e5c12e0a02c16170b8886c78f362c58b162c58b16aaa1c39f2ecc661f2e0c1d0381834183060c183060c183060c1aaaaaaaaaaaaaaa9b87c7e4f0b85c9d1c274700e072a830e0cd8f1e6c180cb830183547aa6d5506aaa0d06a8897162c58b060c18b062c183162c58b5818f07ec183060c183060c1830683554183060c1aaaaaaaaaaaa8b7daa9b87c0c1c034f07e4f28d1505c2e070395478f1e3c58b162c58b162d4183553e5cf87c3e5c387a0f070e0d061c187061c187061d5543875555555555550f0783c1e0f07838780e1e03c0e551e3c78f547aa3d5112e2c58b162c58b16b031e0fd83061c3830e0c3a0d550e0c3830e0c1830e5c381c0e1d43aaaaa870e1c5870e1c5870e1c3875555555516fb5555550f0783c1e43a2a0783c1e07070f01c3c2a8f1e3c78b162c58b162c5a870eaa7cbb31987cb830740e060c1834183060c183060c18306aaaaaaaaaa2df6aaaaaa3e1f1f97c2e172f470bd1c0381caa0c1870603060c065c78f1e3d5506835541aa8f547aa225c18b060c183062c58b162c58b162d6060c183060c1831e0fd83060c1a0d55060c18306aaaaaaaaaaaa2df6aa0d7c030703e1f1f97ca3454170b81c0e55363c79b162c58b162c58b555060cf973e1f0f970e1e83c1c3830e0d061c187061c1875550e1d5555555555543c1e0f0783c1e0e1e038780f03954d8f1e6d51ea9b5444b8b162c58b162c5ac0c3834187061d06aa87061c18707070e1c3870e875543870e1c38781875555555516fb5555363c79b547aa6d5112e2c58b162c58b16b03061c3831e0fd830e0c3a0d550e0c3830e0c1830e5c381c0e1d43aaaaa870e1c587261c387161c5870e1c3875555555516fb55543b2aa8783c1e0f21d1503c1e0f038387839070e1e1542e17162c58b1602cf9b3e3cf8f3e6d400387060e81c0c183060c1a00c183060c1515550555555554b85c00160b0b9702e5c0180c440b85c19b060c18f060c18706a8f54da8025d5506aaa0d062c58b162c0583060c583160c1ac0c1830600fd80306028306aaa0c383060c1aaa0aaaaaaaa8b7daa970b8000c18032e097050160b0180c44 24 16777215 10 1023
def hc_55_7 : Nat → Nat := unpackHintV5 0xd0d686cbd540c6bd46bfb9c1b9d978b0f639abb94fa46dd39e7d7c9566468f0d9685626b7f0996755e6b6ee19f64c6875e31a5578da94d828347a1783ebe3939795134c92c2dadc728714f216dc11b7d7c1266460f94b40ae92b04ad8f00012b 0x5c2e2c98b262c09a6d51ea9700564187061c1830007ec187061d50e8350e6c3870e3c387060c187261c9870e1c587161c3aaa870ea1d540554145bed5555555550e07000381c50438070181c38070e0882c98b262c98b269b547aa5d1159262c593543a0d5555516fb5555555cae572b89c2e5455a2b95caa5cbd550000000b162c58028001b1e3cdc3067c3c3067c3800b162c5b305000023330000000000000005c079ec000162c58b00582c000d8f1e6c00e03000162c58b6602100045bed699a3750fa000a08000001583d40eaa0000000000000000020081f50145cb8050b162c58b0162d162d458b1e3c78f2e05cf833e1cf833e1c58b162d99096969999a200282822222101e7b01e3c01e5c78b162c58b0162c58b162c58b163c78f1e5c0b8f063c38f063c38b162c5b3212d2d22df6b4cd0fa87d45c02a1f0faa87d54ac1ea0755440050504444425105403c7d5500000028000b162c58037067c3b7067c38f1e3c7800b162c58005330022c6998000000000000000780000f3d80b160002c98b162c58000c000e3c78f1e002c58b162004cc008b7dad33040000150fa87d00002b07a81d54000000000000000004003c82aa078f00a162c58b1602c5a2c5a8b166c78f365c0b9f067c39f067c38b162c5b3212d2d2cb334400505044444200f1e0f3d803c78f162c58b1602c58b162c58b162cd8f1e6cb8172e0cb872e0cb87162c58b66425aa4bad22df6b4cd1ba87d45c02a2f17aa8bd54ac1ea0755440050504444425105401c3d551b1e3cdbf0f977e1f2e2c58b160d060d4183162c58b818307540c1d03060c183060c1b32d2d3333335554545555554b030e0cd8f1e6c180cb830183162c58b060c18b062c183162c58b063c1fb060c183060c183060c183060c1b32d2d3322df6b4cd1ba87d40e075503aaa2f114ac0ea07555554545555554b5501ea81e3c78f162c58b162c58b07030e0c3830e0c3830f540c1d1f2e7c3e1f2e1c387543870e1eaa999999999696aaaaaaaaaa2a25878f1e3c58b162c58b162c18f07ec1830e1c187061c187061c183061cb870381c387161c387161c3870e1d999916fb5a665a5a87d43ea2f114ac1ea0750783d541eaaaaaaaaaaaaa2a25aa80f54070f554dc3e5db87cb8f1e3c7a83060d060c58b162c58b162c183aaa060e060c183060c18306b4b4cccc8b9a66a8a8aaaaaaaa96060c383018306032e3c78f1e0c18b160c183060c18b262c58b162c58b160c183060c183063c1fb060c183060c1835a5a666645bed699a075540e07550fa87d45e229581d40eaaa8a8aaaaaaaa96aa03d506c78f362c58b162c58b160c3838187061c187061c183aaa3e5cf87c3e5c3870ea870e1c3d5533332cb332d2d5555555555047e896363c79b162c58b162c58b061c1c0c3830e0c3830e0ea0e1c3870e1c3870f5333322df6b4cccd1ba87d45e229583d40ea0f07a83d551b1e3cd8b162c58b162c583061c3831e0fd830e0c3830e0c383060c3970e0703870e2c3870e2c3870e1c3b33322df6b4ccb54875a8dd43ea2f114ac1ea0750783d541eaaaaaaaaaaaaa8a0f44b5501ea80b85cf9b3e3cf8f3e6c38700a162c58b1602c1a0c1a83060c183070038a0a060c18366425a5a66668800a0a08888840b85c19b060c18f060c187062c58b162c0583060c583160c183060c1803f600c1800c18306cc84b4b48b7dad3346ea1f51700a81c0eaa07552b03a81d551001414111110944150000b162c580030e0c380030e0c39f367c79f1e7cd80000028070f554cc008ccc1400000000000001f00000058b162c00187061c00187061c00000001980116fb5a66008dd43e80001583d40e800020a80058b162c00187061c01fb00061c1870d803c0005802c00e330022df6b4cc04211ba87d00002b07a81d0005040150000000000100000000401f367c79f1e7cd8000000b162c5a8000003060c18307554000c18306cc0014008b1a6600000000000000007806c000162c58b058002c00183060c0180003f60c18306cc2004008b7dad3346ea1f4100000500002b03a81d54000000000000000004005c2e2c58b162c05830e0c38308187061cf9b3e3cf8f3e6c18300a0e1c3aa1c3855433212cb332d2d4400444450504205c2e2c58b162c05830e0c38306000fd830e0c387361c3871e1c383060c38b0e1c38b0e1c0664245bed69996a90eb51ba87d45c029583d40ea0f07aa83d55544004444505042510540002c58b16001c3870e001c3870ecc00cccc00000000001701e7b000058b162c0160b000363c79b00380c00058b162d98084001199aa808800012aa001e7b01e3c01e5c78b162c58b0162c58b162c58b163c78f1e5c0b8f063c38f063c38b162c5b3212d2d33335541555552554300f00001e7b058002c58b162c000600071e3c78f00162c58b1002660046662002aa0004aa80 24 16777215 10 1023
def hc_55_8 : Nat → Nat := unpackHintV5 0xd95d94d30d94cc89a1c8c8f0c24d9fc0547ebc70f9b75946b06dbba9c5aaa01e6a9af54a93e9c38d1db38306867bbdd2713aa169f1d25f6ea15815d64d5eae45f1db3f29b233f6cd2d4daa23a66a1e8d4619f52612f1c10dd94606cdc30001b3 0x5c2e2c98b262c0983360c1831e0c1832e000c1830e0c183060c1803062c1fb060c183060c1b321332d2d335521555555550305c2e2c58b162c05830e0c38300e0c583f60c1870e1cd870e1c7870e1cb80070e0c1830e1c3b32133332d2d5521555555550305c2e0c1831e0c183360c180032e2c58b162c0583061c183060c1803060c183060c183160fdb32120d696a9999aa90aaaaaaaa8182e17164c5931604c187061c1807061c1c8d1a34680707507a999099999182e17164c5931604c187061c1807060c387062c1fb0e6c3870e3c3870e5c00387060c1870e1d99099999696aa90aaaaaaaa0f50305c2e5c0b9702ecc84cccd548555540c170b9702e5c0bb32803ed999a3750fa562750ba83d40e808800888884a22a02e5d55400000058f164c280000d8f1e6e3838e1e3838e1c0098b164d540140005554000000000000002e03cf60000b1e2c9804c160009b547a800282000000c9b1e3cd801c060004c58b26a8741aaa80880022df6aaaaa800000000000000000083d5014b97005163c58f1604c58ba162c7c3c78f1e5c0bdb067c3db067c393162c9aaa0aaaaaaaa8f078005cb8172e04c16170b8880f3d80f1e00f2e3c58f163c5813162c793162c78f47aa3d52e00a8f47aaa3d556478f1e3cb8171e0c7871e0c787262c593543a0d55505555516fb555554783c001e3c07970260b1412e05c2e220f1eaaa00000000142c78b1e011c1c70f1c1c70e3c78f1e004c58b26a000aa002aaaa0000000000000003c000079ec160013163c58f00040000151ea8f50000640600071e3c78f00262c593543a0d4140019540116fb5555540000000000000000001e20aa83c78028b1e2c98b0262c5d0b164e363c79b2e05ed833e1ed833e1c98b164d5505555545aaaa5c1e00172e05cb8130585c2e2200f1e0f3d803c78f163c5931604c58b264c993165c58b264d36a8f54b802a5d2eaa975559363c79b2e05cb832e1cb832e1c98b164d50e8355541555545bed555552e0f000b9702e5c0982c504b8170b888a1c3aacf27979e4f2e6c78f360c1d03060e163c593164c59355060d5060c183060c183060c1aaaaaaaaaaaaa74709d1c1b87c9e4f1385c0e072a830e0cd8f1e6c180cb830183163c593060c193062c183164c5934daa3d506835541aaa974456418f07ec183060c183060c183060c18306a8341aaaaaaaaaa2df6aaaaa9b87c0c1c034f09e4f1385ca8a34070395478f1e3d5418353e5e592c3e5c58f163c593164c387a0e1c3c0d061c187061d438755061c1875555555555550f0783c1e0e1e038780f0783c0e551e3c78f163c58f164c59347aa3d52e88ac831e0fd83061c3830e0c3830e0c3aa1d06a0c1830e5c381c0e1c3930e1c38b0e1d55438750eaa1c387555545bed5555555550f0783c1e0f079510e81e07070f01c3c2aa870eaa3c78f1f3c9e5e793cb8b1e2c783060e060e8593164c183418306aaa0c183060c18306aaaaaaaaaaaaa3e1f2b470ad1c2b95c4e170381caa0c1870603060c065c78f1e3c18b060c183064c58f163c593164d06aaa0d06aa8f547aa5d1159060c183060c1831e0fd83060c183060c1aa0d06aaaaa836555545bed5555506ae018381f0f95cae270b9514680e072a9b1e3cd8306aaa7cbcb2587cb8b1e2c98b262c9870f41c387818706830e0c3a870eaa0c3830eaaaaaaaaa2d5550f0783c1e0e1e038780f0783c0e55363c79b163c593164c5934daa3d52e88ac830e0d061c187061c187543a0d41c1c3870e1c3870e1c3aa1d0ea1e061d555516fb55555554d8f1e6c58f164c593164d36a8f54ba22b20c1870e0c783f60c3830e0c3830ea8741a83060c3970e0703870e4c3930e1c38b0e2c3875550e1d43aa870e1d555516fb55555555543c1e0f0783c1e5443a0781c1c3c1c83870f0ab3cdcf1f3c7cf36170b8070e0a2c98b260c1d03060e1604c183060d14150060c18306aaaaaa82aaaa5c2e172e05cb800130580c062205c2e0cd83060c783060c383164c5931604c183064c18b060d36a8f54b802a0d06aa835559060c183007ec018300183060d5068355541555545bed555552e170001830065c0982c504b80301888008cda31e8c7a33600002c98b260014000c3830e00a1c3aa830e0c3aa8000280aaa80000000000000000b262c98026d51ea0000c830e0c380030e0c3aa1d06a000000000000aa008b7daaaaaa00002c98b26009b547a8000320c3830e00fd80030e0c3aa1d06a1b00780013005808800800071540116fb55555404400000000000000080000003e6cf8f3e3cf9b0000164c59300000a060c18300060d554183060d5401400055540000000000000001e01b0000593164c160013004daa3d41000005000064183060c0180003f60c18306a8341aaa8280030022df6aaaaa80000000000000000005c2f2cdcb1f2c7cb360c18028b262c98b0261c3d070e1e061c187060a82a030e0c3aaa0aaaaa8b5554381c000e1c038700e070380c44 24 16777215 10 1023
def hc_55_9 : Nat → Nat := unpackHintV5 0xdb416ed17274caf1a0c1e643bbf57cb2a255acb17ca35e559da56e93ae7e8d01ab86fd817dc64e77d57c6e825568917c5f3e5559856e4fb6744909ab43058139ce4e36fcb430ad942a5d9423d9a11d899417399410e9940a3dab067cf000019f 0x78faaa0168283c1e2c5d550b170b1602cf833e1cf833e1c78f1e3cb817162c58b585066426666a0a08800888884162c780b1602cb83c1e2c58b162c58b163c5fb1602c583161c583161c78f1e3cb817162c58b45ad2d5332803ed999a175542e17550f8dd43e1f4ac2e2750b85d41ea0740505044004444425109ea00785c58b1e3c58f17ee1604c58baaa500268f1f5546c78f365c0b93162c9b3067c3b3067c3b32803ee66505866880088a0a088840785c58b1e3c58f17ec5813162c5932e004c98f1e3cd8f1e6cb817262c593260c987260c987665007db32d2d3346ea1f4ac4ea1751389d544eaa83d40e80880088a0a08884a213d401c3d5503c2e0a00d363c79b3e2d1933e2d1932e05e063c18307540c1d030060c18306cca0b084cccd114140011111080c3830785c01970060cd8f1e6c183064c18b060cb817063c1fb060c183060c1830060c18306ccb4b4a00fb66668dc6ea1f0fa81c0eaa07552b13a85d40ea0740445050004444425101ea00783c78f1e3cb817060e060c38300e0c3830f540c1d280074f933e2cf8b3e4c387aaa66426666505888008888a0a0840783c78f1e3cb817063c1fb060c3870601c187061c183061cb80070e1c9870e1c5870e1c387665007db3332d2d43ea1f4ac4ea1750783d40e0750783d541eaa0220022222828212880f50070f55400d050783cf8b464cf8b464c78f1e3cb817060eaa818381830060c18306b0a0cc84cccd414110011111080c187018030600c1972e0f0783160c183060c98f1e3c79702e0c183060c183063c1fb0600c183060d696999401f6cccd03aaa0703aa87c6ea1f0fa562750ba81c1ea0703a0282822002222212880f5003c2e6c78f365c0b83061c3831e0fdc0c03830e0c38307554a001d3e4cf8b3e2cf930e1eaa999401f73333282c4400444451047e0840785cd8f1e6cb817061c1c0c03830e0c3832838070e1c3870e5332803ed99999a3750fa562750ba83d40ea0f07a83d4003c2e6c78f365c0b83061c3831e0fd8300e0c3830e0c1830e5c003870e4c3870e2c3870e1c3b32803ed9999696a3750fa562750ba83d40ea0f07aa83d5404400444451041e084a203d40170b8b262c98b0267cd9f1e7c79f36a000d0e1eaa8183060c1803818b060c1d503074cc84cca0b0cd10011141411108170b8b262c98b0260cd83060c783060cb8003060c383060c1830600c18b07ec183060c18306cca00fb665a5a668dd43e9589c4ea170ba81c0eaa075540ea0740440044505044425101ea00b85c58b162c580b061c1870601c18381830e7cd9f1e7c79f36a001daa060e8387aaa66426666505888008888a0a0840b85c58b162c580b061c1870601c18b07ec1830e1c39b0e1c38f0e1c397000e1c183061c387665007db3332d2d46ea1f4ac2ea1750783d40e0750783d541eaa0220022222828212880f5005c2e7cd9f1e7c79f360d005162c58b1602c387aaa060c1830600c183aaa060e06cc84b0a0cccd10014141111108170b83060c783060cd8306000cb8b162c58b0160c187060c1830600c183060c183060c583f6cca00fb41ad2d5333346ea1f4ac0eaa81c0eaa1713a85c2ea0707a81c0e808800a0a0888884a203d40170b8b262c98b0260c3830e0c0383061c383160fdc7cd9f1e7c79f36a001d060eaa8387aaa665007dccccca0b1100111114411f82102e17164c5931604c187061c1807061c1c1c3870e1c038328394cca00fb6666668dd43e9589d42ea0f503a83c1ea0f500170b8b262c98b0260c3830e0c0383061c383160fd87361c3871e1c3872e001c383060c3870ecca00fb66665a5a8dd43e9589d42ea0f503a83c1eaa0f550110011111441078212880f5000274e9d380070e1c380070e1c3b300333300000000000b262c1e170165c058b163c5fb162c58b162c58b0166c78f362c18b0e2c18b0e5c0b8b162c5b32d2d2133335555552155550303c1e2c78bf62c58f1e2c098b162c797001e3c7931e3c78f1e5c0b93162c98f063c38f063c3b321332d2d33552155555555030b163c058b0165c1e0f162c58b162c58b1e2fd8b0162c18b0e2c18b0e3c78f1e5c0b8b162c5a2d696a99909999aaaaaa90aaaa8181e17162c78f163c5fb1604c58b164cb8013263c78f363c79b2e05c98b164c983261c983261d99099969699aa90aaaaaaaa818187060f0b8032e00c19b1e3cd83060c983160c19702e0c783f60c183060c1830600c183060d99696909999aaaaaa90aaaa8181e0f1e3c78f2e05c18f07ec1830e1c1807061c187060c1872e001c387261c387161c3870e1d99099999696aa90aaaaaaaa8181830e030060c01832e5c1e0f062c183060c1931e3c78f2e05c183060c183060c783f60c0183060c1ad2d332133335555552155550303c2e6c78f365c0b830e0e0601c187061c1d48073e7cf9f0f5332133332303c2e6c78f365c0b83061c3831e0fd8300e0c3830e0c1830e5c003870e4c3870e2c3870e1c3b32133332d2d5521555555541ea06 24 16777215 10 1023
def hc_55_10 : Nat → Nat := unpackHintV5 0x82e40082ac0e81d43681d40081d40080d4407bd14173ba066e8d4b690d606006425ad94b527a184d155944fe0644c40e44c400448c0e43b43643b40043b40042b4403db141359a06306d4b2aed6021e6421e88d718997c0f465509557c000255 0x4c58f0064c58319184cd872e0b0e0e4460001c38000000f1e3c7800b262c983060c063c00183000060c183550015555555500000000000000060c38000c060003001e00f0000000018b060c183064c78f1e3c16001300060c183060c1831e0fd80c0006000c18306aaaaaa08003ed5554000000000000000000000001830000363c79b003e2e5933e2e593061c18000001c3830e0c3aa802aaaaaaa80000000000000003c0360001b1e3cd82c0026000c383001830000e1c00187061c18007000380070e1c387015410007daaaaaa803c0360001b1e3cd82c0026000c1870e0c783f600c1800070e000c3830e0c18300e000001c38072e00001c9870e1c5870e1c3875504001f6aaaaa876555000000000000000038000007cd9f1e7c79f3600002c98b26000001c383060c180030600003060d5401555555540000000000000001e01b0000593164c16001300066c183063c183006000000c18000030e0c183060c0183000061c0018b07ec183060c18306aa08003ed555555540000000000000000000259b963e58f966c000058b162c00183000061c187000000e1c18b01870eaa00aaaaaaaa0000000000000000f00d80002c58b160b000580030e0c380c000e000c583f60c1870e1cd870e1c7870e01c000003870000060c1870e1d5410007daaaaaaaa8000000000000000001b1e3cd80c586c78319186cb84c38f0e0e446002c58b16006c78f36000001c38003060c18003060c062c183000550005555555500000000000000007806c000060c18f060c19b0060c00000180000b162c582c0016000c187060c183018000c00183060c183060c583f6aa08003ed555555540000000000000000000239b8e3e38f8e6c0000593164c00000183061c187000000e1c187062a802aaaaaaa80000000000000003c0360000b262c982c0026000c3830e00c1800070e000c38303870e1c0e00070006007015410007daaaaaa803c0360000b262c982c0026000c3830e00c1800070e000c1870e0c583f61cd870e1c7870e01c0000038700e5c0000183061c3875504001f6aaaaa87655500000000000000003800000f00d80000b00098000c000e00aa08003ed555400000000000000993aaa0785c1405b0b1e2c58baa162e8580b363c79b3e0cf873e0cf872e05c58b162d99416109999a22828002222210593160f0b80b2e02c58b1e2fd8b162c58b162c580b363c79b160c587160c5872e05c58b162d996969401f6cccd1b8dd43e1f50b85d542eaa561750ba83d40e8088a0a000888884a213d400f078b170b163c5813aa162e94007a4c9d550f1e3c79702e4c58b26cc19f0ecc19f0ecc84cca0b0cd100111414111080f078b1e2fd8b163c78b0262c58b1e5c0078f1e4c78f1e3c79702e4c58b263c18f0e3c18f0ecca00fb665a5a6687d43e9589c4ea170ba87c3eaa1f5541ea0740440044505044425109ea0 24 16777215 10 1023
def hc_55_11 : Nat → Nat := unpackHintV5 0xba894bb27206ad454ba4e6189fa94f9a714e91fa1e8ccd4b84b6067f894b77720672354f6a1e0664e14f5fa94e57321e53d4d74e715946121840ad59384e1837dc1c37382931a96429920624654b1b424916154b0db618085159003a0600000e 0x3c78f1e000c061c00187061c00183000006e4cf8b3e2db930e1c001980199996968000000000000000078f1e3c0018f07ec1830e1c00187061c1830600001c9870e1c5870e1c3876607d8033332d2d03c01e0004c016007001801c0e000700080000000000000000000e1c000000001b8b6e4db8b6e4c78f1e3c00183000060c06000c18306b4b4cc00cccc000000000000000c18700000185c0018b060c183064c78f1e3c00183060c183060c783f6000c18306b4b4cc0fb0066660180003018003c01e0004c016003001810000000000000000000006c78f36000c383000187061c1830000000764cf8b3e2dd930e1c00198401999969680000000000000000d8f1e6c001870600030e0c38300003870e1c380cc0fb006666660d803c0009802c00e003003801c0800363c79b00060c387063c1fb00061c187060c1800007261c387161c3870e1d981f600ccccb54875a0d803c0009802c00e00300381c000e001000000000000070000000000593164c00f9b3e3cf8f3e6c0000387000060c18300018306000c183300332d2d3300000000000000000b262c98003360c1831e0c18000030e0c183060c0018b07ec183060c18306cc0fb00665a5a660d803c0009802c00603000180003001810000000000000000000002c58b16000c3830e000c061dd9b763dd8f766c00000018300e1c001980199996968000000000000000058b162c00187061c0018b07ec1830e1c39b0e1c38f0e1c0000183061c3876607d8033332d2d06c01e0002c016007001801c0e00070008000000000000000000007e6df8f7e3df9b0000162c58b000e1c000183060c00183000060c06cc000b4b4cccc00000000000000000c1831e0c1833600002c58b16000c187060c18300060c183060c183160fdb303ec01696999983600f000060000c06000b005800c00604000000000000000000000b262c980030e0c380030e0c666d98f663d99b0000060c0003870006610066665a5a0000000000000000164c59300061c18700061c181c3870e000c00e03303ec019999983600f0002600b003800c00e00702000593164c00187061c001830e1c18b07ec39b0e1c38f0e1c0000183061c3876607d8033332d521d683600f0002600b003800c00e07000380040000000000001c00000000000006607d80333306c01e0004c01600700181000000000000000000004c9800002c58b162c0058b000363c79b00d60cf87d60cf87162c58b55005555555500000000000000164c5803c036000b000160b0000000058f17ec58b162c58b1602c58000b26006c78f362c18b0e2c18b0e030003800b162c5aaaaaa82000fb5555000000000000000000000162c00000058f058f1e000004c98f1e3c78047071c3c7071c393162c9aa802aaaaaaa80000000000000003c1e00f0d80002c78bf62c58f1e0b0009800b162c07800000f1e00003c98f1e3c78f018001c0098b164c7831e1c7831e1d5410007daaaaaaaa80000000000000000007f67c182c3fb067d800078f000000162c58b058f17ec0058b0001e3c78f00067c3833e1c58b162d54001555555540000000000000058b1e000b058002c007803c0000000162c58b162c58b1e2fd82c0016002c18b0e2c18b0e3c78f1e030003800b162c5aaaaaa82000fb555500000000000000000000000162c000058f16000000f1e6c78f36011c1c70f1c1c70e4c58b26aa00aaaaaaaa0000000000000000f07806c360000b163c78b1e2fd80b160004c9800b162c0980000132604cb80000f1e3cd8f1e6c06000700262c593260c987260c9875504001f6aaa93655555000000000000000000000000e1c0000d8f1e6c02f8bbe4ef8bbe4c060c18003060000c18306aa00aaaaaaaa000000000000000c383007806c00060000c0600000001b1e3cd83060c983160c182c0026000c783f60c183060c1830060c00018700060c18355555504001f6aaaa0000000000000000000000c18000000f1e3c7801f172c99f172c9831e030e1c00000387061c18755005555555500000000000000007803c0001e3c78f058004c0018f07ec1830e1c06000700061c187060c1807000000e1c00003930e1c38b0e1c3870eaa08003ed5555555400000000000000000098b 24 16777215 10 1023
def hc_55_12 : Nat → Nat := unpackHintV5 0xe4eda4dad686d455a0ca9a6fc419a0ba5e6fb3cda4aa126fa381a49d598a9302968f40f08881b07ec66f7845a06e8a6f6809a05e1a7c5789a451618a470a9642a9183d7d4b35660630394b28220622e54f1ace0615914f0d461308194b000206 0xb16aaa0f0b85013858f16a8f1eaa2c099b1e3cdc3067c3c3067c39702e4c58b26aa8a0a802aaaa5c1e172e05cb800130585c2e2203c2e9b547ab22c58f1e2c78bf62c09aa4d16a2c58b265c99700261326aaa4c9a93551e3c79b1e3cd9702ea8741a93162c993064c393064c3aa83ec140555555552e0f001412e04c16132604cb8170b888a1c3aa8500381e173e2d1933e2d193363c79b2e05d5418354183060c0183060c1a282aaa0aaaa972e05cb817078005c2e03018880c3830785c01970060d36a8f541a0d5506aab26c78f360c183260c583065c0baa4d16a0c783f60c183060c1830600d506835060c18355555507d8280aaaa5c1e030600cb8002825c0b85c06031115418350783c2803c3c78f1e7c59f267c59f265c0b83418750e1d541807061c1875545054155550e07038700e1c000381c0e031101e0f47aa3d591e3c78f2e05d5268b5063c1fb060c3870601d50e835061c187060c1872e001c3aaa870ea1d543930e1c38b0e1c3870eaa0fb050155555554381c0050438070381c06070e01c38222870eaa0f0780382878f1e3cf8b464cf8b464cb817060d060c1aaa830060c18306aa0a8a88aaaaa3c1e172e05cb800170b80c062203061c01830065c1e0f41aaa8341aaa3d51eac83160c183060c98f1e3c79702ea9345a83060c183060c18f07ec1803541a0d4183060d5555541f60a02aaa832e00c180f07800a09702e170180c44060d5541e170a00f1b1e3cd9f167c99f167c99702e0c38354387550601c187061d5514150055554381c0e1c03870000e070380c440785d36a8f564d8f1e6cb817549a2d4187068300ea8741a830e0c38303870e01d50e8750e1c3870e030eaa0fb05015555541e174daa3d59363c79b2e05d5268b5060c387063c1fb0601d50e835061c187060c1872e1cb800703875550e1d43aa87261c387161c3870e1d541f60a02aaaaaaa8703800a08700e070380c0e1c0e01c387044468d1a30b85c8062c98b268751604c183060d41a0c01a0c18355514155553e6cf8f3e3cf9b0b85c2801c2c98b26a1c3aa8b0260c18306aa0c1a8300683060d551415055554b85c2e7cb8172e17000260b0180c440b85d36a8f564593164c5813549a2d419b060c18f060c19700060d554183506aa0c383060c1830600d506835062c1fb060c183060c1aa83ec140555555552e17001412e04c16030600cb803018887cd9f1e7c79f36170b85007858b162d5418351602c187061d4387550601c1a0c3aaa282a0aaaa870381c38070e0001c0e0701888170ba6d51eac8b162c58b016a8b45a830e0c38300ea8741a83160fd83061c387361c3871e1c3872e001c3aaa870ea1d54183061c3875507d8280aaaaaaaa1c0e002821c0381c0e03038700e1c1102e17162c58b1602cf9b3e3cf8f3e6c1c014a1c3aa83060c1830060c1a0c1835555541550545552e17000582c2e5c0b97006031102e174daa3d59060c18f060c19b060c0019755506a0c1aa8b162c58b016a8b45a83061c183060c1803541a0d4183060c183060c583f6aa0fb0501555506caaaa5c2e002825c01970060c0582c0603110f9b3e3cf8f3e6c2e170a00f0b262c9a8306aa2c09830e0c3a870eaa0c03830e0d55450540155550e07038700e1c000381c0e031102e174daa3d59164c5931604d5268b5061c1870601d50e835061c1a1c3870e1c03aa1d0ea0c0e1c380c3aa83ec1405555550b85d36a8f564593164c5813549a2d4187061c1807543a0d41830e1c18b07ec39b0e1c38f0e1c3970e5c00381c3aaa870ea1d54183061c3875507d8280aaaaaaaa1c0e002821c0381c0e030387038070e1c1102e174daa3d592e05d5268b52e05d50e8355507d8280aaaa5c2e002825c0b85c2e17110993000000000058b16002c58001b1e3cddb067c3db067c3800b162c5b32d2d003333000000000000000b262c00000058f17ec58b162c58b16006c78f362c18b0e2c18b0e002c58b16ccb4b40fb0066660d803c0160b0005800002c016007001810000000000000000000002c163c000058b00000264c00078f1e3c0098b164d983661d983661d980199696998000000000000000058f17ec58b1e3c0058b1600003c98f1e3c78f00262c5931e0c7871e0c7876607d80332d2d3303c01e0004c01600f078003c0003800c080000000000000000001e3c00000000058b000162c1600dc19f0edc19f0e3c78f1e002c58b16b4b4cc000cccc000000000000002c58f000000162c58b162c58b1e2fd800b062c38b062c38f1e3c7800b162c5ad2d3303ec019998160002c16000f0078000b005801c00604000000000000000000000b1e2c00162c000000078f000363c79b00262c593660d987660d98766100665a5a660000000000000000162c78f163c5fb00162c580000f1e3cd8f1e6c0098b164c983261c983261d981f600ccb54935a660d803c0009802c026130009800070018100000000000000000001c38000000001b1e3cdbf16fc9bf16fc98000c18300060c000183060d99696801999800000000000000187060000006c78f360c183260c58306000c783f60c183060c18300060c183665a5a07d80333306c01e003018000c00002600b001800c08000000000000000000 24 16777215 10 1023
def hc_55_13 : Nat → Nat := unpackHintV5 0xc3d5a4b9e27db38996a91a9ca1b9d89b15a9913e768e6cb488318f83852b8050cd7b8d3177b8f571519a6b158f67e0cd631d315e712b58358f5145bc4a55bc4331c93ed11837b5c735449c30e9172a69a020ae6f1a2da010726f09f1a000027c 0x6c78f362c58b162c58b160c3830e0c3830e0c1c0c18750e1c3870ebb2eec763b2f540c1d070f554ccccccccb4b55555555551512c6c78f362c58b162c58b160c3830e0c3830e0c583f60c1870e1cd870e1c7870e1cb870381c383060c3870eb48f7db333332d2d2b1788a85d42ea0f07a81c0ea0f07aa83d5555555555554544b5501ea8363c79b0683060c1abf2efc7e3f2e2c58b162c58b161c3d5503060c183060c183075540c1c0d99996969999aaaaaa2a2aaaa58d8f1e6c183063c183066c18306030197162c58b162c58b060c383060c183060c183060c183060c18b07ed691efb6641ad2d533332b1788a81d550381d542e2750b85d40e0f50381d555555515155552d5407aa0d8f1e6c58f164c593164c187061c187061c1830e1c18b07ee50e1c3870eb32ecc66332e0c1d55070f554b48f7dcccccccb4b55555555554133a258d8f1e6c58f164c593164c187061c187061c18707070e1c3870e1c383a83d4b48f7db33333332b1788a89d42ea0f503a83c1ea0f5546c78f362c78b262c98b260c3830e0c3830e0c1870e0c583f61cd870e1c7870e1cb870381c383060c3870eb48f7db333332d2d2b1788a89d42ea0f503a83c1eaa0f55555555555554507a25aa80f54001b1e3cd80070e1c380070e1c3b3003333000000000003c2e2cd8b162c78b162c98b162c58b017ec058b00d8f1e6cb817160c587160c587162c58b66425a5a66664a82aaaaaaaa8600163c593017ec003600f000261b1e3cd8013162c9801c060c800cc0420cc800154044155000200002c58b162ea00363c79b468d1a300162c58b6402006666007806c000162c58b0160002fd9b1e3cd80c000e002c58b16c8200400cccc80100050055554003c2e2c78b262c2478f2e2c22a363c79b2e05c98b164d1a3468d99099999981e17163c593162c005fb266c78f1e3c993162c5806c78f365c0b93162c993064c393064c3b321332d2d3325415555544eaaa860785c19b060c18f060c187066c78f365c0b83060c983160c183060c1803f600c1800c18306cc84b4b4cccc9505555555550c006c78f36000c3830e000c3830e80008d1a3461ea640066662000363c79b00061c187007ec00187061c3600f0002600b0038c800cccc0420800155540141040003c0360001b1e3cd82c0026000c1830600c0001fb060c18364100200666640200200aaaa800785cd8f1e6cb817061c187060c001fb061c1870e6c3870e3c387060c187261c387161c380cc84ccccb4b49505555555550c6c78f362c78b262c98b260cd83060c783060cb830180c1830e0c183060c183060c18b07ec183060c18306ccccccb4b4ccd555555555552c6c78f362c58b162c58b160c3830e0c3830e0c583f60c1870e1cd870e1c7870e1cb870381c383060c3870eccccccccb4b4d555555555552c6c78f360c1831e0c183360c1830180cb8b162c58b162c583061c183060c183060c183060c183060c583f6cccc835a5aa66666aaaaaaaaaaa96363c79b163c593164c593061c187061c187061c1c870e1d1a3468c1d41ea6666666666363c79b163c593164c593061c187061c187060c387062c1fb0e6c3870e3c3870e5c381c0e1c183061c387666666665a5a6aaaaaaaaaa83d52c6c78f366c78f366c78f36ccccccccd55555552c6c78f366c78f366c78f36b48f7db333332b1788a89d42ea0f503aaaaaaaaaaa5aa8aa14993550a01703c2eaa2c5aa2c58b1602cf833e1cf833e1cd8f1e6cb817162c58b4505554155552e5c0b9702e0f000582c2e17110593160f0b80b2e02c5a6d51ea8b45aaa2d556458f17ec58b162c58b162c05aa2d16a6c78f362c18b0e2c18b0e5c0baa1d06a2c58b16aaaaaa0fb05015554b83c162c0597000504b80b0585c2e222a8b16a0f078500f85a2c7a9326aa2c098f1e3c7c3067c3c3067c39702e4c58b26aa8a0a82aaaa3c1e172e05cb800130585c2e2203c1e8f547ab22c78bf62c58f1e2c09aa4d16a2c58b1e5c0078f5551e3d47aa8f263c78f1e3cb817543a0d498b164c7831e1c7831e1d541f60a02aaaaaaa8f07800a0970260b078f01e5c0b85c4451e3d541e0f017050b168b162d554580b1e3c78f3e0cf873e0cf872e05c58b162d541515055554783c2e5c0b97000160b0b85c44162c780b1602cb83c1e8b555168b5547aa3d59162c58b162c58b1e2fd8b016a8b45a8b062c38b062c38f1e3c79702ea8741a8b162c5aaaaa2d9541f60a02aaa8b2e02c580f07800a0970160b0b85c44 24 16777215 10 1023
def hc_55_14 : Nat → Nat := unpackHintV5 0xc30809c23036c23000c23000c1443bba11cdaf8ea1a845d2a135c49586ec9085408a957c817e467c414f74f5d36fb1516b012c6302005c41b05629864d1a4447297c3e124638a95a33f92c2c95d9277d461ffde01969a510863909f5a400027d 0x5c783169701ad9e2e6e261c0e0e6ce3c78f1e2c58b162c58b160c1d0381832e05d438755060c183060c183060c1a0c18306aaaaa8f55555555551f0f97cbe170b97a385e8e01c0e55591512e3c78f1ea0c1aaaaa83060c18f060c18f060c180c065d16aa8b162c58b162c58b060c3a0d55060c183060c183060c183060c183062c1fb55551efb555555555551a2a0f87cbe5f035f00c1c0b85c0e072a870f41e0e1c78f1e3e592cbcb2597163c58f555060c593164c187061d554387061c187061c1aaaaaaaaaaaaa1e0f070f01c3c0783c1e0f0781caab22a25c78f1e3d458b555264c58f163c593164d06aa87061c187061c187061c1a875543870e1c3870e1c38383870f030eaaaa3df6aaaaaaaab22a25c78f1e3d458b555264c58f163c593164d06aa87061c187061c187060c387062c1fb50eaaaaa1c3871e1cd870e1c7871e1c3872e1c0e070e0c1830e1c3aaaa8f7daaaaaaaa1d95550e8a81e0f0783c1e0f0781c1c3c1c83870f0aab22a25c78f1e3d16aa931e3c78f41aaa1c78f1e3d55547bed5555555e8a83e1f2f97cbe5f2f97caa0f0ba8b162c58b499300a162c58b8005c5051b1e3cd9702f1c1c70f1c1c70e2c58b16cc84b4b4cccd100141411111080f0b8b362c58b1e2c58b262c58b162c05fb0162c0363c79b2e05c583161c583161c58b162d691efb425a5a6666562f17008a85c2eaa175542ea17507a81d551001414111110944150000b1e2c982c0140000000993aaa363c79b00262c5933e0cf873e0cf876400660a00660000000000000000163c593017ec003600f000261b1e3cd8013162c9801c060b48f7d80330108332a00011389d42e174001410041ea075500000000000000000100000a0000002c58b162c5d55001b1e3cdc3070c3c3070c3800b162c5b200050033330010c000000000000000000162c58b0000363c79b0000162c58b5a47bec00019999508000000021750ba83d40eaa00783c0361b000058b162c058000bf66c78f36030003800b162c5ad23df60a001400cccca84000014117000085c4ea170ba83d40eaa0000000800000000000800785c58f164c58b0017ee51e3c78f268b1601415506c78f365c0b93162c9b306cc3b306cc3ad23df721332d2d334400445104ce088840785c58f164c5845c78f2e2c20a363c79b2e05c98b164cb972e5d691efb42666666562e01513a85d45e2f517aa0f503aa81e17163c593162c005fb266c78f1e3c993162c5806c78f365c0b93162c993064c393064c3ad23df684ccb4b4ccac5c02a2750ba89c4eaa275541ea075544004451144e08884a20a801e175060c18306870e0146c78f365c0bbf16fc9bf16fc983060c1c000e2828183060d99096969999a200282822222101e17066c183063c183061c19b1e3cd9702e0c183260c583060c1830600fd80306003060c1ad23df684b4b4ccccac5e2e01150381d540eaa89d42ea07503aaa20028282222212882a000363c79b00061c1870180030e0c3a800000023268c5a3168c9870f554c800cccc14000000000000023000000d8f1e6c00187061c00187061c00000001691efb006666005400022750ba83d40e800020a800d8f1e6c00187061c01fb00061c1870d803c0009802c00e2d23df600cccc0420a800044ea1750783d40e074001410054000000000040000000100000a0000006c78f367c59f267c59f26000c183060c1d550003060c1b2000500333300000000000000003c0360001b1e3cd82c0026000c1830600c0001fb060c1835a47bec400801999950800002822e000113a85d40e0f50381d54000000000000000004003c2e6c78f365c0b830e0c38306000fdc0c3830ea1c3870e1d060c029d93762dd8b764c2aa1691efb9099999696a200222228282101e17363c79b2e05c187061c1830007ec187061c39b0e1c38f0e1c183061c9870e1c5870e02d23df684ccccb4b4ac5c02a2750ba83d40ea0f07aa83d555440044445050425105406c78f362c78b262c98b26a0c183060d3e5cf87c3e5c387aaa060c183060c183818b060c1d503074ccccccb4b4cd5555555151552c6c78f362c78b262c98b260cd83060c783060cb830180c1830e0c183060c183060c18b07ec183060c18306b48f7db3332d2d332b1788a89c4ea170ba81c0eaa075540ea07555555555454554b5501ea8 24 16777215 10 1023
def hc_55_15 : Nat → Nat := unpackHintV5 0xa541aa9b527c96294a8f3dbb8ee8158ecc078e78158d98388d7c078d60078c584287514282b9267bb5c1750daa6e9d9c63cab55ce9b852fa7c4dd14a4939264201ce3c995a35adbb2f05aa243eb21cbde0123aa10af1d20026b3000009000000 0x58ba170b160f0782813262c58b160a8a80b1e3c78f8e0e3878e0e3872e05c58b162d555555055554783c2e5c0b97000160b0b85c44581412e0f07a8b55555162c58f162c58f162c59316a2c5aaa8b262c58b1602fd80b16020d550e3c78f1e5c0b8b062c38b062c38b162c5aaaa8f7da0aaaaaaaaa5c140783c00162c05970160b0b85c440a00000000163c58f555264c00078f1e3cf833e1cf833e1c0098b164d45400001555400000000000001600000045aaa4c58f163c05fb00100044001e00f0002620d550e3c78f1e004c58b260070182aaa8f7d802a80882a8000000000000000000707efd8707ec7821c5a0fda673dfb0e6e2e03262fdc99c002800000058b162c00058b5551e3c78f00061c187162c58b5511efb005000555500000000000000580000000000000116aa8b162c58b000041aaa1c78f1e3c000058b162d55547bec0001555560011001001e00f0000000116aa8b162c58b0160002fda0d550e3c78f1e030003800b162c5aaaa8f7d8800802aaa800000000004000000003c7d0f878f0783c14058b163c58f54501608f1e3c7db076c3db076c39702e4c58b26aaaaaa82aaaa3c1e172e05cb800130585c2e222c0a0970783d458b555264c58f163c58297554b8f1e3c78b02e02c9a0d550e3c78f1e5c0b93162c9972e5cbaaaa8f7da0aaaaaaac0a0970783d458b555264c58f163c58b0017ed49aaaaa93263c793363c78f1e3c78f1e2c58b0106aa871e3c78f2e05c98b164c983261c983261d55547bed0555526caaaaa970501e0f000982c264c2644c99702e17110183a0703060f07828070e3c78f1f6c5db276c5db265c0b83060c182a2a030183060c1835555554155551e0f0b9702e5c000b85c060311160504b83c1ea0d55554183063c183063c183061c1a2d55263c78f1e5c0b83060c983160c1a8306aaa0c383060c1803f600c1800c18306aaaa3df682aaaaaaaa970501e0f0001830065c0b85c0603110280000000078f1e3d18b464d18b464c00187061d554387000061c187515000005555000000000000005800000116aa931e3c78f0041aaa1c187061c00187061c00000000000155547bec015554016000010b8022d55263c78f1e00835543830e0c3803f6000c3830e200088003c01e0004c016007155547bec01555404400000000000000080000000a0000001e3c78f003e2cf933e2cf93060c18300001fb060d554183060d4401400155540000000000000160011001001e00f0000000116aa931e3c78f058004c0106aa83060c1830060000fd83060c1aaaa8f7d8800802aaa800000000000000000070f41e0e1c1e0f050060c78f1e3e58b964e58b964cb817061c1875450060830e0c3aaaaaaa0aaaa870381c38070e0001c0e0701888b08282972e0f07a2d55263c78f1e5c0ba8306aaa1c3830e0c38306000fd830e0c3a87555550e1c38f0e6c3870e3c38f0e1c183061c9870e1c5870e02aaa8f7da0aaaaaa1d95550e0a01c0e00070381c06070e01c3822030740e060c78f1e3cf87cb9f0f97163c58f5550e1c593164c183060c183555060c1834183060c1aaaaaaaaaaaa8f87c7cfc1f4707e3f1385c0e072aac8a8971e3c78f45aaa4c58f163c593164d41aaaaa83060c783060c783060cb830180c1830e0d06aa83060c183060c183062c1fb060c183060c1aaaa8f7daaaaaaaaaaa8d1507c3e572b89c2e060e01ab80703954387a0f070e3c78f1f2c965e592cb8b162c58306aaa2c58b160c3830eaaa1c3830e0c38341875555555555550f07838780e1e03c1e0f0783c0e55591512e3c78f1ea2c5aaa8b262c58b162c58b16835543830e0c3830e0c383160fd83061c3a87555550e1c38f0e1c38f0e1c3970e070387060c1870e1d55547bed55555555550e8a81e0f0783c1e0f0781c1c3c070f0aa5c 24 16777215 10 1023
def hc_55_16 : Nat → Nat := unpackHintV5 0xd619b2cae6cdc5e540c00578b73a33b22146ab35bba5f94fa161269a15d394257c8e397b850e4b7f2d787662337149466cb12665adc160954659a9bb53b97c4aba404461963ae2603489962b0a60248d9f1b0e6014a59a0e2d9e044e78000113 0x64d8f1e6d12e8a2c78b26a9345a8b262c9830e0c3aa1d06a0c3830e0c38343870e1d50e8750e1c38707070e1e061d1efb5555555555559363c79b44ba28b1e2c9aa4d16a2c98b260c3830ea8741a830e0c383061c383160fd87361cd870e1c7871e1c3aaa870ea1d543970e070387060c1870e1d1efb555555555555543c1e5443a0783c1e0f0781c1c3c1c83870f0aac9b1e3cda25d14d8f1e6d5268b5363c79b543a0d51efb5555555554dc3e5453a2793c9e4f2793caa0f078b162d5162c99300a162c58b805c5050f1e3c79702f1c1c70f1c1c70e2c58b16cc84b4b4cccd100141411111080f078b1e2c58b1e2c58b262c58b162c05fb0162c01e3c78f2e05c583161c583161c58b162d1efb5a425a5a6666562e0150b85d542eaa85d42ea0f503aaa2002828222221282800058f163c0001400000993aaa1e3c78f00262c5933e0cf873e0cf874600660a00660000000000000000163c58f017ec001e00f000260f1e3c78013162c9801c0608f7dad00330108332a000113a85d0005040107a81d540000000000000000000a000000002c58b162c5d55000f1e3c7c3070c3c3070c3800b162c5a3c6800280199980000000000000000000058b162c000078f1e3c000058b162d1efb5a0000666654000000021750ba83d40eaa00783c01e1b000058b162c058000bf63c78f1e030003800b162c5a3df6b4200400cccca8400001400010ba85d41ea0755000000040000000000000f078b1e2c78b0878f1ea8f1e2c580505540f1e3c79702e4c58b26cc1b30ecc1b30eb2c84ccb4b4cd100111414111080f078b1e2c78b0878f1e3c584143c78f1e5c0b93162c9972e5cba3df6b484ccccccac5c02a2750ba8bd45ea0f503aa81e0f163c58f162c005fb1e3c78f1e3c78f162c5803c78f1e5c0b93162c993064c393064c3a3df6b484ccb54935a66562e01513a85d44e275513aaa0f503aaa20022288a2704442505003c1e0c183541830e1c02878f1e3cb8177e2df937e2df93060c183801c50503060c1b3212d2d33334400505044444203c1e0c783060c783060c3831e3c78f2e05c183064c18b060c183060c01fb0060c0060c18347bed69096969999958b80540e075503aaa2750ba81d40eaa8800a0a0888884a0a0001e3c78f00061c18700061c18700500000464d18b462d1930e1eaa9180199982800000000000000000078f1e3c00187061c00187061c000000011efb5a006666005400022750ba83d40e80002a001e3c78f00061c187007ec00187061c1e00f0002600b00388f7dad00333301082a000113a85d41ea074001410054000000000040000000002800000000f1e3c79f167c99f167c98003060c18307554000c183068c001400cccc0000000000000000f00780003c78f1e0b00098003060c180300007ec183060d1efb5a100200666654200000a000089d42ea07503aa80000000000000000001e0f1e3c78f2e05c187061c1840c3830e1c38754387060c029d93762dd8b764c2aa1659099999696a200222228282101e0f1e3c78f2e05c187061c1830007ec187061c38f0e1c38f0e1c183061c9870e1c5870e023df6b484ccccb54875a562e01513a85d41ea0750783d541eaaaa20022222828212828078f1e3c58f163c593164c18306a83067cb9f0f87cb870f5540c183060c1830703060ea8183a6666665a5a66aaaaaaa8a8aa961e3c78f163c58f164c593063c183063c183065c180c060c187060c183060c183060c583f60c183060c18347bed69999969699958bc4544ea1750381d540eaa81d40eaaaaaaaaa8a8aa96a8a81e3c78f162c58b162c58b061c187061c18707030e1c38754387765dd8ec765ea8183a0e1eaa999999999696aaaaaaaaaa2a25878f1e3c58b162c58b162c187061c187061c18b07ec1830e1c38f0e1c38f0e1c3970e070387060c1870e1d1efb5a6666665a5a562f1150ba85d41ea0750783d541eaaaaaaaaaaaaa2a25aa2a078f1e3c1835068306fcbbf1f8fcb8b162c58b162c5870f5540c183060c183060c1d5503070347cd332d2d33335555545455554b0f1e3c783060c783060c783060c06032e2c58b162c58b160c187060c183060c183060c183060c183160fda3df6b4ccb4b4ccccac5e22a075540e07550ba85d40ea07555555545455554b54540f1e3c78b1e2c78b262c9830e0c3830e0c3830e0e0e1c3aa1c3b32ecc66332e0c1d55070f554b2cccccccb4b55555555551512c3c78f1e2c78b1e2c98b260c3830e0c3830e0c38383870e1c3870e1c1d41ea47bed699999999958bc4544ea17507a81d41ea0f550f1e3c78b1e2c78b262c9830e0c3830e0c383061c383160fd871e1c3871e1c3872e1c0e070e0c1830e1c3a3df6b4ccccccb54875a562f11513a85d41ea0750783d541eaaaaaaaaaaaaa8a0f44b54540f1e3c78f1e3c78f1e3c7a3df6b4ccccccac5e22a2750ba83d40eaaaaaaaaaa96a8a8 24 16777215 10 1023
def hc_55_17 : Nat → Nat := unpackHintV5 0xe7ed9ede6a61d7a9b0ce2661c8e550bf765cb8cdaaaf266aaa0d46a321bb9df94a996126923dc98b71b385498a7af2967449aa6aa26a65894660f12659edc154d5464de9bb471db33d068635bdd22b3aa123f1d2196ea11225d2076eae0001db 0x1701e7b000058f164c0260b000061c18700380c00018706070e1c3801c0e0000c00e01b1e3cd81080013162c987060c3870e1c383cf603c7803cb8f163c58f1604c58b1e4c58b1e3c187061c1807060c387060c387061c1870e1c3870e01c3870e1c3870e1c181c38701871e3c78f2e05c7a3e1e8f898b164c383061c3870e1c0780000f3d82c00262c78b1e0000c1800070e0c3830e000c38300e00070e1c387000600700400878f1e3c0098b164c383061c3870e1c078f079ec01e3c78b1e2c98b0262c593262c593260c3830e0c0383061c383061c3830e0c3870e1c38700e1c3870e1c3870e0c0e1c380c39b1e3cd9702e5d2f174bc4c58b261c1830e1c3870e2c98b262c98b260c3830e0c3830e0c3830e1c3870e1c3870e0c3870e1c1830e4c58b261c1830e1c3870e2c98b262c98b260c3830e0c3830e0c1870e0c583f61cd870e1c7870e1cb870381c383060c3870e4c58b261c1830e1d0f0743c1c3870e1c3870e1c3870e1c1830e1c3870e070e1c381c3870e2c5d0b162e0264c141e174505162c58b405b706dc3b706dc39b1e3cd9702e2c58b16aaaaaa82aaaa5cb8172e05c1e000b0585c2e22320f0b825c1459b162c58f162d55458b516aa2c98b162c58b545a2d405fb0162c0363c79b543a0d4b817160c587160c587162c58b47bed55541555555552e0f1412e0002c580b2e02c16170b8881400000000a4c9aa8b1e2c9801f067c39f067c39b1e3cd8013162c980280a802aaa80000000000000320000002c78b26a9345a80bf6001b007808800800004c363c79b543a0d40098b164c00e03047bed555005501105500000000000000000000000a0000162c58b00162d554d8f1e6c01b836e1db836e1c58b162c554014001555400000000000001900000000000000162c58b545a2d40000d8f1e6d50e8350000162c58b47bed555000055556401e01b001000440000000162c58b545a2d4058000bf66c78f36a8741a80c000e002c58b168f7daaaa0a000c00aaaa00000000001000000000f1f43c7938058b050785d415058f164c582dc1b70edc1b70e6c78f365c0b93162c9aaaaa8f55055554b9702e5c0b83c00260b0b85c44641e1704b828b1e2c9aa4d16a2c12e3c79754ba5d458170164cd8f1e6d50e8352e05c98b164cb972e5d1efb55550555555590785c12e0a2c78b26a9345a8b16002fd93364cd8f1e3c7931e4c9aaa9326a4d5458b1601b1e3cdaa1d06a5c0b93162c993064c393064c3a3df6aaaa0aaaaaaaa97078a097000260b099309913265c0b85c44060e8183070070e0a0f0bb716dc9b716dc99b1e3cd9702e8a0a0c18306803060c1835555554155552e5c0b9702e0f000b85c060311190785c12e0a0cd83060c78306aaa0c1a8355061c19b1e3cdaa4d16a5c0b83060c983160c183060c1aa0d06a00fd80306003060c1a3df6aaaa0aaaaaaaa97078a097000060c019702e170180c440a00000000462d193462d193363c79b0050e1d54187061c00187061c014054015554000000000000019000000363c79b549a2d400187061d50e83500061c18700000000000047bed5550055550064000000d8f1e6d5268b500061c187543a0d401fb00061c1870d803c04400400002600b00388f7daaaa00aaaa0220000000000000004000000000500001b1e3cd801f167c99f167c983060c1800306aaa0c183062a00a000aaaa00000000000000c803c0360020008800000006c78f36a9345a82c0026000c18306a8341a80300007ec183060d1efb55544004015554000000000000000000387a0e1c3c00c18283c2edc5b726dc5b7266c78f365c0ba82a030e0c38304187061d555547aa82aaaa1c38070e01c0e00070381c0622320f0b825c14d8f1e6d5268b52e05c187061d50e835060c001fb061c1870e6c39b0e1c38f0e3c3875550e1d43aa83060c3930e1c38b0e1c047bed55541555555550e071410e0001c0e070181c38070e0880c1d03060e3e1f2e7c3e5cd8f1e6d438755163c593164c59355060d4183060c183060d060c1aaaaaaaaaaaa9f4707cfc1b87c7e3f1385c0e072ab26c78f3689745163c593549a2d4593164c19b060c18f060d554183506aa0cb830180c1830e0c183060d506835060c183062c1fb060c183060c1a3df6aaaaaaaaaaaaa9b87ca8a344f2789c2e060e01a780703954387a0e1c3cdc6e5db8dcb9b1e3cdaa8306a2c58b162c58b16a1c3aa830e0c3830e0c38341875555555555550e1e038780f0783c1e0f0783c0e5564d8f1e6d12e8a2c58b16a8b45a8b162c5830e0c3aa1d06a0c3830e0c583f60c1870e1cd870e1c7870eaaa1c3a87550e5c381c0e1c183061c38747bed55555555555550f079510e81e0f0783c1e07070f01c3c2a9b1e3cd8b162c58b162c5838183060e9b976e371b9750e1d54183060c183060c183418306aaaaaaaaaaaaaaa6e1f2793c2e17274709d1c0381caac9b1e3cda25d14183063c183066d5541a8306aa0c1830180cb8b162c5aa2d16a2c58b160c187060c183541a0d4183060c183060c183060c583f68f7daaaaaaaaaa8365555370f9514689e4f034f00c1c0b85c0e072a870f41c3879b8dcbb71b97363c79b5060d5458f164c593164d438755061c187061c187061c1aaaaaa3d55555550e1e038780f0783c1e0f0783c0e55 24 16777215 10 1023
def hc_55_18 : Nat → Nat := unpackHintV5 0x8ecb29c3d1e520c1c9cffa19b7b252b3b4d915beaef0d8b1a967ad2b318394d6f7f28ae864e5404cfa79a9a12a3ca686cf94434209217d090fe735e75e2563667229750f8ca8149c4d79a421c33e8e9892457cf3e25799b0d7b50843ca0405a7100000b4 0x780c0183060c183c78003062c78b262c098b161c38b164c383060c1830060c183060c183060c18b060c19b1e3cd9702e7d3f1f4fc4c58b260c183065c1e00172e05cb8130580c06170b803c783cf600f1e3c58f164c5813162c993264c597162c993066c183063c183065c00183065c197060c183065c183060c1830e0c183060c1803060c183060c183062c1fb060c183060c19b1e3cd9702e5d2f174bc4c58b260d070341c0c183065c1e00172e05cb8130580c18032e00c06170b82c98b262c98b260cd83060c783060cb830180c1830e0c183060c183060c18b07ec183060c183064c58b260d070341c0c18306ac3ab0eac3ab0e4c38b0e0c18301ab0603060c1ab0eac3972e1c3870e1c38000000b162c58003060000c3830e01c38000030187363c79b9ecfa7b3e00162c58b0e0c187000000000000000b80f3d80002c58b1600b05800030e0c3801c060000c583f60c1870e1cd870e1c7870e0001c3807000000060c1870e1cd8f1e6c08400058b162c383061c3a1e0e8780000000000000000000e0f0e1c3801c3972e001c38b162c58b0162c18b160c18b160c3830e0c0383061c383061c3830e0c38f1e3c79702e7d3f1f4fc2c58b161c1830e1c0e00070e01c38070381c06070380f3d80f1e00f2e3c58b162c580b162c58b162c58b061c1870601c1830e1c1830e1c18b07ec1830e1c38f0e1c38f0e1c397000e1c38f0e3c3870e1c38f0e1c3870e0c1830e1c38f1e3c79702e3d1f0f47c2c58b161c1830e1d0f0743c1c0e00070e01c38070381c06070e01c38070383c7870e1c3870e0000000c18000b162c580000070e0c3830e000c580c3879ecfa7b3e1e3c78f00162c58b0e0c1870000000000000001e00003cf60b00058b162c58000c000e0c3830e000c583f60c1870e01c000003870e3c3870e3c3870000060c1870e1c400878f1e3c0058b162c383061c3a1e0e8780000000000000000001e0700e1c3870e0f1e001c38b162c58b0162c18b160c18b160c3830e0c0383061c383061c383061c1830e6c78f365c0b9f4fc7d3f0b162c587060c387038001c38070e01c0e070181c0e00f1e0f3d803c78f162c58b1602c58b162c58b162c187061c1807060c3870e1c197060c387062c1fb060c3870e6c3870e3c3870e5c003870e5c3970e1c3870e5c3870e1c383060c3870e6c78f365c0b974bc5d2f0b162c587060c38743c1d0f07038001c38070e01c0e070181c38070e01c0e0b162c58b162c5830e0c3830e0c383160fd83061c387361c3871e1c3872e1c0e070e0c1830e1c38b162c587060c38743c1d0f070e1c3870e1c3870e1c387060c3870e1c0e1c381c3870e0002c58b16000c183060c1972e000001c38003060c180030603060c000d8f1e6c0058b162f7b8edee38183060c000000000000002e03cf600003060c783060cd800030060c0000000197162c58b00582c0001830e0c183060030180003060c183060c18b07ecd8f1e6c0840001a0e0683858b162c183060c0000000000000000001e0c1e3c58b162c580b060c0180c18306005cb8b161c38b0e2c583060c1830060c183060c183060c183063c78f1e5c0b8b162c59f4fc7d3f03060c18f078002c16172e05cb8030185c2e03cf603c7803cb8f060c18f063c183063c19b060c00197060c183063c183060c1831e0c78b162c58b0162c58b162c58b160c187060c1830600c183060c183060c183060c183060c583f63c78f1e5c0b8f47c3d1f0341c0d070b162c583060c18f078003c780f2e00cb8030602c16030185c2e7bb1bec59031c60003cf62c58b16000c18f1e0c18306000001c38003060c18003060c062c1830001e3c78f00162c58b71ce38183060c000000000000000780000f3d80306000000c183063c183063c000016000b162c58b00060c380c00060c18306000c183060c183062c1fb10021e3c78f00068381a0e162c58b060c1830000000000000000000780c58b162c580b0603060c180306003c78b161c38b0e2c583060c1830060c183060c183060c183066c78f365c0b8b162c59f4fc7d3f03060c197078002c16172e05cb8030185c2e00f1e0f3d803c78f060c18f063c183066c19b060c01800cb832e0c183060cb83060c183065c197162c58b1602c58b165c593162c58b162c1830e0c183060c0183060cb830e0c183060c183060c183060c18b07ecd8f1e6cb8172e978ba5e068381a0e162c58b060c1832e0f000b9702e5c01970060c0582c06030b85c060c18f060c19b060c180c065c58b162c58b162c1830e0c183060c183060c183060c183062c1fb068381a0e162c58b060c183a61e987a61e987074c180c1830587161c183060e987a61cb970e1c3870e1c078000002c78b2600c18000030e0c38070e00000c3830d8f1e6e3b1e8ec780098b164c383061c000000000000002e03cf60000b1e2c9804c160000c3830e0070180003061c383160fd87361cd870e1c7871e1c3800070e01c000000183061c387363c79b021000262c5930e0c1870e8783a1e00000000000000003800001c07870e1c00e1cb97000e1c58f163c5813162c183162c783061c1870601c1830e1c1830e1c187061c78f1e3cb8173e9f8fa7e262c5930e0c1870e0700038700e1c0381c0e030381c079ec078f007971e2c78b1e2c098b163c98b163c7830e0c38300e0c1870e0c1870e0c1870e0c583f61c7870e1c7870e1cb872e001c0e1c38f0e3c3870e1c38f0e1c3870e0c1830e1c38f1e3c79702e3d1f0f47c4c58b261c1830e1d0f0743c1c0e00070e01c38070381c06070e0700e1c38070383c7870e1c3870e0000000000c18b1e2c780000070e0c3830e000c38323b1e8ec7878f1e3c0098b164c383061c000000000000000780000f3d82c00262c78b1e0000c1800070e0c3830e000c1870e0c583f601c000003870e3c39b0e1c38f0e3c38700e5c0000183061c38710021e3c78f00262c5930e0c1870e8783a1e00000000000000003800003c783cf61c03870e1c383c780070e2c78b262c098b160c18b164c1830e0c38300e0c1870e0c1870e0c1870e0c583f61cd8f1e6cb8173e9f8fa7e262c5930e0c1870e0700038700e1c0381c0e030381c01e3c1e7b0078f1e2c78b262c098b164c98b164c9830e0c38300e0c1870e0c1870e0c1870e0c583f61cd870e1c7870e1cb80070e1cb872e1c3870e1cb870e1c387060c1870e1cd8f1e6cb8172e978ba5e262c5930e0c1870e8783a1e0e0700038700e1c0381c0e030387038070e1c0381c00164c59300061c18700061c187aa00aaaa0000000000 25 33554431 10 1023
def hc_55_19 : Nat → Nat := unpackHintV5 0x83145a3fd86c9f13364f1d1b2754ce73a0a271c79a2edd29a969e92b335966d878cd0bcd1bd59bd2b2b4366d456d2c9e69134a8f29a1b3e50fb04a66f3394330f2295a4f8caba0604bea7a1f05bc0db174460b3362702560ef7228403de0134336000268 0x13a74e9c00187061c00187061ea802aaa80000000000593160000002c78bf62c58b162c58b00061c187060c387060c38700061c187000000000000363c79b168b85a2e00162c58b0e0c1870000163c5fb162c78f00162c580000f263c187061c00187061c1830e1c1830e1c00000000000078f1e3c0098b164c7a3e1e8f8383061c0058b1e0000002c58b162c58b163c5fb00060c387060c387061c18700061c187000000000000168b85a2e1e3c78f00162c58b0e0c1870000162c78f163c5fb00162c580000f1e3c187061c00187061c1830e1c387064c1830e1c000000000000d8f1e6c0098b164c9a4e26938383061c000000187061c00187061c0000000000383061c000000187061c01fb00061c1870d803c0009802c00e0007060c3810800000000000000000000132600000b162c58b00162c000183060c00183060c183060c183060cd8f1e6c00fa7e3e9f858b162c183060c000000000000005931600f00d8002c000582c0000000163c5fb162c58b162c582c0016000c183060c183060c1830600c0001fb060c183363c79b168b85a2e100200162c58b060c183000000000000000000000162c000000582c78000013260c18306000c183060c183060c183063c78f1e007d3f1f4fc4c58b260c183060000000000000000f07803c360000b1e2fd8b163c782c0026002c58b01e000003c780000f263c183060c0180003f60c183060c183060c183063c78f1e2004004c58b263d1f0f47c0c183060000000000000000000003c78000000b162c162c0058b000060c18300001fb060c183060c183060c1831e3c78f003e9f8fa7e162c58b060c18300000000000000162c78002c16000b001e00f0000000058b162c58b162c78bf60b00058003060c183060c183060c180300007ec183060c5a2e168b878f1e3c40080058b162c183060c0000000000000000000000058b0000163c58000003c783060c18003060c183060c183060c19b1e3cd801f4fc7d3f13162c983060c180000000000000003c1e01b0d80002c58f1e2c78bf60b0009800b162c0980000132604cb80000f1e3c183060c0180003f60c183060c183260c383060c183066c78f362004004c58b264d271349c0c1830600000000000000000000f00d80000b00098003060c180300007ec183060c400800183060c000000000000009930e1c3870e1c1e170060c05830e2c78b162c3870e1c58b0e1c580b061c187060c01830e0300e0c3830e6c78f367d3f1f4fc5c0b8b162c587060c3870381c38070e0001c0e070181c0e0b262c1e170165c058b163c5fb162c58b162c58b0160c3830e0c1870e0c1870e0c18003f60c3830e1cd87361c3871e1c7870e1c587161c3870e1c5870e1c387060c187161c387161c3806c78f362d170b45c5c0b8b162c587060c38743c1d0f070381c38070e0001c0e070181c38070e01c0e03c1e2c587162c78b0261c3870e2c5870e0c1800f064c9870e1c3870e0c3830e0c03830e0c3830600c187078f1e3cb817262c593bedfafb7e0e0c1870e07000381c0e1c038700e030381c0783c58f17ec58b1e3c5813162c58f2e003c78f263c187061c1830007ec187061c1830e1c1830e1c38f0e1c38f0e1c183061c987261c387161c5870e1c7871e1c3870e1c7870e1c3870078f1e3cb817262c5931e8f87a3e0e0c1870e8783a1e0e07000381c0e1c038700e03038700e1c0381c1e3c3870e1c3870160c01830783c58b0e1c3870e1c58b0e2c580b060c380c18030e0c38300e0c3830e7d3f1f4fc3c78f1e5c0b8b162c587060c3870e01c3807038001c0e070181c0e0b163c1602c580b165cb83c1e2c58b162c58b163c5fb1602c18b060c387060c3870e1c187061c1830007ec187061c38b0e1c3870e1c587161c3870e1c787361c3871e1c7870e0c1830e2c3930e1c38b0e2c387005a2e168b878f1e3cb817162c58b0e0c1870e8783a1e0e1c038700e07000381c0e03038700e1c0381cf62c7dec18e30785c58b1e3c58f17ec38b0262c5870e1c3870e0c18013063c7870e1c3870e0c3830e0c18003f61c187061c1830060c386c78f365c0b93162c9f371ce38383061c381c000e07038700e1c0380c0e0701e17162c78f163c5fb1604c58b164cb8013263c78f061c187060c001fb061c187060c387060c3870e6c3870e3c387060c187261c387161c387261c9870e1c387261c3870e1c0363c79b2e05c98b164c9a4e26938383061c3a1e0e878381c000e07038700e1c0380c0e1c038700e0702e172e05c187061c1830007ec187061c39b0e1c38f0e1c183061c9870e1c5870e01702e1c1830e1d0f0743c1c0e00070381c06070e01c38070385cb83060c183060000002c78b2601c3800003060c180030600003060cd8f1e6cfa7e3e9f80098b164c183060c000000000000002e03cf60000b1e2c9804c160000cd83060c783060000c1803000000061c183060c1800c060000c583f60c183060c183363c79b021000262c593068381a0e060c1830000000000000000000183c18306003065cb8003062c78b1e2c098b161c38b163c383060c1830060c183060c183060c183063c78f1e5c0b9f4fc7d3f13162c983060c18f078005cb8172e04c16030185c2e03cf603c7803cb8f163c58f1604c58b1e4c58b1e3c18f060c18f060c19700060c18f063c183060c18f060c183060c383060c1830600c183060c183060c18b07ec183060c183063c78f1e5c0b8f47c3d1f13162c98341c0d0703060c18f078003c780f2e04c16030600cb8030185c2e0f1e0c183060c1800000000070e2c78b1e000c180003060c18000c1833e9f8fa7e1e3c78f00262c593060c1830000000000000001e00003cf60b00098b1e2c78000300000060c18f060c18f060c00001870600c1800030e0c18306000c583f60c183060c18310021e3c78f00262c593068381a0e060c183000000000000000000 25 33554431 10 1023
def hc_55_20 : Nat → Nat := unpackHintV5 0x8ac2d343a46f607357cf9569177b53db83de75bc4968d4a2616714cf326d475862352bd5d6d59c33b2b9154149acb89bc24546f1bc2133914eddef06da2532fa9ca158b9248fe71e40add11d20cd8c2f98454a33620ce610d28cf84219cc13eb4800027d 0x3060000002c58b162c5870e1c3870e000c383000038700061c187363c79b3e9f8fa7e00162c58b0e0c187000f80000000000000000002c58b1600000c1870e0c783f600000c3830e0c18300e000000001c5870e1c5870e1c387363c79b0000162c58b0e0c1870e8783a1e00783c0361b000058b162c058000bf60c1870e0c783f600c1800070e000c3830e0c18300e000001c38072e00001c587261c387161c5870e1c387363c79b100200162c58b0e0c1870e8783a1e00000000e0000000000700001e17163c593162c005fb0e0c18f1e3c793062c580070e01c3870e1c060c387063c1fb0e0c03830e0c383061c383061c39b1e3cd9702e4c58b267d3f1f4fc1c1830e1c0e00070381c381c039f0e01c06070380f0b8b1e2c98b00e5c78f2e2c038070e0c1870e0c783f60c03830e0c3830e0c383060c397000e1c3930e1c38b0e1c3970e5c3870e5c3870e1c387363c79b2e05c98b164cb972e5c383061c3a1e0e8781e17163c593162c005fb266c78f1e3c993162c5800c1870e0c783f60c03830e0c383061c383061c383060c397000e1c3930e1c38b0e1c3930e4c3870e1c3930e1c3870e1c387363c79b2e05c98b164c9a4e26938383061c3a1e0e878381c000e0703870381c3930e01c06070e0700e1c3807038006c78f36000c3830e000c3830f5401555400000000000f0b8b362c58b1e2c58b262c58b162c05fb0162c0061c1870601c1830e1c1830e1c187061c181c38700e1c3870e1c3870e1c3870e1c061cd8f1e6cb817168b85a2e162c58b0e0c1870e1c38700163c593017ec003600f00026030e0c00061c18700380c0180001c3870e0070380700d8f1e6c0098b164c0840383061c3870e1c00600002c58b162c3870e000c383000e000c3830e6c78f368d1a346002c58b161c1830e00f00d80002c58b1602c0005fb061c1803000380030e0c3830003800070e001c3870e1c0363c79b100200162c58b0e0c1870e1c3870785c58f164c5807063c7971601c0e1c3830e0c38300e0c3830e0c3830e6c78f365c0b93162c9a3468d187060c383c2e2c78b262c5800bf64cd8f1e3c793262c58b00187061c1807061c187060c387060c38706070e1c03870e1c3870e1c3870e1c9870e1c380c39b1e3cd9702e4c58b264d271349c1c1830e1c3870e6c78f366c78f360c3830e0c3830e0c3830e0c3870e1c3870e1c3870e1c1830e6c78f361c1830e1c3870e6c78f366c78f360c1870e0c783f60c3830e0c3830e0c1830e5c381c0e1c3930e1c38b0e1c3870e6c78f361c1830e1d0f0743c1c3870e1c3870e1c3870e1c1830e1c3870e070e1c381c3870e0c193260c1830601c380b0e0f0b83060c18b160c183162c58b0160c060c0183060c1830600c183060cfa7e3e9f8d8f1e6cb817162c58b060c1832e5c0b9702e0f000582c06030b85c164c583c2e02cb80b160cd83060c783060c583160c183060c583060c183061c18b1e2fd8b162c58b162c580b060c18b062c183060c183060c183060c183007ec018300183060cd8f1e6c5a2e168b8b817068381a0e162c58b060c1832e0f058b0165c0001830065c0582c06030b85c060c183162c1830783c038701e1c583163c183264c183060c5813060c18306030600c1830060c183063c78f1f3d9f4f67c5c0b93162c983060c18f0785cb8172e0004c16030185c2e03c1e0c783060c783060c383163c5fb162c78f1604c183064c18b060c58b163cb800f1e0c183060c18f1e0c18f060c1831e4c783060c1803f600c1800c183060c183060c183063c78f1e5c0b8341c0d0713162c98f47c3d1f03060c18f078000c18032e04c160f1e03cb8030185c2e03063c783060c183c1e02c38070e2c583162c583060c183062c0583060c1803060c060c180c060c183060c78f1e3cfa7e3e9f8b817162c58b060c1831e0f0b9702e5c000582c06030b85c162c780b1602cb83c1e0c583060c183062c18b060c183063c183063c183061c18b162c58b162c58f17ec580b060c18b062c183060c183060c183062c187060c183007ec018300183060c5a2e168b878f1e3cb817068381a0e162c58b060c183165c058b01e0f0001830065c0582c06030b85c162c183060c1830785c03870261c58f160c1831e3c183060c5813060c18306030600c18300060c183066c78f373d9f4f67c5c0b93162c983060c1970785cb8172e0004c16030185c2e03c2e0cd83060c783060c383162c78f163c5fb1604c183064c18b060c58b164cb932e004c264c183060c183264c183260c183063c78f060c183007ec018300183060c183060c183060cd8f1e6cb817068381a0e262c593269389a4e060c1832e0f0001830065c0982c264c0997006030b85c0b85c19b060c18f060c187065c0b83060c983160c183060c1803f600c1800c183065c0b8341c0d0703060c1970b8000c18032e05c2e030185c2e13260000000000b162c0058b000061c187060c387060c38700061c187363c79b3e9f8fa7e00162c58b0e0c18700000000000000164c58000000b1e2fd8b162c58b162c00187061c1830e1c1830e1c01fb00061c1870d803c0160b0005800002c0160070d8f1e6c5a2e168b80058b162c383061c0840000000000000004e0000000b058f0000162c00000993000061c18700061c187060c387060c3871e3c78f00262c59346a391a8e0e0c1870000000000000000163c5fb162c78f00162c580000f263c187061c01fb00061c187060c387060c38707803c0009802c01e0f000780007078f1e3c0098b164c7a3e1e8f8383061c0840000000000000004e00000f1e0000000002c58000b160b00060c387060c387061c187000061c1873e9f8fa7e1e3c78f00162c58b0e0c18700000000000000162c7800002c2e002c58b162c58b163c5fb00060c387060c387061c187007ec00187061c160002c16000f0078000b005801c168b85a2e1e3c78f00162c58b0e0c1870210000000000000001380000002c78b00058b00000001e3c000187061c06000c3830e0c1870e0c1870e6c78f36004c58b268d472351c1c1830e00000000000000002c58f1e2c78bf6002c58b00001e3c7830e0c3803f6000c3830e0c1870e1c383260c1870e1b00780013005804c2600130000e1b1e3cd8013162c99349c4d2707060c381080000000000000009c0000 25 33554431 10 1023
def hc_55_21 : Nat → Nat := unpackHintV5 0xe67f78e0119bd6ba56d015a9c94db2bf8273b63653ac9e669dfba994c24e8b76537d977877299b6d8a686d5c0b6d40076d140b6c203d6c04076be8076acc476421ab5d59b253d6614ac24540ce7d315fdc28264e1f024910879f09f5a400027d 0x3c1e2c78b162c78b162c98b162c58b017ec058b0018f07ec1830e1c1807060c387060c387061c187060c1872e001c387161c5870e1c387161c3870e1c38b0e1c38b0e1c3870e3c78f1e5c0b8b45c2d170b162c587060c38743c1d0f07038001c38070e01c0e070181c38070e01c0e000b1e2c780000306000004c9870e1c3870e0c061c00187061c0387001e3c78f00262c5933e9f8fa7e0e0c1870000000000000000163c58f017ec001e00f00026031e0fd83061c380030e0c3801c0600c18300000e4c3870e2c3870000e1c0380070e1c78f1e3c0098b164c0840383061c3a1e0e878000000000000000000018300000000162c58b162c3870e1c38700063c061c3800070e000c3830e3c78f1e7d3f1f4fc002c58b161c1830e000000000000000000002c58b1600000c783f60c1870e00000c3830e0c183000000000e2c3870e2c3870e1c38f1e3c780000b162c587060c38743c1d0f003c1e00f0d80002c58b1602c0005fb063c1fb060c387018001c00187061c1830601c0000038700000e2c3870e2c3870e1c38f1e3c78801000b162c587060c38743c1d0f0000000070000000000000783c58f163c58071e3c783060c78f162c0038700e1c3870e03061c1830e0c03830e0c383061c383061c38f1e3c79702e4c58b267d3f1f4fc1c1830e1c0e00070381c38070e01c06070380f078b1e2c78b00e3c78f1e2c038070e0c783f60c1870e0c03830e0c3830e0c383060c397000e1c3930e1c38b0e1c3970e1c3970e1c3870e3c78f1e5c0b93162c9972e5cb87060c38743c1d0f03c1e2c78b1e2c5800bf63c78f1e3c78f1e2c58b0018f07ec1830e1c1807061c187060c3870e1c193060c387060c1872e001c387261c387161c387261c9870e1c387261c3870e1c3870e3c78f1e5c0b93162c99349c4d2707060c38743c1d0f07038001c0e070e070387261c0380c0e1c038700e07078f1e3c78f1e3c18f07ec1830e1c187061c187061c183061cb870381c387261c387161c3870e1c78f1e3c383061c3a1e0e8783870e1c3870e1c3870e1c383061c3870e070e1c0e1c387162c387161c58b0783c01830264c58b162c01830603060c160b160c183060c183060c183060c0183060c18f1e3c7a351c8d471702e2c58b160c183063c1e172e05cb8000b0580c06170b80c1870060c01970783c183160c183060c183060c18b162c78b162c78b162c98b062c183060c18b162c58b017ec058b00183060c183060c783f60c0183060c183060c183060c18341c0d070f1e3c79702e2d170b45c2c58b160c183060cb8030603c1e000b1602cb80b0580c06170b801c3800000000b1e2c783060c183064c980030603060c00000183060c78f1e3cfa7e3e9f80098b164c183060c000000000000001830e0000030b8003160c183060c98b1e2c780bf6000300006030007803c000980c183060c183063c1fb00060c18300180c01a0e0683878f1e3c0098b164c0840183060c000000000000000002f6fbf723c01c2c1fb0628cf7efdc6c3971262c38311800070e0000002c58b16000b162c183060c183060c183018f07ec00183000060c1831e3c78f0066162c58b060c18300000000000000060c38000000000000003160c183060c58b162c5800003060c183060c18f07ec0000183060c1a0e0683878f1e3c000058b162c183060c1830e0003018000c007803c0000000062c183060c18b162c58b0160002fd83060c183060c18f07ec06000300060c183068381a0e1e3c78f100200162c58b060c183000000000000e000000003c7870e3c38f1e0f078030602c58b1e2c783060c060c05803060c183060c183060c1830600c183060c78f1e3d1a8e46a38b817262c593060c1831e0f0b9702e5c000982c06030b85c060c380c01830060cb970783c18b060c183064c58f163c5803065c183060c1971e3c78f1605c0593060c183060c1831e0fd830060c183060c183060d070341c3c78f1e5c0b93162c9972e5cb83060c183061c0600c1803065cb83c1e0c583060c183262c78b1e2c5800bf60c193060c183060c183060c9931e3c99b1e3c78f1e3c78f162c5800c183060c183063c1fb0600c183060c183064c187060c183060c1a0e0683878f1e3cb817262c593269389a4e060c183065c018301e0f000982c264c2607264cb8030185c2e03061c180c18301971e3c78f062c183060c1931e3c78f060c183060c1831e0fd83060c183060c18341c0d070f1e3c783060c1835e0c060c183c38f0ebc3af0ebc3af0e0c18306bc3af0e0f0b83062c58b162c19326001c38b162c58700161c0e1c0387061c1870601c1830e1c1830e1c187061cd8f1e6cb8173e9f8fa7e162c58b0e0c1870e0700038700e1c0381c0e030381c0785c59b162c58f162c593162c58b1602fd80b16003061c3831e0fd8300e0c1870e0c1870e0c3830e0c1830e5c397000e070e1c587161c3870e1c5870e1c3870e2c3870e2c3870e1c39b1e3cd9702e2d170b45c2c58b161c1830e1d0f0743c1c0e00070e01c38070381c06070e0700e1c3807038002c78b260b00060c00000009930e1c3870e1c1870600030e0c38070e006c78f36004c58b267d3f1f4fc1c1830e00000000000000002c78b2602fd8006c01e0004c060c387063c1fb00061c18700380c01830600001c987261c387161c5870e0001c3807000e1c39b1e3cd8013162c9810807060c38743c1d0f00000000000000001c000 24 16777215 10 1023
def hc_55_22 : Nat → Nat := unpackHintV5 0xcd4113c5fdd1c1b113ba6dd1b1364ea7fe4e9ec64e958e4e8e49d189fd13878c9c84bcb48061177d90b479411471c5df68b2455ad37854659b4b0e564469a93da1b233d6732a8a5320f266124fa909164e000245 0x5c079ec000363c79b00982c000d8f1e6c00e03000363c79b02100000000000000000079ec078f007971e3c78f1e5c0b8f163c98f163c78f1e3c79702e3c18f0e3c18f0e3c78f1e5c0b8f47c3d1f0f078003c780f2e05c2e170b85c2e00f00001e7b058004c78f1e3c000600071e3c78f0010021e3c78f000000000000000001e3c1e7b0078f1e6c78f365c0b97165c997165c99b1e3cd9702e5c1970e5c1970e6c78f365c0b974bc5d2f17078005cb8172e05c2e170b85c2e0b262cd8f1e6c582cb8b058b163c5fb162c58b162c58b162c59b1e3cd8b062c38b062c38b162c59b1e3cd8b45c2d170b162c59b1e3cd8b162c169c589d3a74e2c58b169d3a74e9d3a74e3c78f1e2c78bf62c58f1e2c98b262c58b1e5c783c1e3c7931e3c78f1e4c58b263c18f0e3c18f0e3c78f1e4c58b263d1f0f47c3c78f1ead3ab4e4c58b263c78f07ab1e2b4ead3ab4ead38b163c582c58b05971e3c78f162c58b162c58b1e2fd8b162c58b062c38b062c38f1e3c78b162c58b45c2d170f1e3c78b162c58b5e2c162c583c78f1ebd3af4e2c58b16bd3af4ebd3af4e6c78f362c58f1e2c78bf62c98b262c58b265c984c264c78f1e6c78f364c58b264c1930e4c1930e6c78f364c58b264d271349c6c78f369d3a74e4c58b264c99309a726274e9d3a74e9d385c2e2cd8b162c78b162c98b162c58b017ec058b00b817160c587160c587162c58b2e05c5a2e168b858b162cb85c00162c05970160b0b85c2e17000593164c05fb000d803c00098004c58b260070180013162c98108000000000000000000000b162c5800000000b162c580000b162c5800b162c580070e1c380070e1c3d50055550000000000003c0360000b162c580b00017ec06000700162c58b100200162c58b00000000000000000164c593000e1c387000e1c387aa00aaaa00000000000b85c593164c58132e5cb971605c05932e05c98b164cb972e5cb817262c5932e5cb970b85c593164c58b0017ec99b263c98f264c58b1601702e4c58b264c1930e4c1930e5c0b93162c99349c4d27170b8004c1613261309932e05c2e170b82c5870e2c58b0e04c9803060f0b8301830060c58b162c180b060c183060c183060c1830600c183060d1a8e46a38d8f1e6cb817162c58b060c1832e5c0b9702e0f000582c06030b85c061c183c2e00cb803062cd8b162c78b160c183060c18b160c18b060c183164c58b162c583060c583160c180bf602c5800c783f60c183060c1830600c183060c183060c183060cd8f1e6c1a0e06838b817168b85a2e162c58b060c1832e0f01830065c00058b0165c0582c06030b85c00e1c00000000183264c183060c58f164c00001830018306000c183067d3f1f4fc6c78f36004c58b260c18306000000000000000c383000000163c593060c193062c183017ec003600f00180c0006000013018f07ec183060c18306000c183060030181b1e3cd8341c0d070013162c9810803060c180000000000000000000000070e00002c58b16002c583060c1830603060c18300060c000183060cd8f1e6c02fb7ebedf858b162c183060c0000000000000018706000000000000002c58b160c183160c5830600000c783f60c183060c1830000060c183363c79b068381a0e0000162c58b060c183061c1803c036000300006030000000058b162c183062c18b060c058000bf60c783f60c183060c1830060c00018700060c183363c79b068381a0e100200162c58b060c183000000000000e000000003c7870e3c7930e02c5803060f0b830600c183058f164c5803060c183060c183060c783060c1803060c18346a391a8e363c79b2e05c98b164c183060cb9702e5c0b83c00260b0180c2e170187060f0b8032e00c18b1e2c983060c983160c18b0065c78f2e0c1832e0cb83062c0b80b260c783f60c183060c1830600c183060c183060cd8f1e6c1a0e06838b817262c5932e5cb97060c183061c183c2e00cb803062c78b260c183260c583062c5800bf64cd93363c78f1e4c793260c183060c193260c193060c183162c5800c783f60c183060c1830600c183060c183060c183060cd8f1e6c1a0e06838b817262c593269389a4e060c1832e0f01830065c000982c264c2607264cb8030185c2e030e0cd8f1e6c180cb830183363c79b060c193062c183063c1fb060c183060c183060c183060c19b1e3cd8341c0d0703060c19b0e3c383060c069c189c3a70e9c3a70e0c183069c3a70e0f078b162c183062c59326001c38b162c5870161c0e1c0387061c1870601c1830e1c1830e1c187061c78f1e3cb8173e9f8fa7e162c58b0e0c1870e0700038700e1c0381c0e030381c 24 16777215 10 1023
def nh_55 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_55_22 (Nat.sub p 704)) (hc_55_21 (Nat.sub p 672)) (Nat.blt p 704)) (hc_55_20 (Nat.sub p 640)) (Nat.blt p 672)) (Bool.rec (Bool.rec (hc_55_19 (Nat.sub p 608)) (hc_55_18 (Nat.sub p 576)) (Nat.blt p 608)) (hc_55_17 (Nat.sub p 544)) (Nat.blt p 576)) (Nat.blt p 640)) (Bool.rec (Bool.rec (Bool.rec (hc_55_16 (Nat.sub p 512)) (hc_55_15 (Nat.sub p 480)) (Nat.blt p 512)) (hc_55_14 (Nat.sub p 448)) (Nat.blt p 480)) (Bool.rec (Bool.rec (hc_55_13 (Nat.sub p 416)) (hc_55_12 (Nat.sub p 384)) (Nat.blt p 416)) (hc_55_11 (Nat.sub p 352)) (Nat.blt p 384)) (Nat.blt p 448)) (Nat.blt p 544)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_55_10 (Nat.sub p 320)) (hc_55_9 (Nat.sub p 288)) (Nat.blt p 320)) (hc_55_8 (Nat.sub p 256)) (Nat.blt p 288)) (Bool.rec (Bool.rec (hc_55_7 (Nat.sub p 224)) (hc_55_6 (Nat.sub p 192)) (Nat.blt p 224)) (hc_55_5 (Nat.sub p 160)) (Nat.blt p 192)) (Nat.blt p 256)) (Bool.rec (Bool.rec (Bool.rec (hc_55_4 (Nat.sub p 128)) (hc_55_3 (Nat.sub p 96)) (Nat.blt p 128)) (hc_55_2 (Nat.sub p 64)) (Nat.blt p 96)) (Bool.rec (hc_55_1 (Nat.sub p 32)) (hc_55_0 p) (Nat.blt p 32)) (Nat.blt p 64)) (Nat.blt p 160)) (Nat.blt p 352)
def f_55 : Nat → Nat × Nat := unpackForestF 0x317c018b600c5700629802d7c016b600b57005a9802d3c016976785cb3c28002d1ecc07166034005a1d95192c169f64364b05a5d8b5a2c50b960b47b09b25840d2c168600a5fafd2a56d17ebd4895b45bae9365741b2b68af5ba44adc2256d14c014b75a47ca91a7d64df2a46975514fabd2e55452eaa28f5614caad2a55450ea8ae15405ca91a3d4adf2a5069523430052bd44952918bf50244a462dd3a9b29d0d948c57a6922534112918a748828a49a7d24d2e952b949347a4c9a524d0e9104800a53a3e32510dbe8d6a94436ba2e3e510d9e896a94436300527d0c992798df422449e635d049f2798cf402449e631cf20a27a6bf3d35b9e9abcf4d4e7904800a4b9deb44e0dbe756d93836b9ceb84e0d9e716d93836300523cdc992668df3624499a35cd49f2668cf3413799d224cd18c0148732364976b7cc4d525dad73037c976b3cbcd525dac600a3f96d324a95be594a92a56b95d3e4a959e554a92a5630051dca51a249adf28458926b5c9a4fe4d26f26470926b3c9516249ac600a3791d324755be454a91d56b90d3e47559e414a91d5638e81447717e3b8b71dc578ee29c74090014671c464875a7c6cd921d69719d688cc2e43ad1e306c918034875a1c5d1921d49f15a648ac1243a92e29ad10ea4789d3243a90e256c90ea3f88d3243a8ee218d10ea378793243c0921d4660095f86caa40117e192890045b858b642c1b2008af0994484c2240114e112a90035f8389a41c0d2006b70616c801abc144d2006a704144801a7c0c4d2006970215c801a3c024d20106900343004adbfd1f1d569efe37c755a5be893df96b8fa24b7d123bec931f56a8fa2437cab83e4171d568ef7b7c7bc1a3aad0ded8f8eaa4f7a93e3d4091d5496f457075523bcc9f1d5486f237c7551fbc49f1d5476ed35f77e363b4d6dda6aeee35c76e323b4d4dd98e0eaa377593e3ac091d54660095774caa34d17dd1288d345b738b639c1b1a68aee594472c2234d14dc92a8d335f7189a38c0d1a66b6e216c699abb844d1a66a6e0144699a7b7c4d1a6696de15c699a3b724d1b9068d33436980c34ed3da7696da05c69da3b640d1a7686d3a4f6bc1234e92da748ed3a4369d1fb4e8eda746ed402469d19b4c050012a6d2464629b7b44d518a6d6d047c629b3b3cd518a6c6ce46462937b349518a4d6cc47c62933b2a95195048c526364c2e324d518a47ec82546291db1d1618a46ec5a5462c123148cc0129ec41645be37b0c5116f8d6c217c5be33b045116f8c6c01645bdb7afc4d16f6d6be17c5bdb3af24d179068b7b635dca22ded3d75268b7b4b5ccae2ded1d70268b80345bda180252d6dad0a236f5adb6288dad6849eb424759eb8288d9d656d8a236358eb42889bd614d8a226b565a7abd17159696acb4756da62b515159686ac57051133aaa9b155048a226354db62888fd514d8a223b525b7a9d1f1496d6a4b6752db62951d1496c6a44605111ba8a9b145048a2233004a3a84591198dea014446635a7c5f1198ce9e14446631a74591196de9c134465b5a6c5f1196ce999344cc1a232d8d312888cb4f4bc9a232d2d2d2b88cb474a89a2540d1196868c818469afa34d6d1a6ae8d3534692fa3496d1a4ae9002446929a348fd1a4768d23746c122348cd190280094345db21fd5bd156a87f56b44dbe1fd59d116a87f56343db21fc9bd0d4887f26b42dbe1fc99d08488840243f931a0cd50fe4be81a4440c121fc96d016d87f2573fd221fc94c0127e7e16434eb79f4550d3ad67c17c34eb39ec550d3ac67a16434db79e44d0d36d67817c34db39da4d0ed06869b633acaa1a6d7ce82687403434dad9cc5b0d36ae7213434da99a6060d48be6a45b3522b9a914cd44be6a25b3512b9b4090d44a66a24f35c121a892cd448e6a24334c0a0024ecd18d05bd6f33e2c16f5accd8e05bd6732e2c16f58cc98d05ba6f31d2e16e9acc58e05ba673092e184090b74c6604582dd2f97a970bd0485ba5b2ec1a175180b74ae5c25c2dd298024dcb52c84dd6f2ccaa1375acb12f84dd672bd2395c5509bac65616426db79544d09b6d65417c26db394a4d0a50684db6328caa136d7ca02685003426dad93c5b09b6ae4e13426da98024cc994c84056f25d2a1015ac954f84056724d2a10158c914c84046f23d221011ac8d4f84046722d2210118c894a84045f21d2210116c844d84206c2022b9029108108840453004978fc59065ade3e154196b58f45f065ace3c154196b18ec590658de3a144196358e45f0658ce38144196318dc550658be361441962d8d25b0690d832c57198a20cc110658a60092b18db40955bc616b02556b17db809559c5d6b02556316db40951bc596902546b15db809519c556902546314dac09517c516902545b139b009c1b04a8ae25b4812c2209514c0124e2416407eb788c5501fad62217c07eb38845501fac62016407e3787c5101f8d61e17c07e338745101f8c61c15407e2f86c5101f8b61996c0cc3603f15c302881804407e2983e060208be1045b0822b84114c206be1035b081ab840d4c2069e1034b08c2e040d1c210681034307c0a00248c010be0085b0042b80214c0109e0084b0042380210c150bc0083f0041d8241580106e00833004178020ac0b0cc0585e02c2300209c010460081f0040d806198030ac0184e00c1b00205c010260003f 10 11
def ch_55 : Nat → Bool := dagCheckNodeV5 fullMask g_55 ep_55 5 31 bds_55 731 (dagTraceF fullMask rootStock 11 f_55) cur_55 nh_55
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 fullMask g_55 ep_55 5 31 731 bds_55 (dagTraceF fullMask rootStock 11 f_55) (cur_55 0) (nh_55 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_0 : treeBlockF 0 32 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_1 : treeBlockF 32 64 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_2 : treeBlockF 64 96 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_3 : treeBlockF 96 128 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_4 : treeBlockF 128 160 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_5 : treeBlockF 160 192 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_6 : treeBlockF 192 224 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_7 : treeBlockF 224 256 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_8 : treeBlockF 256 288 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_9 : treeBlockF 288 320 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_10 : treeBlockF 320 352 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_11 : treeBlockF 352 384 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_12 : treeBlockF 384 416 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_13 : treeBlockF 416 448 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_14 : treeBlockF 448 480 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_15 : treeBlockF 480 512 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_16 : treeBlockF 512 544 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_17 : treeBlockF 544 576 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_18 : treeBlockF 576 608 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_19 : treeBlockF 608 640 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_20 : treeBlockF 640 672 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_21 : treeBlockF 672 704 ch_55 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_55_22 : treeBlockF 704 731 ch_55 = true := by decide +kernel
theorem nj_55_1 : ∀ i, 0 ≤ i → i < 64 → ch_55 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_55_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_55_1 h1 h2)
theorem nj_55_2 : ∀ i, 0 ≤ i → i < 96 → ch_55 i = true := block_join nj_55_1 (fun _ h1 h2 => treeBlockF_at nb_55_2 h1 h2)
theorem nj_55_3 : ∀ i, 0 ≤ i → i < 128 → ch_55 i = true := block_join nj_55_2 (fun _ h1 h2 => treeBlockF_at nb_55_3 h1 h2)
theorem nj_55_4 : ∀ i, 0 ≤ i → i < 160 → ch_55 i = true := block_join nj_55_3 (fun _ h1 h2 => treeBlockF_at nb_55_4 h1 h2)
theorem nj_55_5 : ∀ i, 0 ≤ i → i < 192 → ch_55 i = true := block_join nj_55_4 (fun _ h1 h2 => treeBlockF_at nb_55_5 h1 h2)
theorem nj_55_6 : ∀ i, 0 ≤ i → i < 224 → ch_55 i = true := block_join nj_55_5 (fun _ h1 h2 => treeBlockF_at nb_55_6 h1 h2)
theorem nj_55_7 : ∀ i, 0 ≤ i → i < 256 → ch_55 i = true := block_join nj_55_6 (fun _ h1 h2 => treeBlockF_at nb_55_7 h1 h2)
theorem nj_55_8 : ∀ i, 0 ≤ i → i < 288 → ch_55 i = true := block_join nj_55_7 (fun _ h1 h2 => treeBlockF_at nb_55_8 h1 h2)
theorem nj_55_9 : ∀ i, 0 ≤ i → i < 320 → ch_55 i = true := block_join nj_55_8 (fun _ h1 h2 => treeBlockF_at nb_55_9 h1 h2)
theorem nj_55_10 : ∀ i, 0 ≤ i → i < 352 → ch_55 i = true := block_join nj_55_9 (fun _ h1 h2 => treeBlockF_at nb_55_10 h1 h2)
theorem nj_55_11 : ∀ i, 0 ≤ i → i < 384 → ch_55 i = true := block_join nj_55_10 (fun _ h1 h2 => treeBlockF_at nb_55_11 h1 h2)
theorem nj_55_12 : ∀ i, 0 ≤ i → i < 416 → ch_55 i = true := block_join nj_55_11 (fun _ h1 h2 => treeBlockF_at nb_55_12 h1 h2)
theorem nj_55_13 : ∀ i, 0 ≤ i → i < 448 → ch_55 i = true := block_join nj_55_12 (fun _ h1 h2 => treeBlockF_at nb_55_13 h1 h2)
theorem nj_55_14 : ∀ i, 0 ≤ i → i < 480 → ch_55 i = true := block_join nj_55_13 (fun _ h1 h2 => treeBlockF_at nb_55_14 h1 h2)
theorem nj_55_15 : ∀ i, 0 ≤ i → i < 512 → ch_55 i = true := block_join nj_55_14 (fun _ h1 h2 => treeBlockF_at nb_55_15 h1 h2)
theorem nj_55_16 : ∀ i, 0 ≤ i → i < 544 → ch_55 i = true := block_join nj_55_15 (fun _ h1 h2 => treeBlockF_at nb_55_16 h1 h2)
theorem nj_55_17 : ∀ i, 0 ≤ i → i < 576 → ch_55 i = true := block_join nj_55_16 (fun _ h1 h2 => treeBlockF_at nb_55_17 h1 h2)
theorem nj_55_18 : ∀ i, 0 ≤ i → i < 608 → ch_55 i = true := block_join nj_55_17 (fun _ h1 h2 => treeBlockF_at nb_55_18 h1 h2)
theorem nj_55_19 : ∀ i, 0 ≤ i → i < 640 → ch_55 i = true := block_join nj_55_18 (fun _ h1 h2 => treeBlockF_at nb_55_19 h1 h2)
theorem nj_55_20 : ∀ i, 0 ≤ i → i < 672 → ch_55 i = true := block_join nj_55_19 (fun _ h1 h2 => treeBlockF_at nb_55_20 h1 h2)
theorem nj_55_21 : ∀ i, 0 ≤ i → i < 704 → ch_55 i = true := block_join nj_55_20 (fun _ h1 h2 => treeBlockF_at nb_55_21 h1 h2)
theorem nj_55_22 : ∀ i, 0 ≤ i → i < 731 → ch_55 i = true := block_join nj_55_21 (fun _ h1 h2 => treeBlockF_at nb_55_22 h1 h2)
theorem nc_55 : ∀ i, 0 ≤ i → i < 731 → ch_55 i = true := nj_55_22
theorem lb_55 : LowerBin fullMask rootStock g_55 12 :=
  lowerDagV5 (kn_cons lb_32 (kn_cons lb_54 (kn_cons lb_26 (kn_cons lb_52 (kn_cons lb_25 (kn_cons lb_53 (kn_cons lb_50 (kn_cons lb_51 (kn_cons lb_31 (kn_cons lb_49 (kn_cons lb_23 (kn_cons lb_24 (kn_cons lb_33 (kn_cons lb_29 (kn_cons lb_34 (kn_cons lb_46 (kn_cons lb_39 (kn_cons lb_43 (kn_cons lb_44 (kn_cons lb_38 (kn_cons lb_36 (kn_cons lb_41 (kn_cons lb_45 (kn_cons lb_28 (kn_cons lb_27 (kn_cons lb_37 (kn_cons lb_40 (kn_cons lb_17 (kn_cons lb_22 (kn_cons lb_42 (kn_cons lb_47 (kn_cons lb_48 (kn_cons lb_35 (kn_nil)))))))))))))))))))))))))))))))))) rc_55 nc_55 (by decide +kernel)

def wg : List Gate := [⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [15, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676736 * 2 ^ 32 + 3939033216)) (13 - 1) := by
  rw [show canon fullMask (4276676736 * 2 ^ 32 + 3939033216) = g_55 by decide]
  exact lb_55

end PEqualNP.Outside.L_meta_49303

theorem PEqualNP.Outside.L_meta_49303 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676736 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676736 * 2 ^ 32 + 3939033216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_49303.table2_from_lowerBin (4276676736 * 2 ^ 32 + 3939033216) 13 PEqualNP.Outside.L_meta_49303.root_lb PEqualNP.Outside.L_meta_49303.wg 18 rfl PEqualNP.Outside.L_meta_49303.wfits PEqualNP.Outside.L_meta_49303.weval
