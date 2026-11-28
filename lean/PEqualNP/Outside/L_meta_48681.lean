import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48681

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

def m_0 : Nat := 0xf000f0000000000
def s_0 : List Nat := [0x500050000000000, 0x300030000000000, 0xf0000000000]
def g_0 : Nat := 0x100070000000000
def ep_0 : Nat := 0x600000000000000000000000000000000000000000001000200000000000100040000000000
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

def m_1 : Nat := 0x5500550000000000
def s_1 : List Nat := [0x1100110000000000, 0x500050000000000, 0x550000000000]
def g_1 : Nat := 0x100150000000000
def ep_1 : Nat := 0x1400000000000000000000000000010004000000000001001000000000000000000000000000
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

def m_2 : Nat := 0x3300000033000000
def s_2 : List Nat := [0x1100000011000000, 0x300000003000000, 0x33000000]
def g_2 : Nat := 0x100000013000000
def ep_2 : Nat := 0x1200000000000000000000000000000000000000010000000200000000000000000000000100000010000000
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

def m_3 : Nat := 0x3300330000000000
def s_3 : List Nat := [0x1100110000000000, 0x300030000000000, 0x330000000000]
def g_3 : Nat := 0x100130000000000
def ep_3 : Nat := 0x1200000000000000000000000000010002000000000000000000000000000100100000000000
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

def m_5 : Nat := 0x4444444400000000
def s_5 : List Nat := [0x404040400000000, 0x44004400000000, 0x444400000000]
def g_5 : Nat := 0x4044400000000
def ep_5 : Nat := 0x440000000000004004000000000000404000000000000000000000000000000000000000000
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

def m_6 : Nat := 0x3000300030003000
def s_6 : List Nat := [0x1000100010001000, 0x300000003000, 0x30003000]
def g_6 : Nat := 0x100010003000
def ep_6 : Nat := 0x1000200000001000000020000000000000000000000000000000000000000000000000000000100010000000
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

def m_7 : Nat := 0x3333000000000000
def s_7 : List Nat := [0x1111000000000000, 0x303000000000000, 0x33000000000000]
def g_7 : Nat := 0x113000000000000
def ep_7 : Nat := 0x12000000000000010200000000000000000000000000000110000000000000
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

def m_8 : Nat := 0x5555000000000000
def s_8 : List Nat := [0x1111000000000000, 0x505000000000000, 0x55000000000000]
def g_8 : Nat := 0x115000000000000
def ep_8 : Nat := 0x14000000000000010400000000000001100000000000000000000000000000
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

def m_9 : Nat := 0xff000000000000
def s_9 : List Nat := [0x55000000000000, 0x33000000000000, 0xf000000000000]
def g_9 : Nat := 0x17000000000000
def ep_9 : Nat := 0x600000000000000120000000000000014000000000000
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

def m_10 : Nat := 0xc000c000c000c0
def s_10 : List Nat := [0x40004000400040, 0xc0000000c0, 0xc000c0]
def g_10 : Nat := 0x40004000c0
def ep_10 : Nat := 0x40008000000040000000800000000000000000000000000000000000000000000000000000004000400000
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

def m_11 : Nat := 0xf0f000000000000
def s_11 : List Nat := [0x505000000000000, 0x303000000000000, 0xf000000000000]
def g_11 : Nat := 0x107000000000000
def ep_11 : Nat := 0x6000000000000000000000000000001020000000000000104000000000000
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

def m_12 : Nat := 0x2200220022002200
def s_12 : List Nat := [0x200020002000200, 0x220000002200, 0x22002200]
def g_12 : Nat := 0x20002002200
def ep_12 : Nat := 0x200200000000200000020000000000000000000000002000200000000000000000000000000000000000000
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

def m_13 : Nat := 0xc0c0c0c
def s_13 : List Nat := [0x4040404, 0xc000c, 0xc0c]
def g_13 : Nat := 0x4040c
def ep_13 : Nat := 0x4080000000000040008000000000000000000000000000000000000000000040400
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

def m_14 : Nat := 0xff0000000000
def s_14 : List Nat := [0x550000000000, 0x330000000000, 0xf0000000000]
def g_14 : Nat := 0x170000000000
def ep_14 : Nat := 0x6000000000000001200000000000000140000000000
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

def m_15 : Nat := 0x5050000050500000
def s_15 : List Nat := [0x1010000010100000, 0x50000000500000, 0x50500000]
def g_15 : Nat := 0x10000010500000
def ep_15 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000000000000000000
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

def m_16 : Nat := 0x30c030c030c030c
def s_16 : List Nat := [0x104010401040104, 0xc000c000c000c, 0x30c0000030c, 0x30c030c]
def g_16 : Nat := 0x10403040304030c
def ep_16 : Nat := 0x200000800000200000000080000000000000000000000000000000000000000000000000104000400040000
def bds_16 : List (Nat × List Nat × Nat × Nat) := []
def cur_16 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_16 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_16 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_16 : Nat → Bool := dagCheckNodeV5 m_16 g_16 ep_16 1 1 bds_16 10 (dagTraceF m_16 s_16 4 f_16) cur_16 nh_16
set_option maxHeartbeats 0 in
theorem rc_16 : dagCheckRootsV5 m_16 g_16 ep_16 1 1 10 bds_16 (dagTraceF m_16 s_16 4 f_16) (cur_16 0) (nh_16 0) s_16 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_16 : treeBlockF 0 10 ch_16 = true := by decide +kernel
theorem nc_16 : ∀ i, 0 ≤ i → i < 10 → ch_16 i = true := fun _ h1 h2 => treeBlockF_at nb_16 h1 h2
theorem lb_16 : LowerBin m_16 s_16 g_16 5 :=
  lowerDagV5 (kn_nil) rc_16 nc_16 (by decide +kernel)

def m_17 : Nat := 0xcccc000033330000
def s_17 : List Nat := [0x4444000011110000, 0x33330000, 0xc0c000003030000, 0xcc000000330000]
def g_17 : Nat := 0x4000013130000
def ep_17 : Nat := 0x4000000000000000400000202000000000000000000000004000010100000
def bds_17 : List (Nat × List Nat × Nat × Nat) := []
def cur_17 : Nat → List (Nat × Nat) := unpackCursorV5 0xb146850932244890e8701 0x54a1e787302904cfa264d2e591207442a00f 7 127 3 7 9 511 13 8191
def nh_17 : Nat → Nat := unpackHintV5 0xe81b12e45c0a8912201400800f082e002 0x0 11 2047 5 31
def f_17 : Nat → Nat × Nat := unpackForestF 0x54a067c33279e0cb864421d298148042a00f 4 9
def ch_17 : Nat → Bool := dagCheckNodeV5 m_17 g_17 ep_17 1 1 bds_17 11 (dagTraceF m_17 s_17 4 f_17) cur_17 nh_17
set_option maxHeartbeats 0 in
theorem rc_17 : dagCheckRootsV5 m_17 g_17 ep_17 1 1 11 bds_17 (dagTraceF m_17 s_17 4 f_17) (cur_17 0) (nh_17 0) s_17 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_17 : treeBlockF 0 11 ch_17 = true := by decide +kernel
theorem nc_17 : ∀ i, 0 ≤ i → i < 11 → ch_17 i = true := fun _ h1 h2 => treeBlockF_at nb_17 h1 h2
theorem lb_17 : LowerBin m_17 s_17 g_17 5 :=
  lowerDagV5 (kn_nil) rc_17 nc_17 (by decide +kernel)

def m_18 : Nat := 0x33330000cccc
def s_18 : List Nat := [0x111100004444, 0xcccc, 0x30300000c0c, 0x33000000cc]
def g_18 : Nat := 0x1313000004cc
def ep_18 : Nat := 0xc8000002020000040000000000000000000000101000000400
def bds_18 : List (Nat × List Nat × Nat × Nat) := []
def cc_18_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xf01e0391f20e03b87706c1d81b0350ea0d4179ae0dc0b43682c0ce59c128a504a08c518230460844d981d001 0x3c9e1d4c09830492c049018090a8685d3a2c9b144a89a4c481e040e854b020300c1804940f1307088343c181a0709020381c34060e040d01848283d121a880b4304a141e040ecd8fe64772e378719c24fe0a7701377699ba4bdca56e1276691ae0fd5876a0374e19a20bcf856702736119a07cc8364419200b8b04c0822000f 11 2047 5 31 10 1023 17 131071
def cc_18_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xd8d8d8bcb8b8b8b8b8b8b89c989898987c78715b585843404040404024201903 0xfd3cf934f418f014dd4cd944d418d014ca38c634c138bd3460185d28b43cb034a94ca54058189a4c964491288d2454185128844c8044 8 255 3 7 10 1023 16 65535
def cc_18_2 : Nat → List (Nat × Nat) := unpackCursorV5 0x14284974e1c3160a54050000000 0x2546121248c14488d234692b4492944749228511024 7 127 3 7 10 1023 17 131071
def cur_18 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_18_2 (Nat.sub p 64)) (cc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_18_0 p) (Nat.blt p 32)
def hc_18_0 : Nat → Nat := unpackHintV5 0x8824211f10e4a6c33319980c826213101804bc25c1292930c90446121110047463811c00d846c03601a08d006803020f480b8002 0x0 13 8191 5 31
def hc_18_1 : Nat → Nat := unpackHintV5 0xd636a0b4098cab49533a5252048a3440a108f4a7623721a88cc45c52a214849484622110e9060a2c212208083841250520204008 0x0 13 8191 5 31
def hc_18_2 : Nat → Nat := unpackHintV5 0x525a3acf546e63511890acc52225211886d02490b38124004 0x0 13 8191 5 31
def nh_18 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_18_2 (Nat.sub p 64)) (hc_18_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_18_0 p) (Nat.blt p 32)
def f_18 : Nat → Nat × Nat := unpackForestF 0xc7e063b031bc4d12225122348892468d2205110240319814fc0a760537789e3c4d1e030f0140299814bc0a56052768a634511a030d0140291af8e17c68bd385e9a010fd6078b034021da95314a8004370219a39311c888d284692010bd0098804402159d4f0ea60042702118107c08366024249d124d8a868492a2493120780832041718260c110607830340209820f4106a082d0e1a02094103c0c340612020740822000f 7 10
def ch_18 : Nat → Bool := dagCheckNodeV5 m_18 g_18 ep_18 1 1 bds_18 78 (dagTraceF m_18 s_18 5 f_18) cur_18 nh_18
set_option maxHeartbeats 0 in
theorem rc_18 : dagCheckRootsV5 m_18 g_18 ep_18 1 1 78 bds_18 (dagTraceF m_18 s_18 5 f_18) (cur_18 0) (nh_18 0) s_18 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_0 : treeBlockF 0 32 ch_18 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_1 : treeBlockF 32 64 ch_18 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_18_2 : treeBlockF 64 78 ch_18 = true := by decide +kernel
theorem nj_18_1 : ∀ i, 0 ≤ i → i < 64 → ch_18 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_18_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_18_1 h1 h2)
theorem nj_18_2 : ∀ i, 0 ≤ i → i < 78 → ch_18 i = true := block_join nj_18_1 (fun _ h1 h2 => treeBlockF_at nb_18_2 h1 h2)
theorem nc_18 : ∀ i, 0 ≤ i → i < 78 → ch_18 i = true := nj_18_2
theorem lb_18 : LowerBin m_18 s_18 g_18 6 :=
  lowerDagV5 (kn_nil) rc_18 nc_18 (by decide +kernel)

def m_19 : Nat := 0x3030c0c03030c0c
def s_19 : List Nat := [0x101040401010404, 0xc0c00000c0c, 0x3000c0003000c, 0x3030c0c]
def g_19 : Nat := 0x10304040303040c
def ep_19 : Nat := 0x200000800000000000000000002000000000008000000000000000000000000000000000100040400000400
def bds_19 : List (Nat × List Nat × Nat × Nat) := []
def cur_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58952244890e8701 0x1d283091e3420d0d2420a263a88d993a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_19 : Nat → Nat := unpackHintV5 0x340c0b00c0300c0300c02c215002 0x0 10 1023 5 31
def f_19 : Nat → Nat × Nat := unpackForestF 0xc74636f1a14e8a6c43a49220a086c00f 3 10
def ch_19 : Nat → Bool := dagCheckNodeV5 m_19 g_19 ep_19 1 1 bds_19 10 (dagTraceF m_19 s_19 4 f_19) cur_19 nh_19
set_option maxHeartbeats 0 in
theorem rc_19 : dagCheckRootsV5 m_19 g_19 ep_19 1 1 10 bds_19 (dagTraceF m_19 s_19 4 f_19) (cur_19 0) (nh_19 0) s_19 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_19 : treeBlockF 0 10 ch_19 = true := by decide +kernel
theorem nc_19 : ∀ i, 0 ≤ i → i < 10 → ch_19 i = true := fun _ h1 h2 => treeBlockF_at nb_19 h1 h2
theorem lb_19 : LowerBin m_19 s_19 g_19 5 :=
  lowerDagV5 (kn_nil) rc_19 nc_19 (by decide +kernel)

def m_20 : Nat := 0xff00ff0000000000
def s_20 : List Nat := [0x5500550000000000, 0x3300330000000000, 0xf000f0000000000, 0xff0000000000]
def g_20 : Nat := 0x100170000000000
def ep_20 : Nat := 0x1600000000000000000000000000010006000000000001001200000000000100140000000000
def bds_20 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0), (m_14, s_14, 4, g_14), (m_1, s_1, 4, g_1), (m_3, s_3, 4, g_3)]
def cc_20_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_20_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_20 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_20_1 (Nat.sub p 32)) (cc_20_0 p) (Nat.blt p 32)
def hc_20_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_20_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_20 : Nat → Nat := fun p => Bool.rec (hc_20_1 (Nat.sub p 32)) (hc_20_0 p) (Nat.blt p 32)
def f_20 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_20 : Nat → Bool := dagCheckNodeV5 m_20 g_20 ep_20 1 1 bds_20 43 (dagTraceF m_20 s_20 6 f_20) cur_20 nh_20
set_option maxHeartbeats 0 in
theorem rc_20 : dagCheckRootsV5 m_20 g_20 ep_20 1 1 43 bds_20 (dagTraceF m_20 s_20 6 f_20) (cur_20 0) (nh_20 0) s_20 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_0 : treeBlockF 0 32 ch_20 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_20_1 : treeBlockF 32 43 ch_20 = true := by decide +kernel
theorem nj_20_1 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_20_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_20_1 h1 h2)
theorem nc_20 : ∀ i, 0 ≤ i → i < 43 → ch_20 i = true := nj_20_1
theorem lb_20 : LowerBin m_20 s_20 g_20 7 :=
  lowerDagV5 (kn_cons lb_0 (kn_cons lb_14 (kn_cons lb_1 (kn_cons lb_3 (kn_nil))))) rc_20 nc_20 (by decide +kernel)

def m_21 : Nat := 0xffff000000000000
def s_21 : List Nat := [0x5555000000000000, 0x3333000000000000, 0xf0f000000000000, 0xff000000000000]
def g_21 : Nat := 0x117000000000000
def ep_21 : Nat := 0x16000000000000010600000000000001120000000000000114000000000000
def bds_21 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11), (m_9, s_9, 4, g_9), (m_8, s_8, 4, g_8), (m_7, s_7, 4, g_7)]
def cc_21_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2a1a4690a4218805f17c1e1781e0745d0561414c530485204451044101401003c47805801 0x7c188f428642814e7942543130217419081151402d306f416a414d322922643e4032602e1422514025305340442c5b4256314d422122484e40423c2e08222d4025302e402630183c0c4c36423232294221321c4e1442103e0832a233913371235c3338230413000f 10 1023 4 15 10 1023 16 65535
def cc_21_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170a1502805011080040000 0x9d418d31a92979216c415831a42940218a409f418632993e793268413421941914118a408b40 9 511 4 15 10 1023 16 65535
def cur_21 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_21_1 (Nat.sub p 32)) (cc_21_0 p) (Nat.blt p 32)
def hc_21_0 : Nat → Nat := unpackHintV5 0x87050e01d1338476d8cdb01b602de4588cab194a327874f009e0138127003b4c7018d2398c62e8c5718a03940028004d0c9a01340258427900138000 0x58302806c55a8532aaad833282ce86d5aad282d95a21020c702a014d883a20632b50 15 32767 6 63
def hc_21_1 : Nat → Nat := unpackHintV5 0xc806401f4cdc76e037009c83460e3001c000000 0x7553a984d4644000d9429013a 13 8191 6 63
def nh_21 : Nat → Nat := fun p => Bool.rec (hc_21_1 (Nat.sub p 32)) (hc_21_0 p) (Nat.blt p 32)
def f_21 : Nat → Nat × Nat := unpackForestF 0xa529a42906339741953e9419053377428b407642754e7c1875427419052363416241603e602e04333f423e3153403d423c4e442c3c423c2e04230a420a322e40094226300932084e183c0842083e0c4c08320413000f 6 10
def ch_21 : Nat → Bool := dagCheckNodeV5 m_21 g_21 ep_21 1 1 bds_21 43 (dagTraceF m_21 s_21 6 f_21) cur_21 nh_21
set_option maxHeartbeats 0 in
theorem rc_21 : dagCheckRootsV5 m_21 g_21 ep_21 1 1 43 bds_21 (dagTraceF m_21 s_21 6 f_21) (cur_21 0) (nh_21 0) s_21 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_0 : treeBlockF 0 32 ch_21 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_21_1 : treeBlockF 32 43 ch_21 = true := by decide +kernel
theorem nj_21_1 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_21_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_21_1 h1 h2)
theorem nc_21 : ∀ i, 0 ≤ i → i < 43 → ch_21 i = true := nj_21_1
theorem lb_21 : LowerBin m_21 s_21 g_21 7 :=
  lowerDagV5 (kn_cons lb_11 (kn_cons lb_9 (kn_cons lb_8 (kn_cons lb_7 (kn_nil))))) rc_21 nc_21 (by decide +kernel)

def m_22 : Nat := 0xff00ff00000000
def s_22 : List Nat := [0x55005500000000, 0x33003300000000, 0xf000f00000000, 0xff00000000]
def g_22 : Nat := 0x17005700000000
def ep_22 : Nat := 0x40000000000000000000000000000600020000000000120002000000000014005400000000
def bds_22 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9)]
def cur_22 : Nat → List (Nat × Nat) := fun _ => []
def nh_22 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_22 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_22 : dagCheckRootsV5 m_22 g_22 ep_22 1 1 0 bds_22 (dagTraceF m_22 s_22 4 f_22) (cur_22 0) (nh_22 0) s_22 4 = true := by decide +kernel
theorem nc_22 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_22 g_22 ep_22 1 1 bds_22 0 (dagTraceF m_22 s_22 4 f_22) cur_22 nh_22 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_22 : LowerBin m_22 s_22 g_22 5 :=
  lowerDagV5 (kn_cons lb_9 (kn_nil)) rc_22 nc_22 (by decide +kernel)

def m_23 : Nat := 0xf0f0f0f000000000
def s_23 : List Nat := [0x5050505000000000, 0x3030303000000000, 0xf000f000000000, 0xf0f000000000]
def g_23 : Nat := 0x10105000000000
def ep_23 : Nat := 0x1040000000000010004000000000000000000000000000101000000000000010105000000000
def bds_23 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_23 : Nat → List (Nat × Nat) := fun _ => []
def nh_23 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_23 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_23 : dagCheckRootsV5 m_23 g_23 ep_23 1 1 0 bds_23 (dagTraceF m_23 s_23 4 f_23) (cur_23 0) (nh_23 0) s_23 4 = true := by decide +kernel
theorem nc_23 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_23 g_23 ep_23 1 1 bds_23 0 (dagTraceF m_23 s_23 4 f_23) cur_23 nh_23 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_23 : LowerBin m_23 s_23 g_23 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_23 nc_23 (by decide +kernel)

def m_24 : Nat := 0xf0f0f0f00000000
def s_24 : List Nat := [0x505050500000000, 0x303030300000000, 0xf000f00000000, 0xf0f00000000]
def g_24 : Nat := 0x107070700000000
def ep_24 : Nat := 0x600000000000006000000000000000000000000000001020202000000000104040400000000
def bds_24 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_24 : Nat → List (Nat × Nat) := fun _ => []
def nh_24 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_24 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_24 : dagCheckRootsV5 m_24 g_24 ep_24 1 1 0 bds_24 (dagTraceF m_24 s_24 4 f_24) (cur_24 0) (nh_24 0) s_24 4 = true := by decide +kernel
theorem nc_24 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_24 g_24 ep_24 1 1 bds_24 0 (dagTraceF m_24 s_24 4 f_24) cur_24 nh_24 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_24 : LowerBin m_24 s_24 g_24 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_24 nc_24 (by decide +kernel)

def m_25 : Nat := 0xcccccccc00000000
def s_25 : List Nat := [0x4444444400000000, 0xc0c0c0c00000000, 0xcc00cc00000000, 0xcccc00000000]
def g_25 : Nat := 0x4044400000000
def ep_25 : Nat := 0x440000000000004004000000000000404000000000000000000000000000004044400000000
def bds_25 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5)]
def cur_25 : Nat → List (Nat × Nat) := fun _ => []
def nh_25 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_25 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_25 : dagCheckRootsV5 m_25 g_25 ep_25 1 1 0 bds_25 (dagTraceF m_25 s_25 4 f_25) (cur_25 0) (nh_25 0) s_25 4 = true := by decide +kernel
theorem nc_25 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_25 g_25 ep_25 1 1 bds_25 0 (dagTraceF m_25 s_25 4 f_25) cur_25 nh_25 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_25 : LowerBin m_25 s_25 g_25 5 :=
  lowerDagV5 (kn_cons lb_5 (kn_nil)) rc_25 nc_25 (by decide +kernel)

def m_26 : Nat := 0x3333333300000000
def s_26 : List Nat := [0x1111111100000000, 0x303030300000000, 0x33003300000000, 0x333300000000]
def g_26 : Nat := 0x113131300000000
def ep_26 : Nat := 0x1200000000000012000000000000010202020000000000000000000000000110101000000000
def bds_26 : List (Nat × List Nat × Nat × Nat) := [(m_3, s_3, 4, g_3)]
def cur_26 : Nat → List (Nat × Nat) := fun _ => []
def nh_26 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_26 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_26 : dagCheckRootsV5 m_26 g_26 ep_26 1 1 0 bds_26 (dagTraceF m_26 s_26 4 f_26) (cur_26 0) (nh_26 0) s_26 4 = true := by decide +kernel
theorem nc_26 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_26 g_26 ep_26 1 1 bds_26 0 (dagTraceF m_26 s_26 4 f_26) cur_26 nh_26 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_26 : LowerBin m_26 s_26 g_26 5 :=
  lowerDagV5 (kn_cons lb_3 (kn_nil)) rc_26 nc_26 (by decide +kernel)

def m_27 : Nat := 0x5050505050505050
def s_27 : List Nat := [0x1010101010101010, 0x50005000500050, 0x505000005050, 0x50505050]
def g_27 : Nat := 0x10105010501050
def ep_27 : Nat := 0x1040000000001040000000000010004000400040000000000000000000101000100010000000000000000000
def bds_27 : List (Nat × List Nat × Nat × Nat) := [(m_4, s_4, 4, g_4)]
def cur_27 : Nat → List (Nat × Nat) := fun _ => []
def nh_27 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_27 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_27 : dagCheckRootsV5 m_27 g_27 ep_27 1 1 0 bds_27 (dagTraceF m_27 s_27 4 f_27) (cur_27 0) (nh_27 0) s_27 4 = true := by decide +kernel
theorem nc_27 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_27 g_27 ep_27 1 1 bds_27 0 (dagTraceF m_27 s_27 4 f_27) cur_27 nh_27 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_27 : LowerBin m_27 s_27 g_27 5 :=
  lowerDagV5 (kn_cons lb_4 (kn_nil)) rc_27 nc_27 (by decide +kernel)

def m_28 : Nat := 0x5555555500000000
def s_28 : List Nat := [0x1111111100000000, 0x505050500000000, 0x55005500000000, 0x555500000000]
def g_28 : Nat := 0x115155500000000
def ep_28 : Nat := 0x1440000000000014004000000000010404000000000001101000000000000000000000000000
def bds_28 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1), (m_8, s_8, 4, g_8), (m_4, s_4, 4, g_4), (m_5, s_5, 4, g_5)]
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
  lowerDagV5 (kn_cons lb_1 (kn_cons lb_8 (kn_cons lb_4 (kn_cons lb_5 (kn_nil))))) rc_28 nc_28 (by decide +kernel)

def m_29 : Nat := 0x66006600660066
def s_29 : List Nat := [0x22002200220022, 0x6000600060006, 0x6600000066, 0x660066]
def g_29 : Nat := 0x6004600460066
def ep_29 : Nat := 0x40002000000040000000200000000000000000000600020002000000000000000000000000000000000000
def bds_29 : List (Nat × List Nat × Nat × Nat) := []
def cur_29 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x1924309193c2050d3c205263d88d5d2a549902a109800f 7 127 3 7 10 1023 14 16383
def nh_29 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_29 : Nat → Nat × Nat := unpackForestF 0xc7a63529564f0a4c42a49e205084c00f 3 10
def ch_29 : Nat → Bool := dagCheckNodeV5 m_29 g_29 ep_29 1 1 bds_29 10 (dagTraceF m_29 s_29 4 f_29) cur_29 nh_29
set_option maxHeartbeats 0 in
theorem rc_29 : dagCheckRootsV5 m_29 g_29 ep_29 1 1 10 bds_29 (dagTraceF m_29 s_29 4 f_29) (cur_29 0) (nh_29 0) s_29 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_29 : treeBlockF 0 10 ch_29 = true := by decide +kernel
theorem nc_29 : ∀ i, 0 ≤ i → i < 10 → ch_29 i = true := fun _ h1 h2 => treeBlockF_at nb_29 h1 h2
theorem lb_29 : LowerBin m_29 s_29 g_29 5 :=
  lowerDagV5 (kn_nil) rc_29 nc_29 (by decide +kernel)

def m_30 : Nat := 0x3030303030303030
def s_30 : List Nat := [0x1010101010101010, 0x30003000300030, 0x303000003030, 0x30303030]
def g_30 : Nat := 0x10101010103030
def ep_30 : Nat := 0x1000202000001000000020200010000000000000000000000000000000000000000000000010101010100000
def bds_30 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_30 : Nat → List (Nat × Nat) := fun _ => []
def nh_30 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_30 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_30 : dagCheckRootsV5 m_30 g_30 ep_30 1 1 0 bds_30 (dagTraceF m_30 s_30 4 f_30) (cur_30 0) (nh_30 0) s_30 4 = true := by decide +kernel
theorem nc_30 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_30 g_30 ep_30 1 1 bds_30 0 (dagTraceF m_30 s_30 4 f_30) cur_30 nh_30 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_30 : LowerBin m_30 s_30 g_30 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_30 nc_30 (by decide +kernel)

def m_31 : Nat := 0xc0c0c0c0c0c0c0c0
def s_31 : List Nat := [0x4040404040404040, 0xc000c000c000c0, 0xc0c00000c0c0, 0xc0c0c0c0]
def g_31 : Nat := 0x40004000c0
def ep_31 : Nat := 0x400080000000400000008000000040004000c0000000000000000000000000000000000000004000400000
def bds_31 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_31 : Nat → List (Nat × Nat) := fun _ => []
def nh_31 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_31 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_31 : dagCheckRootsV5 m_31 g_31 ep_31 1 1 0 bds_31 (dagTraceF m_31 s_31 4 f_31) (cur_31 0) (nh_31 0) s_31 4 = true := by decide +kernel
theorem nc_31 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_31 g_31 ep_31 1 1 bds_31 0 (dagTraceF m_31 s_31 4 f_31) cur_31 nh_31 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_31 : LowerBin m_31 s_31 g_31 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_31 nc_31 (by decide +kernel)

def m_32 : Nat := 0xcccc0000cccc
def s_32 : List Nat := [0x444400004444, 0xc0c00000c0c, 0xcc000000cc, 0xcccc]
def g_32 : Nat := 0x444000004cc
def ep_32 : Nat := 0x88000000000000000000000040000000c8000004000000040000000000000000000000044400000400
def bds_32 : List (Nat × List Nat × Nat × Nat) := []
def cur_32 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_32 : Nat → Nat := fun _ => 0
def f_32 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_32 : Nat → Bool := dagCheckNodeV5 m_32 g_32 ep_32 1 1 bds_32 1 (dagTraceF m_32 s_32 3 f_32) cur_32 nh_32
set_option maxHeartbeats 0 in
theorem rc_32 : dagCheckRootsV5 m_32 g_32 ep_32 1 1 1 bds_32 (dagTraceF m_32 s_32 3 f_32) (cur_32 0) (nh_32 0) s_32 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_32 : treeBlockF 0 1 ch_32 = true := by decide +kernel
theorem nc_32 : ∀ i, 0 ≤ i → i < 1 → ch_32 i = true := fun _ h1 h2 => treeBlockF_at nb_32 h1 h2
theorem lb_32 : LowerBin m_32 s_32 g_32 4 :=
  lowerDagV5 (kn_nil) rc_32 nc_32 (by decide +kernel)

def m_33 : Nat := 0x3333000033330000
def s_33 : List Nat := [0x1111000011110000, 0x303000003030000, 0x33000000330000, 0x33330000]
def g_33 : Nat := 0x113000013130000
def ep_33 : Nat := 0x1200000000000000000000000012000000000000010200000202000000000000000000000110000010100000
def bds_33 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_33 : Nat → List (Nat × Nat) := fun _ => []
def nh_33 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_33 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_33 : dagCheckRootsV5 m_33 g_33 ep_33 1 1 0 bds_33 (dagTraceF m_33 s_33 4 f_33) (cur_33 0) (nh_33 0) s_33 4 = true := by decide +kernel
theorem nc_33 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_33 g_33 ep_33 1 1 bds_33 0 (dagTraceF m_33 s_33 4 f_33) cur_33 nh_33 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_33 : LowerBin m_33 s_33 g_33 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_33 nc_33 (by decide +kernel)

def m_34 : Nat := 0x5500550055005500
def s_34 : List Nat := [0x1100110011001100, 0x500050005000500, 0x550000005500, 0x55005500]
def g_34 : Nat := 0x100150011001500
def ep_34 : Nat := 0x1000000000001400000004000000000000000000010004000000040001001000110010000000000000000000
def bds_34 : List (Nat × List Nat × Nat × Nat) := [(m_1, s_1, 4, g_1)]
def cur_34 : Nat → List (Nat × Nat) := fun _ => []
def nh_34 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_34 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_34 : dagCheckRootsV5 m_34 g_34 ep_34 1 1 0 bds_34 (dagTraceF m_34 s_34 4 f_34) (cur_34 0) (nh_34 0) s_34 4 = true := by decide +kernel
theorem nc_34 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_34 g_34 ep_34 1 1 bds_34 0 (dagTraceF m_34 s_34 4 f_34) cur_34 nh_34 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_34 : LowerBin m_34 s_34 g_34 5 :=
  lowerDagV5 (kn_cons lb_1 (kn_nil)) rc_34 nc_34 (by decide +kernel)

def m_35 : Nat := 0xff000000ff00
def s_35 : List Nat := [0x550000005500, 0x330000003300, 0xf0000000f00, 0xff00]
def g_35 : Nat := 0x170000003700
def ep_35 : Nat := 0x200000000000000000000000000000000000000006000000040000001200000032000000140000000400
def bds_35 : List (Nat × List Nat × Nat × Nat) := [(m_14, s_14, 4, g_14)]
def cur_35 : Nat → List (Nat × Nat) := fun _ => []
def nh_35 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_35 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_35 : dagCheckRootsV5 m_35 g_35 ep_35 1 1 0 bds_35 (dagTraceF m_35 s_35 4 f_35) (cur_35 0) (nh_35 0) s_35 4 = true := by decide +kernel
theorem nc_35 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_35 g_35 ep_35 1 1 bds_35 0 (dagTraceF m_35 s_35 4 f_35) cur_35 nh_35 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_35 : LowerBin m_35 s_35 g_35 5 :=
  lowerDagV5 (kn_cons lb_14 (kn_nil)) rc_35 nc_35 (by decide +kernel)

def m_36 : Nat := 0xaaaa0000aaaa
def s_36 : List Nat := [0x222200002222, 0xa0a00000a0a, 0xaa000000aa, 0xaaaa]
def g_36 : Nat := 0x202000022aa
def ep_36 : Nat := 0x20a800000000000000000000000000000088000002020000000000000202000022000000000000000000
def bds_36 : List (Nat × List Nat × Nat × Nat) := []
def cur_36 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_36 : Nat → Nat := fun _ => 0
def f_36 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_36 : Nat → Bool := dagCheckNodeV5 m_36 g_36 ep_36 1 1 bds_36 1 (dagTraceF m_36 s_36 3 f_36) cur_36 nh_36
set_option maxHeartbeats 0 in
theorem rc_36 : dagCheckRootsV5 m_36 g_36 ep_36 1 1 1 bds_36 (dagTraceF m_36 s_36 3 f_36) (cur_36 0) (nh_36 0) s_36 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_36 : treeBlockF 0 1 ch_36 = true := by decide +kernel
theorem nc_36 : ∀ i, 0 ≤ i → i < 1 → ch_36 i = true := fun _ h1 h2 => treeBlockF_at nb_36 h1 h2
theorem lb_36 : LowerBin m_36 s_36 g_36 4 :=
  lowerDagV5 (kn_nil) rc_36 nc_36 (by decide +kernel)

def m_37 : Nat := 0xaa00aa00aa00aa00
def s_37 : List Nat := [0x2200220022002200, 0xa000a000a000a00, 0xaa000000aa00, 0xaa00aa00]
def g_37 : Nat := 0x20002002200
def ep_37 : Nat := 0x200200000000200000020000000000000000000000002000200000000000200020022000000000000000000
def bds_37 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_37 : Nat → List (Nat × Nat) := fun _ => []
def nh_37 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_37 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_37 : dagCheckRootsV5 m_37 g_37 ep_37 1 1 0 bds_37 (dagTraceF m_37 s_37 4 f_37) (cur_37 0) (nh_37 0) s_37 4 = true := by decide +kernel
theorem nc_37 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_37 g_37 ep_37 1 1 bds_37 0 (dagTraceF m_37 s_37 4 f_37) cur_37 nh_37 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_37 : LowerBin m_37 s_37 g_37 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_37 nc_37 (by decide +kernel)

def m_38 : Nat := 0x3300330033003300
def s_38 : List Nat := [0x1100110011001100, 0x300030003000300, 0x330000003300, 0x33003300]
def g_38 : Nat := 0x100130013003300
def ep_38 : Nat := 0x1200200000001200000020000000000000000000010002000200000000000000000000000100100010000000
def bds_38 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2), (m_3, s_3, 4, g_3), (m_6, s_6, 4, g_6), (m_12, s_12, 4, g_12)]
def cc_38_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xcc730ae2b0a86a0a461884210805f17c1e1781d15615054141501404c52144510405003c47805801 0x7d348f4a874682467946743d203544251815402414146e4d52456a35654d2d4561353c261016554c40340c1441345b4a53464e46493d213545253c460816324c274814340c2414340c24364a2e462a3a22361d46193610460836a237913771275c3738270417000f 10 1023 4 15 10 1023 16 65535
def cc_38_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x984c170b050a805020100440200 0xa94d854599358125a44d504568354c257d249e4d86459a357926944d2c4560351c15884c7d34 9 511 4 15 10 1023 16 65535
def cur_38 : Nat → List (Nat × Nat) := fun p => Bool.rec (cc_38_1 (Nat.sub p 32)) (cc_38_0 p) (Nat.blt p 32)
def hc_38_0 : Nat → Nat := unpackHintV5 0x860f0c01d123a00710ce201b832da65b00b6016812b475680a71942326873b487600ec01d023a007400e219a87320c5e18ae39446258c27900138000 0x4e6e02200586415a60dad5545a0ad39b942665566b5910608437408a0203a61035944 15 32767 6 63
def hc_38_1 : Nat → Nat := unpackHintV5 0xc206101dccec06a335007cc3c01e00d0830e006 0x14e7540e571014d8c00562302 13 8191 6 63
def nh_38 : Nat → Nat := fun p => Bool.rec (hc_38_1 (Nat.sub p 32)) (hc_38_0 p) (Nat.blt p 32)
def f_38 : Nat → Nat × Nat := unpackForestF 0xa54da44d0637964d9635944d0537774a884c774676467d347546743d0527624d6235614d613504373f4a554c3f463e463d3d3d2541343c4604270a4a324c0a460a3a27480a3609460936143408460c2408360417000f 6 10
def ch_38 : Nat → Bool := dagCheckNodeV5 m_38 g_38 ep_38 1 1 bds_38 43 (dagTraceF m_38 s_38 6 f_38) cur_38 nh_38
set_option maxHeartbeats 0 in
theorem rc_38 : dagCheckRootsV5 m_38 g_38 ep_38 1 1 43 bds_38 (dagTraceF m_38 s_38 6 f_38) (cur_38 0) (nh_38 0) s_38 6 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_0 : treeBlockF 0 32 ch_38 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_38_1 : treeBlockF 32 43 ch_38 = true := by decide +kernel
theorem nj_38_1 : ∀ i, 0 ≤ i → i < 43 → ch_38 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_38_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_38_1 h1 h2)
theorem nc_38 : ∀ i, 0 ≤ i → i < 43 → ch_38 i = true := nj_38_1
theorem lb_38 : LowerBin m_38 s_38 g_38 7 :=
  lowerDagV5 (kn_cons lb_2 (kn_cons lb_3 (kn_cons lb_6 (kn_cons lb_12 (kn_nil))))) rc_38 nc_38 (by decide +kernel)

def m_39 : Nat := 0xf000f000f000f000
def s_39 : List Nat := [0x5000500050005000, 0x3000300030003000, 0xf0000000f000, 0xf000f000]
def g_39 : Nat := 0x100010003000
def ep_39 : Nat := 0x1000200000001000000020000000000000000000000000000000000000001000100030000000100010000000
def bds_39 : List (Nat × List Nat × Nat × Nat) := [(m_6, s_6, 4, g_6)]
def cur_39 : Nat → List (Nat × Nat) := fun _ => []
def nh_39 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_39 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_39 : dagCheckRootsV5 m_39 g_39 ep_39 1 1 0 bds_39 (dagTraceF m_39 s_39 4 f_39) (cur_39 0) (nh_39 0) s_39 4 = true := by decide +kernel
theorem nc_39 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_39 g_39 ep_39 1 1 bds_39 0 (dagTraceF m_39 s_39 4 f_39) cur_39 nh_39 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_39 : LowerBin m_39 s_39 g_39 5 :=
  lowerDagV5 (kn_cons lb_6 (kn_nil)) rc_39 nc_39 (by decide +kernel)

def m_40 : Nat := 0xf000f000f000f00
def s_40 : List Nat := [0x500050005000500, 0x300030003000300, 0xf0000000f00, 0xf000f00]
def g_40 : Nat := 0x100070003000700
def ep_40 : Nat := 0x200000000000600000004000000000000000000000000000000000001000200030002000100040000000400
def bds_40 : List (Nat × List Nat × Nat × Nat) := [(m_0, s_0, 4, g_0)]
def cur_40 : Nat → List (Nat × Nat) := fun _ => []
def nh_40 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_40 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_40 : dagCheckRootsV5 m_40 g_40 ep_40 1 1 0 bds_40 (dagTraceF m_40 s_40 4 f_40) (cur_40 0) (nh_40 0) s_40 4 = true := by decide +kernel
theorem nc_40 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_40 g_40 ep_40 1 1 bds_40 0 (dagTraceF m_40 s_40 4 f_40) cur_40 nh_40 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_40 : LowerBin m_40 s_40 g_40 5 :=
  lowerDagV5 (kn_cons lb_0 (kn_nil)) rc_40 nc_40 (by decide +kernel)

def m_41 : Nat := 0xcc00cc00cc00cc
def s_41 : List Nat := [0x44004400440044, 0xc000c000c000c, 0xcc000000cc, 0xcc00cc]
def g_41 : Nat := 0x40044004400cc
def ep_41 : Nat := 0x40008800000040000000880000000000000000000400000000000000000000000000000004004400440000
def bds_41 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_41 : Nat → List (Nat × Nat) := fun _ => []
def nh_41 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_41 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_41 : dagCheckRootsV5 m_41 g_41 ep_41 1 1 0 bds_41 (dagTraceF m_41 s_41 4 f_41) (cur_41 0) (nh_41 0) s_41 4 = true := by decide +kernel
theorem nc_41 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_41 g_41 ep_41 1 1 bds_41 0 (dagTraceF m_41 s_41 4 f_41) cur_41 nh_41 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_41 : LowerBin m_41 s_41 g_41 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_41 nc_41 (by decide +kernel)

def m_42 : Nat := 0xffff0000
def s_42 : List Nat := [0x55550000, 0x33330000, 0xf0f0000, 0xff0000]
def g_42 : Nat := 0x13570000
def ep_42 : Nat := 0x440000000000000202000000000000130200000000000010540000
def bds_42 : List (Nat × List Nat × Nat × Nat) := []
def cur_42 : Nat → List (Nat × Nat) := unpackCursorV5 0x9 0xf 2 3 1 1 4 15 5 31
def nh_42 : Nat → Nat := fun _ => 0
def f_42 : Nat → Nat × Nat := unpackForestF 0xf 1 4
def ch_42 : Nat → Bool := dagCheckNodeV5 m_42 g_42 ep_42 1 1 bds_42 1 (dagTraceF m_42 s_42 3 f_42) cur_42 nh_42
set_option maxHeartbeats 0 in
theorem rc_42 : dagCheckRootsV5 m_42 g_42 ep_42 1 1 1 bds_42 (dagTraceF m_42 s_42 3 f_42) (cur_42 0) (nh_42 0) s_42 3 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_42 : treeBlockF 0 1 ch_42 = true := by decide +kernel
theorem nc_42 : ∀ i, 0 ≤ i → i < 1 → ch_42 i = true := fun _ h1 h2 => treeBlockF_at nb_42 h1 h2
theorem lb_42 : LowerBin m_42 s_42 g_42 4 :=
  lowerDagV5 (kn_nil) rc_42 nc_42 (by decide +kernel)

def m_43 : Nat := 0xff00ff00
def s_43 : List Nat := [0x55005500, 0x33003300, 0xf000f00, 0xff00]
def g_43 : Nat := 0x13003700
def ep_43 : Nat := 0x24000000000000000000000000000200040000000000130032000000000010000400
def bds_43 : List (Nat × List Nat × Nat × Nat) := []
def cc_43_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682b1560ac148a80d009c3382704e09c1382704648c1182304607c8f81f03a2740e81b1341680c841c001 0x793875346c2c68245c305d444f484b40453c4130384c3444302c2c24254c2144184c144408100924fe3ffa3be637d233c53fb93bb537ad33a92fa52b91277d23703f643b60375833542f502b3c2728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_43_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707062606052494841404040404040242020202004 0xf54cf140ec4ce840e128dd24d828d424cc38c834c018bc14b130b244a3489f40983c94308d4c894484188014 8 255 3 7 10 1023 16 65535
def cur_43 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_43_0 p) (Nat.blt p 32)
def hc_43_0 : Nat → Nat := unpackHintV5 0xa142548910a03a70c952850a142240810203460c1220405080400000 0x0 7 127 2 3
def hc_43_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3870c983054a1120344881020405081020402 0x0 7 127 2 3
def hc_43_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_43 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_43_2 (Nat.sub p 64)) (hc_43_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_43_0 p) (Nat.blt p 32)
def f_43 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633c838c834053fbc18bc14053b0537b2440533052f052b97489740943c94300527814c814480188014052375387534043f682c6824043b04375d440433042f042b43484340413c413004272c4c2c442c2c2c240423214c2144041f144c1444041b041709240413000f 6 10
def ch_43 : Nat → Bool := dagCheckNodeV5 m_43 g_43 ep_43 1 1 bds_43 64 (dagTraceF m_43 s_43 5 f_43) cur_43 nh_43
set_option maxHeartbeats 0 in
theorem rc_43 : dagCheckRootsV5 m_43 g_43 ep_43 1 1 64 bds_43 (dagTraceF m_43 s_43 5 f_43) (cur_43 0) (nh_43 0) s_43 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_0 : treeBlockF 0 32 ch_43 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_43_1 : treeBlockF 32 64 ch_43 = true := by decide +kernel
theorem nj_43_1 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_43_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_43_1 h1 h2)
theorem nc_43 : ∀ i, 0 ≤ i → i < 64 → ch_43 i = true := nj_43_1
theorem lb_43 : LowerBin m_43 s_43 g_43 6 :=
  lowerDagV5 (kn_nil) rc_43 nc_43 (by decide +kernel)

def m_44 : Nat := 0xf0f0f0f
def s_44 : List Nat := [0x5050505, 0x3030303, 0xf000f, 0xf0f]
def g_44 : Nat := 0x307070f
def ep_44 : Nat := 0x4080000000000040008000000000000000000000000030202000000000000040400
def bds_44 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_44 : Nat → List (Nat × Nat) := fun _ => []
def nh_44 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_44 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_44 : dagCheckRootsV5 m_44 g_44 ep_44 1 1 0 bds_44 (dagTraceF m_44 s_44 4 f_44) (cur_44 0) (nh_44 0) s_44 4 = true := by decide +kernel
theorem nc_44 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_44 g_44 ep_44 1 1 bds_44 0 (dagTraceF m_44 s_44 4 f_44) cur_44 nh_44 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_44 : LowerBin m_44 s_44 g_44 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_44 nc_44 (by decide +kernel)

def m_45 : Nat := 0xcccccccc
def s_45 : List Nat := [0x44444444, 0xc0c0c0c, 0xcc00cc, 0xcccc]
def g_45 : Nat := 0x4404cc
def ep_45 : Nat := 0x48800000000004400c8000000000000040000000000000000000000000000440400
def bds_45 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_45 : Nat → List (Nat × Nat) := fun _ => []
def nh_45 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_45 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_45 : dagCheckRootsV5 m_45 g_45 ep_45 1 1 0 bds_45 (dagTraceF m_45 s_45 4 f_45) (cur_45 0) (nh_45 0) s_45 4 = true := by decide +kernel
theorem nc_45 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_45 g_45 ep_45 1 1 bds_45 0 (dagTraceF m_45 s_45 4 f_45) cur_45 nh_45 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_45 : LowerBin m_45 s_45 g_45 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_45 nc_45 (by decide +kernel)

def m_46 : Nat := 0xff000000ff000000
def s_46 : List Nat := [0x5500000055000000, 0x3300000033000000, 0xf0000000f000000, 0xff000000]
def g_46 : Nat := 0x100000013000000
def ep_46 : Nat := 0x1200000000000000000000000000000000000000010000000200000001000000130000000100000010000000
def bds_46 : List (Nat × List Nat × Nat × Nat) := [(m_2, s_2, 4, g_2)]
def cur_46 : Nat → List (Nat × Nat) := fun _ => []
def nh_46 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_46 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_46 : dagCheckRootsV5 m_46 g_46 ep_46 1 1 0 bds_46 (dagTraceF m_46 s_46 4 f_46) (cur_46 0) (nh_46 0) s_46 4 = true := by decide +kernel
theorem nc_46 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_46 g_46 ep_46 1 1 bds_46 0 (dagTraceF m_46 s_46 4 f_46) cur_46 nh_46 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_46 : LowerBin m_46 s_46 g_46 5 :=
  lowerDagV5 (kn_cons lb_2 (kn_nil)) rc_46 nc_46 (by decide +kernel)

def m_47 : Nat := 0xf000f000f000f0
def s_47 : List Nat := [0x50005000500050, 0x30003000300030, 0xf0000000f0, 0xf000f0]
def g_47 : Nat := 0x100050005000f0
def ep_47 : Nat := 0x4000a000000040000000a00000000000000000000000000000000000100000000000000010005000500000
def bds_47 : List (Nat × List Nat × Nat × Nat) := [(m_10, s_10, 4, g_10)]
def cur_47 : Nat → List (Nat × Nat) := fun _ => []
def nh_47 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_47 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_47 : dagCheckRootsV5 m_47 g_47 ep_47 1 1 0 bds_47 (dagTraceF m_47 s_47 4 f_47) (cur_47 0) (nh_47 0) s_47 4 = true := by decide +kernel
theorem nc_47 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_47 g_47 ep_47 1 1 bds_47 0 (dagTraceF m_47 s_47 4 f_47) cur_47 nh_47 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_47 : LowerBin m_47 s_47 g_47 5 :=
  lowerDagV5 (kn_cons lb_10 (kn_nil)) rc_47 nc_47 (by decide +kernel)

def m_48 : Nat := 0xf0f00000f0f00000
def s_48 : List Nat := [0x5050000050500000, 0x3030000030300000, 0xf0000000f00000, 0xf0f00000]
def g_48 : Nat := 0x10000010500000
def ep_48 : Nat := 0x1040000000000000000000000010000000400000000000000000000000100000100000000010000010500000
def bds_48 : List (Nat × List Nat × Nat × Nat) := [(m_15, s_15, 4, g_15)]
def cur_48 : Nat → List (Nat × Nat) := fun _ => []
def nh_48 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_48 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_48 : dagCheckRootsV5 m_48 g_48 ep_48 1 1 0 bds_48 (dagTraceF m_48 s_48 4 f_48) (cur_48 0) (nh_48 0) s_48 4 = true := by decide +kernel
theorem nc_48 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_48 g_48 ep_48 1 1 bds_48 0 (dagTraceF m_48 s_48 4 f_48) cur_48 nh_48 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_48 : LowerBin m_48 s_48 g_48 5 :=
  lowerDagV5 (kn_cons lb_15 (kn_nil)) rc_48 nc_48 (by decide +kernel)

def m_49 : Nat := 0xf0f00000f0f0000
def s_49 : List Nat := [0x505000005050000, 0x303000003030000, 0xf0000000f0000, 0xf0f0000]
def g_49 : Nat := 0x107000003070000
def ep_49 : Nat := 0x200000000000000000000000006000000040000000000000000000001020000030200000104000000040000
def bds_49 : List (Nat × List Nat × Nat × Nat) := [(m_11, s_11, 4, g_11)]
def cur_49 : Nat → List (Nat × Nat) := fun _ => []
def nh_49 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_49 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_49 : dagCheckRootsV5 m_49 g_49 ep_49 1 1 0 bds_49 (dagTraceF m_49 s_49 4 f_49) (cur_49 0) (nh_49 0) s_49 4 = true := by decide +kernel
theorem nc_49 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_49 g_49 ep_49 1 1 bds_49 0 (dagTraceF m_49 s_49 4 f_49) cur_49 nh_49 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_49 : LowerBin m_49 s_49 g_49 5 :=
  lowerDagV5 (kn_cons lb_11 (kn_nil)) rc_49 nc_49 (by decide +kernel)

def m_50 : Nat := 0x5500aa005500aa
def s_50 : List Nat := [0xaa000000aa, 0x11002200110022, 0x5000a0005000a, 0x5500aa]
def g_50 : Nat := 0x150002005500aa
def ep_50 : Nat := 0x4000a800000000000000000000000000000000000400020000000000100002000000000000000000000000
def bds_50 : List (Nat × List Nat × Nat × Nat) := []
def cur_50 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0x1a4471b4371343927d8d5ed5949d1540f 7 127 3 7 6 63 10 1023
def nh_50 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_50 : Nat → Nat × Nat := unpackForestF 0xfa7536ed0caf472174aa0f 3 6
def ch_50 : Nat → Bool := dagCheckNodeV5 m_50 g_50 ep_50 1 1 bds_50 10 (dagTraceF m_50 s_50 4 f_50) cur_50 nh_50
set_option maxHeartbeats 0 in
theorem rc_50 : dagCheckRootsV5 m_50 g_50 ep_50 1 1 10 bds_50 (dagTraceF m_50 s_50 4 f_50) (cur_50 0) (nh_50 0) s_50 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_50 : treeBlockF 0 10 ch_50 = true := by decide +kernel
theorem nc_50 : ∀ i, 0 ≤ i → i < 10 → ch_50 i = true := fun _ h1 h2 => treeBlockF_at nb_50 h1 h2
theorem lb_50 : LowerBin m_50 s_50 g_50 5 :=
  lowerDagV5 (kn_nil) rc_50 nc_50 (by decide +kernel)

def m_51 : Nat := 0x55005500aa00aa
def s_51 : List Nat := [0xaa00aa, 0x11001100220022, 0x50005000a000a, 0x55000000aa]
def g_51 : Nat := 0x150055000200aa
def ep_51 : Nat := 0x40000000a80000000000000000000400000002000000100000000200000000000000000000
def bds_51 : List (Nat × List Nat × Nat × Nat) := []
def cur_51 : Nat → List (Nat × Nat) := unpackCursorV5 0x1a2d58b12a44874e0701 0xd2440c34d0c309343924cf626af2d592906842c00f 7 127 3 7 9 511 13 8191
def nh_51 : Nat → Nat := unpackHintV5 0x340c0b00c02c2b02c0b02c015002 0x0 10 1023 5 31
def f_51 : Nat → Nat × Nat := unpackForestF 0x33d33532dd3432573472421a21600f 3 9
def ch_51 : Nat → Bool := dagCheckNodeV5 m_51 g_51 ep_51 1 1 bds_51 10 (dagTraceF m_51 s_51 4 f_51) cur_51 nh_51
set_option maxHeartbeats 0 in
theorem rc_51 : dagCheckRootsV5 m_51 g_51 ep_51 1 1 10 bds_51 (dagTraceF m_51 s_51 4 f_51) (cur_51 0) (nh_51 0) s_51 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_51 : treeBlockF 0 10 ch_51 = true := by decide +kernel
theorem nc_51 : ∀ i, 0 ≤ i → i < 10 → ch_51 i = true := fun _ h1 h2 => treeBlockF_at nb_51 h1 h2
theorem lb_51 : LowerBin m_51 s_51 g_51 5 :=
  lowerDagV5 (kn_nil) rc_51 nc_51 (by decide +kernel)

def m_52 : Nat := 0x2222222222222222
def s_52 : List Nat := [0x202020202020202, 0x22002200220022, 0x222200002222, 0x22222222]
def g_52 : Nat := 0x2020202022222
def ep_52 : Nat := 0x200202000000200000020200002000000000000000202020202000000000000000000000000000000000000
def bds_52 : List (Nat × List Nat × Nat × Nat) := [(m_12, s_12, 4, g_12)]
def cur_52 : Nat → List (Nat × Nat) := fun _ => []
def nh_52 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_52 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_52 : dagCheckRootsV5 m_52 g_52 ep_52 1 1 0 bds_52 (dagTraceF m_52 s_52 4 f_52) (cur_52 0) (nh_52 0) s_52 4 = true := by decide +kernel
theorem nc_52 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_52 g_52 ep_52 1 1 bds_52 0 (dagTraceF m_52 s_52 4 f_52) cur_52 nh_52 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_52 : LowerBin m_52 s_52 g_52 5 :=
  lowerDagV5 (kn_cons lb_12 (kn_nil)) rc_52 nc_52 (by decide +kernel)

def m_53 : Nat := 0xa0a0a0a0a0a0a0a
def s_53 : List Nat := [0x202020202020202, 0xa000a000a000a, 0xa0a00000a0a, 0xa0a0a0a]
def g_53 : Nat := 0x202020202020a
def ep_53 : Nat := 0x200000800000200000000080002000000000008000000000000000000020202020202000000000000000000
def bds_53 : List (Nat × List Nat × Nat × Nat) := []
def cc_53_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb41682d05a0b4168292520a41482904a4941282314608c108a00c007c2f81f03a2740e81b1341680c841c001 0x724c6e40694c65405c3c5834542c5024492845243c2c38242c202d34253c2134183c143408100924fe3ffa3be637d233cd3fc93bb537a133952f892b85277d23783f743b60374c33402f342b302728231c1f101b0c170413000f 11 2047 5 31 10 1023 16 65535
def cc_53_1 : Nat → List (Nat × Nat) := unpackCursorV5 0xb0b0b0b0b0949090909074707070707070545050505034303022202012090801 0xf54cf140ec4ce840e128dd24d828d424c64cc240bc4cb840b13cad34a818a4149c28982490188c1481208234 8 255 3 7 10 1023 16 65535
def cur_53 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec ([]) (cc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_53_0 p) (Nat.blt p 32)
def hc_53_0 : Nat → Nat := unpackHintV5 0x950a0408101d3870e1c3260c1528508901a3060c1220405080400000 0x0 7 127 2 3
def hc_53_1 : Nat → Nat := unpackHintV5 0x9522448910a0408101d3254a142850890204080d1830488101420100 0x0 7 127 2 3
def hc_53_2 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def nh_53 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_53_2 (Nat.sub p 64)) (hc_53_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_53_0 p) (Nat.blt p 32)
def f_53 : Nat → Nat × Nat := unpackForestF 0x63f063be94ce940e84ce8400637d528d524d428d4240633053f053bba4cba40b84cb8400537a53ca534a418a414053398289824052f8c188c14052b052782340523043f043b664c6640654c65400437503c5034502c5024043345284524042f382c3824042b04272d340423213c2134041f143c1434041b041709240413000f 6 10
def ch_53 : Nat → Bool := dagCheckNodeV5 m_53 g_53 ep_53 1 1 bds_53 64 (dagTraceF m_53 s_53 5 f_53) cur_53 nh_53
set_option maxHeartbeats 0 in
theorem rc_53 : dagCheckRootsV5 m_53 g_53 ep_53 1 1 64 bds_53 (dagTraceF m_53 s_53 5 f_53) (cur_53 0) (nh_53 0) s_53 5 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_0 : treeBlockF 0 32 ch_53 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_53_1 : treeBlockF 32 64 ch_53 = true := by decide +kernel
theorem nj_53_1 : ∀ i, 0 ≤ i → i < 64 → ch_53 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_53_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_53_1 h1 h2)
theorem nc_53 : ∀ i, 0 ≤ i → i < 64 → ch_53 i = true := nj_53_1
theorem lb_53 : LowerBin m_53 s_53 g_53 6 :=
  lowerDagV5 (kn_nil) rc_53 nc_53 (by decide +kernel)

def m_54 : Nat := 0x5a005a005a005a
def s_54 : List Nat := [0xa000a000a000a, 0x12001200120012, 0x5a0000005a, 0x5a005a]
def g_54 : Nat := 0x1200520052005a
def ep_54 : Nat := 0x40000800000040000000080000000000000000000000000000000000120002000200000000000000000000
def bds_54 : List (Nat × List Nat × Nat × Nat) := []
def cur_54 : Nat → List (Nat × Nat) := unpackCursorV5 0x16ac58b12a44890e8701 0x193430d19282090d28209263a88d9d3a54d903a10d800f 7 127 3 7 10 1023 14 16383
def nh_54 : Nat → Nat := unpackHintV5 0x340d0340d0302c0300c02c215002 0x0 10 1023 5 31
def f_54 : Nat → Nat × Nat := unpackForestF 0xc7463629d64a0a6c43a494209086c00f 3 10
def ch_54 : Nat → Bool := dagCheckNodeV5 m_54 g_54 ep_54 1 1 bds_54 10 (dagTraceF m_54 s_54 4 f_54) cur_54 nh_54
set_option maxHeartbeats 0 in
theorem rc_54 : dagCheckRootsV5 m_54 g_54 ep_54 1 1 10 bds_54 (dagTraceF m_54 s_54 4 f_54) (cur_54 0) (nh_54 0) s_54 4 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_54 : treeBlockF 0 10 ch_54 = true := by decide +kernel
theorem nc_54 : ∀ i, 0 ≤ i → i < 10 → ch_54 i = true := fun _ h1 h2 => treeBlockF_at nb_54 h1 h2
theorem lb_54 : LowerBin m_54 s_54 g_54 5 :=
  lowerDagV5 (kn_nil) rc_54 nc_54 (by decide +kernel)

def m_55 : Nat := 0xc0c0c0c0c0c0c0c
def s_55 : List Nat := [0x404040404040404, 0xc000c000c000c, 0xc0c00000c0c, 0xc0c0c0c]
def g_55 : Nat := 0x404040004040c
def ep_55 : Nat := 0x800000400000004080004000000040008000000000000000000000000000000000004040400040400
def bds_55 : List (Nat × List Nat × Nat × Nat) := [(m_13, s_13, 4, g_13)]
def cur_55 : Nat → List (Nat × Nat) := fun _ => []
def nh_55 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_55 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_55 : dagCheckRootsV5 m_55 g_55 ep_55 1 1 0 bds_55 (dagTraceF m_55 s_55 4 f_55) (cur_55 0) (nh_55 0) s_55 4 = true := by decide +kernel
theorem nc_55 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_55 g_55 ep_55 1 1 bds_55 0 (dagTraceF m_55 s_55 4 f_55) cur_55 nh_55 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_55 : LowerBin m_55 s_55 g_55 5 :=
  lowerDagV5 (kn_cons lb_13 (kn_nil)) rc_55 nc_55 (by decide +kernel)

def m_56 : Nat := 0xaaaaaaaaaaaaaaaa
def s_56 : List Nat := [0x2222222222222222, 0xa0a0a0a0a0a0a0a, 0xaa00aa00aa00aa, 0xaaaa0000aaaa, 0xaaaaaaaa]
def g_56 : Nat := 0x20202020222aa
def ep_56 : Nat := 0x20020a800000200000020a80002000000000088000202020202000000020202020222000000000000000000
def bds_56 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 6, g_53)]
def cur_56 : Nat → List (Nat × Nat) := fun _ => []
def nh_56 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_56 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_56 : dagCheckRootsV5 m_56 g_56 ep_56 1 1 0 bds_56 (dagTraceF m_56 s_56 6 f_56) (cur_56 0) (nh_56 0) s_56 6 = true := by decide +kernel
theorem nc_56 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_56 g_56 ep_56 1 1 bds_56 0 (dagTraceF m_56 s_56 6 f_56) cur_56 nh_56 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_56 : LowerBin m_56 s_56 g_56 7 :=
  lowerDagV5 (kn_cons lb_53 (kn_nil)) rc_56 nc_56 (by decide +kernel)

def m_57 : Nat := 0x5555555555555555
def s_57 : List Nat := [0x1111111111111111, 0x505050505050505, 0x55005500550055, 0x555500005555, 0x55555555]
def g_57 : Nat := 0x115155511551555
def ep_57 : Nat := 0x1040000000001440000004000014004000440040010404000000040001101000110010000000000000000000
def bds_57 : List (Nat × List Nat × Nat × Nat) := [(m_28, s_28, 7, g_28)]
def cur_57 : Nat → List (Nat × Nat) := fun _ => []
def nh_57 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_57 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_57 : dagCheckRootsV5 m_57 g_57 ep_57 1 1 0 bds_57 (dagTraceF m_57 s_57 7 f_57) (cur_57 0) (nh_57 0) s_57 7 = true := by decide +kernel
theorem nc_57 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_57 g_57 ep_57 1 1 bds_57 0 (dagTraceF m_57 s_57 7 f_57) cur_57 nh_57 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_57 : LowerBin m_57 s_57 g_57 8 :=
  lowerDagV5 (kn_cons lb_28 (kn_nil)) rc_57 nc_57 (by decide +kernel)

def m_58 : Nat := 0xff00ff00ff00ff00
def s_58 : List Nat := [0x5500550055005500, 0x3300330033003300, 0xf000f000f000f00, 0xff000000ff00, 0xff00ff00]
def g_58 : Nat := 0x100170013003700
def ep_58 : Nat := 0x1200200000001600000024000000000000000000010006000200040001001200130032000100140010000400
def bds_58 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20), (m_38, s_38, 7, g_38), (m_39, s_39, 5, g_39), (m_34, s_34, 5, g_34), (m_40, s_40, 5, g_40), (m_37, s_37, 5, g_37), (m_35, s_35, 5, g_35), (m_46, s_46, 5, g_46), (m_43, s_43, 6, g_43)]
def cur_58 : Nat → List (Nat × Nat) := unpackCursorV5 0x13098486411188442030078bc1e0e1703443801 0x3240cd51d40795092028d3e4fe92f647b90e94f952e147650d52f44acd27148c01f 9 511 4 15 10 1023 14 16383
def nh_58 : Nat → Nat := unpackHintV5 0xacedba17b7945d28d76e816c1726f0636f054fe74cc833cffd318b723ddb16bd20fd6e03cc10003c00000 0x152aaaaac3b631d0c6355558c6b39cf33bce7558e7800000040000015561dbaa55872aaad4318c6ab5554e7d000800000000054aaaaaa319c63a872a8de318c6398c631aac73c0000002000000aab0edaa8c631aad500080004002aad54395563caaab52c635aad55539f4002000000045c0016b5aaaaaaac635aceb9675caa31bf631ad6318d555ef7bc00000040000015546318d54637ec6318d55f37cc631aaaa8e18c671c358c0040000000000631aaaaaa8ce38631c318c6aa31ac6318c637aabdef780000008000002aa8c631aa8c6bdaaad6b58008000002c55558c6b555ac6318deaaaf9be6b5ad555572ceb3ae18c60020000000002cb82ad52acba874aaab53def7aaad3f755470010000000000553c79555f37cd569fb39e8eb38ce339d5554e73d40020000000000aa739c6719d6aaaa78f2a9ce77bdef55aa8e7a780080000000002a9ce73aaad52ac7b60020000010ab54aaaf9be6aab554f9750e95556a8f0008000000001170555555001000000 20 1048575 8 255
def f_58 : Nat → Nat × Nat := unpackForestF 0x193c64b191f354190c54f152c547795054314bc52b149ca34148c01f 4 10
def ch_58 : Nat → Bool := dagCheckNodeV5 m_58 g_58 ep_58 3 7 bds_58 16 (dagTraceF m_58 s_58 8 f_58) cur_58 nh_58
set_option maxHeartbeats 0 in
theorem rc_58 : dagCheckRootsV5 m_58 g_58 ep_58 3 7 16 bds_58 (dagTraceF m_58 s_58 8 f_58) (cur_58 0) (nh_58 0) s_58 8 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_58 : treeBlockF 0 16 ch_58 = true := by decide +kernel
theorem nc_58 : ∀ i, 0 ≤ i → i < 16 → ch_58 i = true := fun _ h1 h2 => treeBlockF_at nb_58 h1 h2
theorem lb_58 : LowerBin m_58 s_58 g_58 9 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_38 (kn_cons lb_39 (kn_cons lb_34 (kn_cons lb_40 (kn_cons lb_37 (kn_cons lb_35 (kn_cons lb_46 (kn_cons lb_43 (kn_nil)))))))))) rc_58 nc_58 (by decide +kernel)

def m_59 : Nat := 0xf0f0f0f0f0f0f0f0
def s_59 : List Nat := [0x5050505050505050, 0x3030303030303030, 0xf000f000f000f0, 0xf0f00000f0f0, 0xf0f0f0f0]
def g_59 : Nat := 0x101050105030f0
def ep_59 : Nat := 0x104020a000001040000020a000100040004000c0000000000000000000101000100030000010105010500000
def bds_59 : List (Nat × List Nat × Nat × Nat) := [(m_48, s_48, 5, g_48), (m_23, s_23, 5, g_23), (m_27, s_27, 5, g_27), (m_39, s_39, 5, g_39), (m_47, s_47, 5, g_47), (m_31, s_31, 5, g_31), (m_30, s_30, 5, g_30), (m_4, s_4, 4, g_4), (m_15, s_15, 4, g_15)]
def cur_59 : Nat → List (Nat × Nat) := unpackCursorV5 0x119 0xddf 3 7 1 1 5 31 6 63
def nh_59 : Nat → Nat := unpackHintV5 0x845000840000 0x9d4d6f7ac6738c9180407d2cf4338ce3b90b1e0c393656bd1a744 16 65535 8 255
def f_59 : Nat → Nat × Nat := unpackForestF 0xddf 1 5
def ch_59 : Nat → Bool := dagCheckNodeV5 m_59 g_59 ep_59 3 7 bds_59 2 (dagTraceF m_59 s_59 7 f_59) cur_59 nh_59
set_option maxHeartbeats 0 in
theorem rc_59 : dagCheckRootsV5 m_59 g_59 ep_59 3 7 2 bds_59 (dagTraceF m_59 s_59 7 f_59) (cur_59 0) (nh_59 0) s_59 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_59 : treeBlockF 0 2 ch_59 = true := by decide +kernel
theorem nc_59 : ∀ i, 0 ≤ i → i < 2 → ch_59 i = true := fun _ h1 h2 => treeBlockF_at nb_59 h1 h2
theorem lb_59 : LowerBin m_59 s_59 g_59 8 :=
  lowerDagV5 (kn_cons lb_48 (kn_cons lb_23 (kn_cons lb_27 (kn_cons lb_39 (kn_cons lb_47 (kn_cons lb_31 (kn_cons lb_30 (kn_cons lb_4 (kn_cons lb_15 (kn_nil)))))))))) rc_59 nc_59 (by decide +kernel)

def m_60 : Nat := 0x3333333333333333
def s_60 : List Nat := [0x1111111111111111, 0x303030303030303, 0x33003300330033, 0x333300003333, 0x33333333]
def g_60 : Nat := 0x113131313133333
def ep_60 : Nat := 0x1200202000001200000020200012000000000000010202020202000000000000000000000110101010100000
def bds_60 : List (Nat × List Nat × Nat × Nat) := [(m_38, s_38, 7, g_38)]
def cur_60 : Nat → List (Nat × Nat) := fun _ => []
def nh_60 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_60 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_60 : dagCheckRootsV5 m_60 g_60 ep_60 1 1 0 bds_60 (dagTraceF m_60 s_60 7 f_60) (cur_60 0) (nh_60 0) s_60 7 = true := by decide +kernel
theorem nc_60 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_60 g_60 ep_60 1 1 bds_60 0 (dagTraceF m_60 s_60 7 f_60) cur_60 nh_60 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_60 : LowerBin m_60 s_60 g_60 8 :=
  lowerDagV5 (kn_cons lb_38 (kn_nil)) rc_60 nc_60 (by decide +kernel)

def m_61 : Nat := 0xcccccccccccccccc
def s_61 : List Nat := [0x4444444444444444, 0xc0c0c0c0c0c0c0c, 0xcc00cc00cc00cc, 0xcccc0000cccc, 0xcccccccc]
def g_61 : Nat := 0x40444004404cc
def ep_61 : Nat := 0x400088000004400000048800040040004400c8000404000000040000000000000000000004044400440400
def bds_61 : List (Nat × List Nat × Nat × Nat) := [(m_5, s_5, 4, g_5), (m_41, s_41, 5, g_41), (m_25, s_25, 5, g_25), (m_31, s_31, 5, g_31), (m_55, s_55, 5, g_55), (m_45, s_45, 5, g_45), (m_32, s_32, 4, g_32), (m_10, s_10, 4, g_10), (m_13, s_13, 4, g_13)]
def cur_61 : Nat → List (Nat × Nat) := unpackCursorV5 0x292a42909525088e118421069da0681a05cd705855154150505405014035cd0340c1288a006401 0x992f7123b9516931d9294121ca496122282e5a40bb518a3e5232b13e4132183ea8169c5e925e895279445a505b50745e6b52625e5252495e415239452024284f1843eb4ee342d243c14fa143812f3123102e0822001f 10 1023 4 15 11 2047 16 65535
def nh_61 : Nat → Nat := unpackHintV5 0x10d999dc3f3b8006beb2d54298327af80e5e20eba81d4d282950551c0ea241515af22b00442148404505829fc0f3e01879828ea889cb0a2ccca58414b0801570a1a7081b598003680000 0x180274e00739cea00005c000006004d1a30018c639acc00006130000007340d88ce7180bde80000ce3c0e338d5e1b1e0f00037b459b00781b1e339c6a00000b362f73078ce71af78c6bb5eaab166cf3decdef7bdec38c6717b1cd18deaec07319ce71af5558b37b59ee039a0aaac16339c6000ce71aaad6b58000002a800ce71aa800000800701a09d180ce71a800c38b1162c 19 524287 8 255
def f_61 : Nat → Nat × Nat := unpackForestF 0xb4e0b42d9290a43ca49094fab51a93ea81609438c5e8a5e8952092f79443c5e3b523a5e5b503a52395e395239450923184f20241843082e0822001f 5 11
def ch_61 : Nat → Bool := dagCheckNodeV5 m_61 g_61 ep_61 3 7 bds_61 30 (dagTraceF m_61 s_61 7 f_61) cur_61 nh_61
set_option maxHeartbeats 0 in
theorem rc_61 : dagCheckRootsV5 m_61 g_61 ep_61 3 7 30 bds_61 (dagTraceF m_61 s_61 7 f_61) (cur_61 0) (nh_61 0) s_61 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_61 : treeBlockF 0 30 ch_61 = true := by decide +kernel
theorem nc_61 : ∀ i, 0 ≤ i → i < 30 → ch_61 i = true := fun _ h1 h2 => treeBlockF_at nb_61 h1 h2
theorem lb_61 : LowerBin m_61 s_61 g_61 8 :=
  lowerDagV5 (kn_cons lb_5 (kn_cons lb_41 (kn_cons lb_25 (kn_cons lb_31 (kn_cons lb_55 (kn_cons lb_45 (kn_cons lb_32 (kn_cons lb_10 (kn_cons lb_13 (kn_nil)))))))))) rc_61 nc_61 (by decide +kernel)

def m_62 : Nat := 0xff00ff00ff00ff
def s_62 : List Nat := [0x55005500550055, 0x33003300330033, 0xf000f000f000f, 0xff000000ff, 0xff00ff]
def g_62 : Nat := 0x170057005700ff
def ep_62 : Nat := 0x4000a800000040000000a80000000000000000000600020002000000120002000200000014005400540000
def bds_62 : List (Nat × List Nat × Nat × Nat) := [(m_9, s_9, 4, g_9), (m_10, s_10, 4, g_10), (m_51, s_51, 5, g_51), (m_50, s_50, 5, g_50), (m_54, s_54, 5, g_54), (m_29, s_29, 5, g_29)]
def cc_62_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xb42b2ac2b099660946509060480200801b56c1b06c1b06499064145501405014048920480d507001 0xfa443c0910b5e40d68eb5238958d95632970bb5c20d34c34510934b24528d749a5d2457050360409872341a4d0845e1f168645216d5850560c910292410d783b5a08d481a560415a034f78d1dba4f6691d714f5451d11373449ca84f2211c48370209c001f 10 1023 4 15 11 2047 18 262143
def cc_62_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x88441dae870b81b2bc5c2e1709548225108132180c0601e8e070381c0a85028028000000 0x3f4b9f15d909afa174b06bd84ce4a642537a28a404de022ecd7352bae125d02e8609724b9835ca5a6e2d16149b7a45b5aed8976326cd926ac2e4e8d260694c5ea22d4b14a46ad1956 9 511 3 7 11 2047 17 131071
def cc_62_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xc29a21100 0x884c854c534d8745204d8245 6 63 3 7 9 511 16 65535
def cur_62 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (cc_62_2 (Nat.sub p 64)) (cc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_62_0 p) (Nat.blt p 32)
def hc_62_0 : Nat → Nat := unpackHintV5 0xed09ca437c66c8cbb797602e815d00b90546b28c05180a3010cea180430084090411e883a0c6e18a2e944028804f089a111481f8c391838e801c0000 0x3fd3d13fdff0d555005103c000141540003e20019660000880f00fff13d3df7fc905550001103c43ffd0f53fdff2555400001440f055550410041000 15 32767 6 63
def hc_62_1 : Nat → Nat := unpackHintV5 0xd000d000af42af00ae02ae00ad029530950095009500744274007302730072025a305a005a005a00384438003800360434042c10260c200c023c020002000004 0x5b6d5fb555550c484155557dd754015d5555d757d4312150550f30c000004d4d30c0f0300000fff1f43df7fc341554440f10000f 16 65535 7 127
def hc_62_2 : Nat → Nat := unpackHintV5 0xd00c82c80c02030000 0x55fb6d555500 12 4095 6 63
def nh_62 : Nat → Nat := fun p => Bool.rec (Bool.rec (hc_62_2 (Nat.sub p 64)) (hc_62_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_62_0 p) (Nat.blt p 32)
def f_62 : Nat → Nat × Nat := unpackForestF 0x2204c82516114c821140b4f7a971e95d7a1740b4776131c14572531c0450293da35c68575a05d0291d925c5ed15835c5e914094f56d755a5d561700947471791c5a4c8d13034471491b5646558093736d78db5a3c910f02436d48da5636558092732970b3452ed70b2450213c935d24974915c0211c545e151686a341a4d0545214d585056020dc135e04d682a440a49013520495810560209c001f 7 11
def ch_62 : Nat → Bool := dagCheckNodeV5 m_62 g_62 ep_62 2 3 bds_62 69 (dagTraceF m_62 s_62 7 f_62) cur_62 nh_62
set_option maxHeartbeats 0 in
theorem rc_62 : dagCheckRootsV5 m_62 g_62 ep_62 2 3 69 bds_62 (dagTraceF m_62 s_62 7 f_62) (cur_62 0) (nh_62 0) s_62 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_0 : treeBlockF 0 32 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_1 : treeBlockF 32 64 ch_62 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_62_2 : treeBlockF 64 69 ch_62 = true := by decide +kernel
theorem nj_62_1 : ∀ i, 0 ≤ i → i < 64 → ch_62 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_62_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_62_1 h1 h2)
theorem nj_62_2 : ∀ i, 0 ≤ i → i < 69 → ch_62 i = true := block_join nj_62_1 (fun _ h1 h2 => treeBlockF_at nb_62_2 h1 h2)
theorem nc_62 : ∀ i, 0 ≤ i → i < 69 → ch_62 i = true := nj_62_2
theorem lb_62 : LowerBin m_62 s_62 g_62 8 :=
  lowerDagV5 (kn_cons lb_9 (kn_cons lb_10 (kn_cons lb_51 (kn_cons lb_50 (kn_cons lb_54 (kn_cons lb_29 (kn_nil))))))) rc_62 nc_62 (by decide +kernel)

def m_63 : Nat := 0xf0f0f0f0f0f0f0f
def s_63 : List Nat := [0x505050505050505, 0x303030303030303, 0xf000f000f000f, 0xf0f00000f0f, 0xf0f0f0f]
def g_63 : Nat := 0x10707070307070f
def ep_63 : Nat := 0x200000800000600000004080006000000040008000000000000000001020202030202000104040400040400
def bds_63 : List (Nat × List Nat × Nat × Nat) := [(m_53, s_53, 6, g_53), (m_40, s_40, 5, g_40), (m_24, s_24, 5, g_24), (m_49, s_49, 5, g_49), (m_44, s_44, 5, g_44), (m_55, s_55, 5, g_55), (m_19, s_19, 5, g_19), (m_0, s_0, 4, g_0), (m_13, s_13, 4, g_13)]
def cur_63 : Nat → List (Nat × Nat) := unpackCursorV5 0xb2691e71c7131c1 0x214d3495a4d249934a391894678dd537149c01f 6 63 2 3 10 1023 14 16383
def nh_63 : Nat → Nat := unpackHintV5 0xdf00ac66ac00707870006791620b3658006c0000 0x1416ad5d8de342e73c79d2700018d7a0b1ac631ec60f39e3be8671ec73b6005bd608d01aa3540f1e9a00005a802c63468001e3cc7471e 16 65535 7 127
def f_63 : Nat → Nat × Nat := unpackForestF 0x214d18dda4d14dcb4a2918946149c01f 4 10
def ch_63 : Nat → Bool := dagCheckNodeV5 m_63 g_63 ep_63 3 7 bds_63 9 (dagTraceF m_63 s_63 7 f_63) cur_63 nh_63
set_option maxHeartbeats 0 in
theorem rc_63 : dagCheckRootsV5 m_63 g_63 ep_63 3 7 9 bds_63 (dagTraceF m_63 s_63 7 f_63) (cur_63 0) (nh_63 0) s_63 7 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_63 : treeBlockF 0 9 ch_63 = true := by decide +kernel
theorem nc_63 : ∀ i, 0 ≤ i → i < 9 → ch_63 i = true := fun _ h1 h2 => treeBlockF_at nb_63 h1 h2
theorem lb_63 : LowerBin m_63 s_63 g_63 8 :=
  lowerDagV5 (kn_cons lb_53 (kn_cons lb_40 (kn_cons lb_24 (kn_cons lb_49 (kn_cons lb_44 (kn_cons lb_55 (kn_cons lb_19 (kn_cons lb_0 (kn_cons lb_13 (kn_nil)))))))))) rc_63 nc_63 (by decide +kernel)

def m_64 : Nat := 0xffffffff
def s_64 : List Nat := [0x55555555, 0x33333333, 0xf0f0f0f, 0xff00ff, 0xffff]
def g_64 : Nat := 0x135737ff
def ep_64 : Nat := 0x24a800000000004400c8000000000202040000000000130232000000000010540400
def bds_64 : List (Nat × List Nat × Nat × Nat) := [(m_43, s_43, 6, g_43)]
def cur_64 : Nat → List (Nat × Nat) := fun _ => []
def nh_64 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_64 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_64 : dagCheckRootsV5 m_64 g_64 ep_64 1 1 0 bds_64 (dagTraceF m_64 s_64 6 f_64) (cur_64 0) (nh_64 0) s_64 6 = true := by decide +kernel
theorem nc_64 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_64 g_64 ep_64 1 1 bds_64 0 (dagTraceF m_64 s_64 6 f_64) cur_64 nh_64 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_64 : LowerBin m_64 s_64 g_64 7 :=
  lowerDagV5 (kn_cons lb_43 (kn_nil)) rc_64 nc_64 (by decide +kernel)

def m_65 : Nat := 0xffff0000ffff
def s_65 : List Nat := [0x555500005555, 0x333300003333, 0xf0f00000f0f, 0xff000000ff, 0xffff]
def g_65 : Nat := 0x1757000037ff
def ep_65 : Nat := 0x20a8000000000000000000000040000000c8000006020000040000001202000032000000145400000400
def bds_65 : List (Nat × List Nat × Nat × Nat) := [(m_18, s_18, 6, g_18)]
def cur_65 : Nat → List (Nat × Nat) := fun _ => []
def nh_65 : Nat → Nat := unpackHintV5 0x2 0x0 4 15 2 3
def f_65 : Nat → Nat × Nat := fun _ => (0, 0)
set_option maxHeartbeats 0 in
theorem rc_65 : dagCheckRootsV5 m_65 g_65 ep_65 1 1 0 bds_65 (dagTraceF m_65 s_65 5 f_65) (cur_65 0) (nh_65 0) s_65 5 = true := by decide +kernel
theorem nc_65 : ∀ i, 0 ≤ i → i < 0 → dagCheckNodeV5 m_65 g_65 ep_65 1 1 bds_65 0 (dagTraceF m_65 s_65 5 f_65) cur_65 nh_65 i = true := fun _ _ h => absurd h (Nat.not_lt_zero _)
theorem lb_65 : LowerBin m_65 s_65 g_65 6 :=
  lowerDagV5 (kn_cons lb_18 (kn_nil)) rc_65 nc_65 (by decide +kernel)

def g_66 : Nat := 0x1171757135737ff
def ep_66 : Nat := 0x124020a800001640000024a800160040004400c8010606020202040001121202130232000114145410540400
def bds_66 : List (Nat × List Nat × Nat × Nat) := [(m_20, s_20, 7, g_20), (m_21, s_21, 7, g_21), (m_63, s_63, 8, g_63), (m_59, s_59, 8, g_59), (m_60, s_60, 8, g_60), (m_57, s_57, 8, g_57), (m_61, s_61, 8, g_61), (m_62, s_62, 8, g_62), (m_28, s_28, 7, g_28), (m_56, s_56, 7, g_56), (m_38, s_38, 7, g_38), (m_65, s_65, 6, g_65), (m_64, s_64, 7, g_64), (m_13, s_13, 4, g_13), (m_14, s_14, 4, g_14), (m_53, s_53, 6, g_53), (m_15, s_15, 4, g_15), (m_10, s_10, 4, g_10), (m_43, s_43, 6, g_43), (m_58, s_58, 9, g_58), (m_52, s_52, 5, g_52), (m_33, s_33, 5, g_33), (m_49, s_49, 5, g_49), (m_26, s_26, 5, g_26), (m_7, s_7, 4, g_7), (m_12, s_12, 4, g_12), (m_36, s_36, 4, g_36), (m_18, s_18, 6, g_18), (m_11, s_11, 4, g_11), (m_32, s_32, 4, g_32), (m_23, s_23, 5, g_23), (m_46, s_46, 5, g_46), (m_0, s_0, 4, g_0), (m_2, s_2, 4, g_2), (m_50, s_50, 5, g_50), (m_1, s_1, 4, g_1), (m_16, s_16, 5, g_16), (m_8, s_8, 4, g_8), (m_6, s_6, 4, g_6), (m_39, s_39, 5, g_39), (m_17, s_17, 5, g_17), (m_51, s_51, 5, g_51), (m_42, s_42, 4, g_42)]
def cc_66_0 : Nat → List (Nat × Nat) := unpackCursorV5 0xaa05502a03500a80510e881401a0050028013c19a14d02603300960cb02580f0f7803b05d80ec07213901c02e006e0b3100e4001 0xee7206e3f030dfc1a2880c4530523e02b9c8138e608c7e03eb904f5bc25ac611c6f08a3183f17c1e8b60e4570662982edbc166be09357041a781cd1c0d4dc060660282a010510070880286c00c2201317c068b60245700a29e0917f028b77f457be629dead7ef36b778b57b95a9dbcd3ed869769347b2da1d8097eb74af56a4fa0123ce88fe6946f2a15f904adc5855e152a6fd14f7bca5bba51dc1286d113f6589db064dd6f266ac92b4d893a4c17d1b0b67605739c2997613cba0965484729c219080fc83076360371ac198d00ac5804e1901f0a00d81605c010260003f 13 8191 6 63 11 2047 21 2097151
def cc_66_1 : Nat → List (Nat × Nat) := unpackCursorV5 0x9826090a408c603801f17c1f0749d03f8f0384e0344d0304c0300a21906018051140410882008002 0x7b1f1d97c76d8df672791cdd16c70511b5726a572b56fa758e846f9d18e545f9116e2c578514e036f7ed7dcb576ed3da347665b988545e111686c5651150446117d745b5915d4c534c5512164415b89b67435f90472 10 1023 4 15 11 2047 18 262143
def cc_66_2 : Nat → List (Nat × Nat) := unpackCursorV5 0xe870781b1d8686331080c0200e27038184c049a41209031980a250280c86030090400200 0x2f57eb91fad572cf58f346fcb18f1c5fc314ef96fba57ed94fb251eb964aa952a154a49928964995b9e3679e5126d7e991ca5954925123e728c5b22244865120964 9 511 4 15 11 2047 18 262143
def cc_66_3 : Nat → List (Nat × Nat) := unpackCursorV5 0xf06cf61b0c9642e570b850e8140914824111883c8d260301808440201008031180482001 0x1fe303f16d7629af91c9ee2c3cc606f0ecee97dd92bb706674ae4e6d41c2b8378476e07b0318a012fbea577a2bef055dd4a6b9127710d4da199aa2fb4c5364afcc51f980bfb0453 9 511 4 15 11 2047 19 524287
def cc_66_4 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c27090e2288220791e0781e06cdb06c1926418160180601806012648120480f312c401001300400 0x13cd9274b2c6135962ff164d669b64a97f992db144d65db24b25f954af26dfa49aa4836c8eadf1b58e3137c5a5f8a4af0c49a223f43b4886289495be86b1cfb6e9c4df3697e612bca16f912bf1e55e249ac29277c2bf044d5d093bb94d 10 1023 4 15 11 2047 19 524287
def cc_66_5 : Nat → List (Nat × Nat) := unpackCursorV5 0xb02c0a11db741d0705c0689a06098058960581604cd3048520444a7280912409018c60180330c003 0xc0afd7edcaf9ac5e954e58ddc4dbf7db1ee26fd847fa88df44b7e3945c427f824def093dc945b7ad162576d5b65816db3ad15e572c5b7d8363af2dd5adb2ae305c562b66df68d8ec8b7d715dac27f544dea01a53364a52cb1c4d68daa511558d26b405564ca7c4127 10 1023 4 15 11 2047 19 524287
def cc_66_6 : Nat → List (Nat × Nat) := unpackCursorV5 0xe07032790c86428b40a0502090080389c0e070345a0d068341a049201004420100080000 0xde8c9ba59728a2edb7eda6a9a45ff24aaec935d78e5ad16320aaea94dd38c9a48ff39b668563cf6df9ad8f31afe5b53ca4df928ff211bde926c66fd8ad530e3961458 9 511 4 15 11 2047 19 524287
def cc_66_7 : Nat → List (Nat × Nat) := unpackCursorV5 0xb01602a15219c5306604c090520211c20803001f0be07c0e0cc81802c2580a0902200308600c00c618030003 0x7f47c7e97c380367dd70378367ba477c6807bb8c7cb7c7b2577a97c79c7078b587845f77b707717c8c34f8b34b89b478834387a4f852478423f82a377f96d7e14f7d1477a13f7913776927368360601675844748447545b74453731556012772464719656794570b546695570135 11 2047 5 31 11 2047 20 1048575
def cc_66_8 : Nat → List (Nat × Nat) := unpackCursorV5 0x942508c9e5781e0691a0645906416358160509314c13040d00310c02c4b02c083200802008020008 0x8f1448e8449245f90c5b8fc578e453389468d47c8217d8c945781278bb7c8ad708197d8a15d8937c88b6c8117d873438694f7c13f865708097d8595d7b13f84b7c83c708017d8314d8234f81b478124f80a47802377e94e7a93e77126 10 1023 4 15 11 2047 20 1048575
def cc_66_9 : Nat → List (Nat × Nat) := unpackCursorV5 0xb43682d0581b01586b05415a8b0160282500a012124044288110220402800f09c1114200308600c008810001 0x9fb609e47e9d5729c463abd6baa563a946fa8c6ba7c67a5c63a445fa1c53a0b62a016f9f1679e95f9d94f9c9479386f768675e05f4284f390479b83d9a135941279895d9593f9793595a5794b48944539ab4b99b439924f982479723f0695d9694f961479513f939279285491944910449006c 11 2047 5 31 11 2047 20 1048575
def cc_66_10 : Nat → List (Nat × Nat) := unpackCursorV5 0x8ca308c21284189601625816050940489204811144110440d4340c124c9024081200350c00300000 0xb057eaf954aea44ae144b6d6bb5563b446fb3c6bb2c67b0c63af45fadc53ad16ea1370ac358ab358aa954a3c52a9b68a8370a7348a6944a60449c03d78867a557ea4b58780779486fa3d7ea347ea2b48a21449407fa15699f9655f85f 10 1023 4 15 11 2047 20 1048575
def cc_66_11 : Nat → List (Nat × Nat) := unpackCursorV5 0xd060b0171b8586c151a8542a15091c822289401c4e070291408240200c460301800c0000 0xbf17cb896cbe154bd164bc17cbaa6cba16cb986cb8c65c0d6fbfd6bbed67bdd63bcb6fbbb67bb35fb9357b816eb7154b6254b5954b4964b317cb2244b1944b1044 9 511 4 15 11 2047 20 1048575
def cc_66_12 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c670986609826090a40799e0745d0705c05996054550541504c93048520445104402f0801104001 0xcf97cce97ccd16ccc86cd056bcf567ce367cdb5fcc357cb96ecac58c9c70c4965c395f9d1276185fc88342d027c7c70c6460c586cc4c60c3c72ca56bc9567c8462c7267c6a5fc5257c4167c315fc29579c927790676085f55057c204d2c827c1164c0154 10 1023 4 15 11 2047 20 1048575
def cc_66_13 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8750290d20a03402804c284b082103e27c0f05e03c0780f01e0306600c0170ae0582b01602a106808000800 0xe0364df865d2035deb54ddb7cdcb54dc055d4965d394f9e1276304f2e027dab64da065d937cd7b6cd716c9587f7b077d686dd606cd4b6cd3b7ed256fdf56fde56bdd567dbd63db36ed9a6fd8a67d825fd5a57d516fd4167d315fd29579d9279506f7a0676205f56057d18352d827d0954 11 2047 5 31 11 2047 20 1048575
def cc_66_14 : Nat → List (Nat × Nat) := unpackCursorV5 0xb860e801e2745d06c9b0685735c16158160509404c53048520480f33c0f03c0f03c0e12900a00000 0xefb63f7562f5b6ff536bf4367f1b63f116ff0167d293fc29379606f7d067ef05d4783f3c037ee164e3934e3134ec97ce2934e2024eb944e1934eb044ea164e927ce897ce7944e6944e6572e5a5ce515ce2034e3b5fe335be2b57e1b53edc6fed46bec467eac63e9b6fe8367e734fe4b47e416ee1134 10 1023 4 15 11 2047 20 1048575
def cc_66_15 : Nat → List (Nat × Nat) := unpackCursorV5 0xa8148690501528a0130a604c09052024048078cf0145242480900e21c0380608c01803006002504008000800 0x1fe8d8fe36385237424dbe116d707b67831b1c149be074cf0223f8011bbfe5bdfd2ced313f6189ba7a49d2d0de7e0677ec229220fc7a06e2e8277e4b23ec5f1f4488f99447c8223f11bdf78d6fac677c631be05b9e12caf6d687b032bd35c1e76d8f313477c36bca0d5e4068f0d60 11 2047 5 31 11 2047 21 2097151
def cc_66_16 : Nat → List (Nat × Nat) := unpackCursorV5 0xf078385c0e070381c0babe1a4d060b0180b1582c10680389c0e052281406430180c00600 0x21e6970eb4386da5c34d0e1949f0c24785d1fc5516e288a713b5f889abc40d3e1f2dd0e0188580a3fc5945e04f09c648423e41cd51fc0ab0683482e324131f2082f90337e815aa4071ca028b10094c 9 511 4 15 11 2047 21 2097151
def cc_66_17 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c2619825194250942238822088202801e2781d1741c13b8e02ccb020c711c0701c0610902000800 0x47cdf23cae11d37c8e5b64704d23569f1a3438ceb8464172306f9174708fda7c7ad2e3b68f1bb438d927c6291e2f47f16a3787cb6bfa53de028ed413f6209ba7c49e2b2890f01886c0a4525121d0310d0148640a448152264d91296c88c36430052212890b814 10 1023 4 15 11 2047 21 2097151
def cc_66_18 : Nat → List (Nat × Nat) := unpackCursorV5 0xb81702e05c0a4b482904c398130139a6048290110a20402801001c2380700e01c02c6580a09402420a010001 0x25ead12e95c9702ecb61709507f2cb643482fcb00d6688b733c57991a5cc2d0e604af2fa4f96923cae8fdff29ef11476a89fa8049c0d0bb2b0579542a9a213cb208e4a03f17c13ca6552512892796c9352249851249ce12416c91c3648a512432b92945f9422dc9d15e4b8a72535f919abc88d3e4268f2047c 11 2047 5 31 11 2047 21 2097151
def cc_66_19 : Nat → List (Nat × Nat) := unpackCursorV5 0x7e17e07e07837807047006a36a06624704604603e43e03e03073002652602410cc0c00c00c00c0082080080023020001 0x9fdaa4fad527c2ab3c1359e8aac0c53cdb09e088179e2b1a5e1bcd90bf2c16f9d89ecfd5ae7bac73cb6e95cb7c885ae2f2cf10163810afb9c54e7726a9706f420339b017e7506a1b81f0400bce11c2738b1391559b4a6ce15a6032bee61539bc9a9ae17c3603e078179b6b5c02579cb2a4830673542fcd651671ad737462908b5c5a59e002bee49539b0a6a0a19cd40bf3504d0d00f81c05e666c93283598db24c40d46004e4b03f 12 4095 5 31 11 2047 21 2097151
def cc_66_20 : Nat → List (Nat × Nat) := unpackCursorV5 0x9c09828888808808808808616ec6e06e06646606606606226206205c35c05c05c05c05a15625605605222f22e0017000 0x29e4a14c05da81b652e5b69f26b4a86da303653a0d03c03e09817a601a536dbe9a6d74cb67a5db1cba5ba262c4d713e5d4992621bd0b0ce4c83f1f81bd2ad8e5c2df4a1556b49fd1216e850af46a54a1c2dd0815e8806944b6ba1db1d0a9ae844c74945fa462bd2097e8f4b747257a3129d1692e8a48f2d85f91c2dc6415e230a74304ba0c23b580bd99056c58275cc11d5758aa86df5336ba85b3d38d8e5a2df2316b8c4b3c4458e962bad593f6609db144dd722669806f42833d26176820b9408502601f8fa0dc3903e09017 12 4095 5 31 11 2047 21 2097151
def cc_66_21 : Nat → List (Nat × Nat) := unpackCursorV5 0xec1c0f80700d85b0331d49a8148690501a01386704e09449c9301e43c0780b2160206400800c218011001000 0x57f1f2b92fb5f145af1be576db2b969f0414e748a157ad3eba6875c16d81ca7ba050db127ece13b6389baee4ceb62cb5a135ac8bed604d6af0695ab6facdb5d62d9eae6c72f96f928b5c6c59e272c6d813f66c9db1a4dd762669906f43c339360fc8006e1f81f0580bc925a6ac28a1f01f0540bd555a2a92cb4d95da402e5345b6a726b4786ca94a7d4850ea3ae15117da64aed1c1703d03e0a017 11 2047 5 31 11 2047 21 2097151
def cc_66_22 : Nat → List (Nat × Nat) := unpackCursorV5 0xcb1ca0c81c80c80c04a2fa209c39a19a098182b8018007276286205a42f62e02e02642602602602411a51a016200b000 0x2e38dd71362af533ca45ae3f2cf7094557895a9049d240d68c067b7c228d40ac6304e2501f0c00d83e05c090276e955994b7db44f5230d404012b71b74c85be502d71e9678a8b1db64d5350de9086b458339d418ed906a2401f0b80d83c05c060276b94511c0f83a05d140cf6a155b5ab149c5ae3b2cf6a95d47c35a2619ed30ba2281f0b00d83805c04026a3927aed32c72596d02aaa3127444328c409c1b02f64a6f934b54705995d254a21264d0378880741a02b3116fb349ea3c1a82b03568c6eb3db75909beba4cf3096f92cb5c6e59e282c76713556c95a8649d330de8e06b440339d018ecc06a3482b1841388407c290360c81700809d94d92c42cb649350600bd8adb2c78a763353b11a19ba13c9d07f6115d6d09fd90d0ec32ab0514f74ca1b664fd7926760855370279380fc4003e0b817 12 4095 5 31 11 2047 21 2097151
def cc_66_23 : Nat → List (Nat × Nat) := unpackCursorV5 0xea7ea0dc7dc0d82c2bb85b80b429509027e97a26895a75a05a05625605605605225205203ac1721600a6062022020001 0xc05b6600d82ff2dadd13f6789db244dd7d2677eb439f11fad84a95524c5103f1540e84c056fb29adc13f9ed1fdf8515b727ebd9335a895aa849efa08a5083f19c138a607c2502f5b24faa5239c613c5203a12015bdcaebd851ed16855aa4faa123df05561229efc14b7aca3bb650d68256a9127bd82a9c413cb608e330271400f84605eb44bf53a57acd2fd4c95e112befb95b7a8abbb454ef426ab392b54493d6493ea248f58a4fa8523de45b60f29efa94b7a0a3bb050d65256a7927ac12fd3e95df42b4f31565909529a498e00bef2957bb89edd6492ea04b7624bba521d5e53e9d28f0684f7c825bc811dd60877402fb9c11ac406d4c02f7145eab92fd3895e0c2bef895b78cabbaa54ef026ab092b52c939be17cb40af77838bb41adcc0d06504e2701f0880bdc855560256a51271901389a07c2102e2601f0800bd7c99d190cf7014d 12 4095 5 31 11 2047 21 2097151
def cc_66_24 : Nat → List (Nat × Nat) := unpackCursorV5 0x131984494e91048000000 0x2943fc195d6fd3fc1d556f93f60533c14552903f1581f09c179ca379fa3f9c637c0d456f13f6813b651375fd335b52b55d27 9 511 4 15 10 1023 20 1048575
def cur_66 : Nat → List (Nat × Nat) := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_24 (Nat.sub p 768)) (cc_66_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (cc_66_22 (Nat.sub p 704)) (cc_66_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (cc_66_20 (Nat.sub p 640)) (cc_66_19 (Nat.sub p 608)) (Nat.blt p 640)) (cc_66_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (cc_66_17 (Nat.sub p 544)) (cc_66_16 (Nat.sub p 512)) (Nat.blt p 544)) (cc_66_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (cc_66_14 (Nat.sub p 448)) (cc_66_13 (Nat.sub p 416)) (Nat.blt p 448)) (cc_66_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (cc_66_11 (Nat.sub p 352)) (cc_66_10 (Nat.sub p 320)) (Nat.blt p 352)) (cc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (cc_66_8 (Nat.sub p 256)) (cc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (cc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (cc_66_5 (Nat.sub p 160)) (cc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (cc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (cc_66_2 (Nat.sub p 64)) (cc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (cc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def hc_66_0 : Nat → Nat := unpackHintV5 0xa90240a4891e9d89c098215a92617088e26086a88e7daa4074da347011326f78266cd0aa639a4e5f291c568a285281024c119c4571a83f59863b88f436894030199c2bb91826c13e1e920c19e12c1361a00da96e05a202014118000050000000 0x707070780e0381ea3a0303032b0303030b0303a80c0c0c7c1701c0700c803030031304ad50b541d507540d5950340d550349d54151305555555555140114ac444450500055404a30707a07030307a81ea804c1305d50b541d0746d1b546d23566444c55042d406d2715128ea0ba81c1c1c1e80eaaaaa81ea31f05c84c2801c072212b542d592755665541d507565650544c15555555554500452b14141111001550128c0c0c3c3c1e0780c0e0380c6c5c4c1305d1b42d0b46d1b546d23543d0740d91131554142d2b501b49c544a3070f070f80e0380e48c5c5c8e540d52f05c0f01c03208c231542d43d55035540c1501513114ac444448c1128c015070f070f8ac0e0303a030381ea3030303030b0303a80c0c0c1703c0700c803030031304ad50b543d507540d5950340d550349d541513055555555540d5140114ac444451040d2700055404a3a31b0b13038303a31349d0349d4bc2709e8c0170b0b171307130f1307130f170b0b171384c0c4e1303331f1f028c0b002c000045d50b544d135544d275543d507540d59400015555555554000000b00001309c0000000410028c1c3c1c3c3c7c3c2c3c2c3c3c02b17172b0f07070f0f83c0c3e0f0300028c07001c004ad50b543d507543d0f5543d1f5540d59400015555555554000002b00000000000410028c1c1c1c1c1c0171b80e0300017542d50741d1b46d51b48d50364015546d23400b001b09c440a32348d2728c2c6e8e030307030f07a304c9d0740d2741327027a30707070b0707070707070700ac5c5c1e07030781c0c1c1c1c1c00070070028c013f542d50749d550741d5507541d503565000044c155555555540100003f00709c00000000000410028c0c0c1c3c1c3c0c0c200005d0b46d1b546d23543d0740d900551b48d002c006c2711028c7c5c5cae0380e0380c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0c00000028c8084cd50b543d507540d5950340d550349d54000155555555540000037000000000309c000410028c5c6ea83c1c1c3e000005d50b543d076646d1b546d2354015400b001b09c440a31f17172ba82eaa81ea0faaaa000000820028d2b542d50f541d5927556655656500005555555555000000ac000000000010400a3545c2c2c5c6c1c6c3c6c1c6c3c5c2c2c5c6e1b031b86c0cacacacac5c0b06c4c06c4c0ac3f0cc2b155175555451142c46d44440044002c2c2c2c2c2c2c2c2c2c2c2c2c2c2c2cacacacac2c0b02c0b0ac3f0dc2b10b55550b555a3555591442d55555555514005c5c5c5c17001542d50f541d5035650544c1555554500451111001550128c1c3c1c3c5c5c5c2c5c2c5c5c0c0c002aa17207a802800000000001555555555400000000000000001c3c1c3e17a82ea03aaa1781ea3aaa80000000001555555555400000000000000004a305c00b003c007022002000808000004001c1c1c1e0380e203171717170803000000000155555555400002c00070030009c000101c1c1c1e0380e2031717170b170b171700a003030000000000000555555555500000000000000000707070780e0381ea3a030303170303030b0303a80c0c0c0000000001555555555400000000000030000004a305c00b001c007000c03022000c030000c0000001001717170b170b1717070707070303000aaa000a2000000000055555555550000000000000000a82ea1707070707a03aaaaaa07a8c0000000001555555555400000000000000004a305c00b02000880007001c080302200000100070f070f85c0e030380c0e0705c5c5c2c5c2c5c5e80000c0c0000000000001555555555400000000000000004a301c3c1c3e170380c0e80c0e07a8c0c5c0c0c0c2c0c0ea030303000000000055555555550000000000000000128c17002c00f001c00302000c030000c0000001001717171717171717000000555555000000000000128c17002c00f001c003020000010043434343434343434343 24 16777215 10 1023
def hc_66_1 : Nat → Nat := unpackHintV5 0xb4711ab3b030b128a2aff04ea9f180a1023c9b4170931a0a8f70ea8a315083d1987d19ae7950f274a12c6dd1b468615c6071fc5b993655299c5089284b594c42c2263e3922342a842df18e23b2901ed1381739e60dea5409c9080708b00001c2 0x1c1c1c1c1c0171b80e030005551b4bd1742d0741d1b46d51b4bd503640044c0000a3442f4bd04c9ca30b1ba380c0c1c0c3c1e8c1341d034bd04c9c09e8e8cbc0d2c0c3c1c130272f1b170b170b2f1b0707070705002b17172b8bc0cae2f03070707070000000000550050155500000bc000000000000040707070b0707070707070700ac5c5c1e07030781c0c1c1c1c1c00070070028c01555555555401147542d5075550741d5507541d503565000044c000001c2700000000000028c4041f17172b80e0380e032f1b170b170b2f1b2b0f1f071f072b0f0500000000800005555515000000000000000000041f17172b80e0380e0303370303030b0303030f0303030703030000000a3202155555555540133542d50f541d50356540d035540d550000000000000000000a310105c6ea83c1c1c3e00001545d0b43d076646d1b546d2f540044c0000a3441f17172b2b1b170b170b2b1b2b0f1f071f072b0faaaa05000000000000555500501500000000000000001f17172ba82eaa81ea0faaaa000000820028d55555555540133542d50f541d595566556565000044c00000000000000028c404545c2c2c5c6c1c6c3c6c1c6c3c5c2c2c5c6e1b031b86c0ccccccccc5c0b06c4c06c4c16c470cc33155551415554514514141111001105c5c5c5c1700155555451542d50f541d5035650544c0044444400128d415070f070f1717170b170b17170303000aa2a00a0000000000055555555550000000000000000070f070f85ea0ba80eaa85e07a8eaaa00000000005555555555000017000000000004a30005c00b003c007022002000803022000001000707070780e0381c80c0c5c5c5c2c5c2c5c5c02800c0c0000000000001555555555400005c00000000001000707070780e0381ea3a030303170303030b0303a80c0c0c0000000001555555555400005c0000000000128c0017002c007001c00302000c030000c0000001001717170b170b1717070707070303000aaa000a881c000000000155555555540000000000000002a0ba85c1c1c1c1e80eaaaaa81ea300000000005555555555000017000000000004a30005c00b02000880007001c0808000004001c3c1c3e0380e03817170b170b178003000000000155555555400002c03c00030009c000101c3c1c3e0380e0381717170b170b1717a000030300000000000005555555555000017000000000000001c3c1c3e170380c0e80c0e07a8c0c5c0c0c0c2c0c0ea03030300000000005555555555000017000000000300004a30005c00b003c007000c03022000c030000c000000100171717171717171700000055555500001700000004a30005c00b003c007000c08000004001c3c1c1c2c1e8c1c1c1c1c1c1c1c5c2c2c5c1e07030781c0c1c1c1c1c5c0b01c1c01c4c01c0707c1f117542d50741d550749d5507541d5035650544c15555555554500450b14410749c1111001550128c1c2c1d07542d5170b0b170f07070f232323231702c0f01c2308c2b0ac45d550f5543c15055915131142c4448c1128d1001507070b0b070b07a30707070b0b0b170b0b170f07070f0f83c0c3e0f031702c0f01c0f0f00f1302b0ac45d50b543d507543d0f5543d275540d59415130555555543d5551401142c4451043d270440055404a303545c2c2c5c8c8c8c8da966a85c0b08c230ac2b2211755605415556451142c48c1128d111001580e170b0b17a83e07a82ea3aaaaaa2b1702ca084c0ac2b22117542d599559275543d507565650544c1555559555551401142c510649c1111001550128c5c2c2c5e80c0e0ba8e0380c0ea030f0303030703030303031702c2b003200c0c00c4c117542d50f541d50356540d035540d27550544c15555555554500450b111114410349c001550128e83c3c1c0c1c0eaa84c1305d0b46d1b546d23543d0766444c55042d406d2715128e0b03a80c1e031742d0f41d990340d113010b40d5128c1c3c1c3ea82ea03aaa81ea3aaa8cc1703c07282130884ad50b543d50756655649d559594151305555555555140114ac445050440055404a3 24 16777215 10 1023
def hc_66_2 : Nat → Nat := unpackHintV5 0xc6b8eebd6a54b998f4b0fa28ad30f2a6c19ca231249bd99692625e8cc9668671967cca6a78711672f1606bd9c665c9845cc2425918ea5680a651115c4a51b04481743b7a423798f832295c2b71ae265148207178174a4a11697808aa3000022a 0xf0f0f0f50760380c4c0b04c13004c13003c0700c80001c155450000028c1c3c1c3c3c3c2c3c2c3c3d52b17172b0f07070f0f83c0c3e0f0304c00b003c007003c0f0003c130000c08000001c00003c1300001555a341d50755404400000000000f09c000000028c000c0c1c3c1c3c0c0d644c0b04c13004c13003c0700c80004c155450000028c7c5c5cae0380e0380c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0d504c00b003c007000c0800300c000304c0000004c0000000155555a365640440000000000000309c0000028c02a83c1c1c3e544c00b003c072204c13004c13001300055514001b09c000a31f17172ba82eaa81ea0faaaa5413002c00f001c0813002200202000001300000000555565955a3011000000000000000000a3001f171717171f1f04c00b003c007000c08000004c00011751f54041300000000000000a3000f0f55541c1c1d541c1d45c2c2c5cae2f032b8bc0c1c1c1c1c5c0b07c4c07c4c01c0707c1f15541515554511141411110011501c3c1c1c2c1e8c1c1c1c1c1c1c1c5c2c2c5c1e07030781c0c1c1c1c1c5c0b01c1c01c4c01c0707c1f155555555545117542d50741d550755507541d5035650544c00445050444400128d415070b0741d50b545c2c2c5c3c1c1c3cac8c8cac5c0b03c070bc230ac2b1175543d552f5564544c44444104400541c2c1d07075550b0b555170b0b170f07070f2b8ac0cae2b031702c0f01c2b1302b1302b0ac55555054551444445050440045407070b0b070b07a30707070b0b0b170b0b170f07070f0f83c0c3e0f031702c0f01c0f0f00f1302b0ac555555543d5551445d50b543d507543d0f5543d5540d59415130011111414110004a350540d5170b0b172b23232b6a59aa1702c2f08c2b0ac8845d552f555564511104111100150303555170b0b172b072b0f2b072b0f6a55a5aa1702c2b1302b1302b0ac8855505455551444505044440045480e170b0b17a83e07a82ea3aaaaaa2b1702ca084c0ac2b221555559555551445d50b5665565550f541d5959415130011141411110004a350545c2c2c5e03980e03a5552b0f2f072f072b0f03035551702c2b0bc0320bc4c0bc4c15555554150511111114412f40011505c2c2c5e80c0e0ba8e0380c0ea030f0303030703030303031702c2b003200c0c00c4c155555555545117542d50f541d50356540d035540d550544c0044444451040d27000128d415a0f0f07030703aaa1304c551742d1b46d51b4bd50f41d99113011128d160b03a80c1e031742d0f41d990340d11301034a345070f070f2b1b170b170b2b1b0303555aa6a55a52f05c0f01c2b1302b1308855555054551444445050440044070f070faa0ba80eaaa07a8eaaa3305c0f01ca084c22155555555545133542d50f541d5995595565650544c00444450504400128d4150707070780e03980cac6c5c2c5c2cac6d56940c0d5547c1701c0700c81f1301f130555555505414444444505000440707070780e0381ea3a0303032b0303030b0303a80c0c0c7c1701c0700c803030031305555555555144cd50b541d507540d5950340d550355415130011111114410349c0004a350541c1e81c0c0c1ea07aa01304c551742d0741d1b46d51b4bd599113011128d14ac6c5c2c5c2cac6c1c1c1c1c0c0d556aa9556987c1707c4c07c4c01c0722155514155545111414111100112a0ba81c1c1c1e80eaaaaa81ea31f05c84c2801c0722155555555545133542d5955665541d507565650544c00445050444400128d415070f070f80e0380e48c5c5cbe540d52f05c0f01c0320bc231542d43d5503554bd15131111111040015070f070f80e0380e4ac6c5c2c5c2cac6e95540c0d554bc1703c0700c82b1302b130555555505414444444505000454070f070f8ac0e0303a030381ea303370303030b0303a80c0c0cdc1703c0700c8030300313055555555540d5144cd50b543d507540d5950340d550355415130011111114140004a3505414005c2c2c5c7c1cbc3c7c1cbc3c5c2c2c5cbe2f032f8bc0ccc7c7cdc00000000014540015554000000000000000100170b0b171307130f1307130f170b0b171384c0c4e1303331f1f37028c0b002c000055555555550045d50b544d135544d5543d507540d5940001130000000000000000a310101c3c1c3c3c7c3c2c3c2c3c3c02b17172b0f07070f0f83c0c3e0f0300028c07001c0055555555550056d50b543d507543d0f5543d1f5540d59400000000000000000028c404 24 16777215 10 1023
def hc_66_3 : Nat → Nat := unpackHintV5 0xbc68feb4021aaef144a9b150a1b2009c715093d2288f013489716483897a7db1767871507091f86d48d26c30466829026209885c915e57e92a5369204cd9a444621e3fc1283562982e19d2248a6420b8f41959d814613e0ac26808b08400022c 0x1b0b0b1b1082e47a8be4ba88e2381e07aa000002f41d41e48d55900fc022028c1c1c1c2c1c1c1ccc1c1c1c1c0a82ea47aa81e07aa81ea81ea07aaaaaaaa0000070070028c000000cd1741d41c1d41d0765a5990013000fc01c2700000020800a300000170b0b0f5aaaa0f07070f0f0f0f0f1b1b0f1b4b0f0f0f810f04c1304c5a30741d5550b68d1141b40c070f070faa9a2b1b170b170b2b1b55a5a0453305c0f01c882b1302b13055555555551444444450500044070f070f0f330f0b0f0b0f0f56a0baaa07a83eaa0faaa0f83eaaaaaaa803305c0f01c0f0f00f13084c28221555a341d50755555545114ac44505065804a3004407070707aaa9331b170b170b331ba555a0451f05c0701c881f1301f130555555555514444444505000440707070b070707330707070756a0ba91eaa0781eaa07aa07a81eaaaaaa0780ea801f05c07130070700701c84c2822155075075568d555554511441d2705104465804a300441f0b0b0f0aa1b0b0b1b0f07070f0f0f0f0f1f1f0f1f1f0f0f0f400a30701c002f555a42b00000070b07330aa1b0b0b1b072f4f07070707070707232307070707400701c0a3002f41d23555a443f0709c00000033171733aaaa331b170b170b231b4f0f23074f07230f50453305c088231302f1304cd55555659144511111414001452a83c1c1c3e004c2c4c2c2c5c4c6c3c1c1c3ea84c4c4c6c4dcc4c4c4c6c4c6c13004551b48d010a300b28c01b00c001f171733aaaa000000331b170b170b331b3b0f1f071f073b0fa0000000555554000500000000000000001f171733a82eaa81ea0faaaa004c4c4c2c4c2c4ccc4c3c4c1c4c1c4c3e84c4eaaaa84eaaa800004c000000115555555554001028c00fc0020800a3000000000b0b0b0baa82eaaaaa80000000005555555550002c00208000000282ea3aa37a8c01d50070b070b070b07070b070b5a0b80e82ea3aaa0ba8eaa0780c04c0701d07568d400b0b0b0b0b0b0b0baaaaaa0b0b030b0b0b0b0b0b0b0b0b2b234f234110b02c0b02c2b0fc88230bc42d550b5555559645000b0b0b0b0b0b0b0baaa0b80eaa82ea3aaaaa0ba8eaaa800b02c0b02c2b0fc88880b42d0b42d2b59a6644fc33171733a82eaa81ea0faaaa00cc1702130a0883345d596966441705c2709ca03a0228c01105c5c5c5e0380e0380c000001555554000000008a3000005c00b003c007000c00001010001c3c1c3e17a82ea03aaa1781ea3aaa8000000000155555555540000000000000a3000005c00b003c0070220020fc00808001010001c3c1c3e170380c0e80c0e07a8c0c5c0c0c0c2c0c0ea030303000000000055555555550000000000000c3f0028c000017002c00f001c00302000c030000c3f00004040017171717171717171f1f00000055555500000000028c000017002c00f001c003020004040007070b0b070b07a30707070b0b0b170b0b170f07070f0f83c0c3e0f0304c00b003c007003c0f0003c130000c08000001c00003c13000005d0b43d0743c3d43cbd4ad2b40413000000000003c2700000000a30080e170b0b17a83e07a82ea3aaaaaa2b04c00b02200204c000f001c08080000000004c00005d0b6962f52b47d990104c0000000000000000028c005c2c2c5e80c0e0ba8e3b0380c0ea030f03030307030303030304c00b003c007000c0800300c000304c0000004c000000005d0b4ad1f40d903035032f50104c0000000000000309c0000028c0283c3c1c0c1c0eaa84c0b04c13004c13003c07220000701b4bd1130000028c1c3c1c3ea82ea03aaa3b81ea3aaa813002c00f001c08800813002020000007000081300000cd1743d076962f5990104c0000000000000000028c000c0c3c3c1e0780c0e0380c4c1302c0b04c13004c13003c0700c800001c06c5c6d2f444c000000a3070f070f8ac0e0303a030381ea3030303030b0303a80c0c0c13002c00f001c00302000c030000c13000000070000000304c0045d0f41d03640c0d40cbd4041300000000000000c27000000a300a31b0b1b038b031304c0304c04e8c27a3545c2c2c5c6c1cbc3c7c1c6c3c5c2c2c5c6e2f032f86c0ccc7c7c13002c01304c001304c000f001c00302000000000130000568d0b542d5555011000000000000000000a300 24 16777215 10 1023
def hc_66_4 : Nat → Nat := unpackHintV5 0xd2d17ece212cc30ac6b7d2ceb18992ac8940a10ae09b117e99088296b0968b32e086214480397a7502ce6f097e634af05db1665761945221504d313c47b16041a9823ca14237016830d18c259ace1f49941b190c1539780dd9d805ba0800016e 0xc0c0007c1cec3c7c1cec3c5c2c2c5e80020300e0380c0000000000ec8d4ec8d45d0b4ed1f40d90000000000008000010070f070f80e0317030b032f03670303032303230303030f030703000001744d550000a388005c2c2c5c4c1c4c3c4c1c4c3e0380e80c0e80c0e0380c0c5c0c0c0c2c0c0c0c4c0c4c0c0c0c0c0c4c0c0c0c0c0c0c3c0c0c0c1c0c0c0028c0b002c000000001742d131351353b47d03640c0d40d400000000000a3202000001c3c1c3c3c7c3c2c3c2c3c3c080e0380e03a0303a0303035b0303030b0303030f030303070303030f030f03030303030f031f0303030300000a301c00700000011743d0743c3d43c7d40d9030350350000000000028c8080000070707073b1b170b170b3b1b030300080e0300e0300a000000000006745d0741d3b2353b2350364004c0000200000020000006c2c2c6c420380d1c0c2c0c8c0c8c0c0c0cbc0d2c0c0c0c1c0c1c0c00000bd075070355400028e201c1c1c2c1c1c1ccc1c1c1c1c080e03a0303a030380e0303470303030b030303070303030303030703070303030303070303030703030000070070028c0000011741d41c1d41d0740d90303503500130000709c0000000a32020000000c0d554dc1cdc3cdc1cdc3c5c2c2c5e81520340e0380cdc4c0dc4c05c0b1dc7700c85555555555145050444445800441b0f1f0f0386c0ddc0c3c0c7c0e8e8e8c1cdc1c6c0e1b03770367030703a3a32f49ca3545c2c2c5c6c1ccc3ccc1c6c3e0380e80c0c0c0e33a030380e0303170303030b0303031b031b0303030303330303030303030f030303070303005c0b06c4c0bc4c000c80303003130568d0b542d555555551444505044128d81900440303070f070f170b0b0f1b0f1b0f0f0f1b0f370f0f0f503034880e031304c0f04c555a30741d544442b1b170b170b2b1b070f070f030355580e03a05480d033b05c2b1302b1300f01c0321555555555451114141111001101c3c1c3c3ccc3c2c3c2c3c3d580e0380e03a0303a0303030303030b0303030f030303070303030f030f03030303030f030303030300ec1703c0703c3c03c4c00c8030300313055568d07541d5555551444445050128d819004407070707671b170b170b671b030355580e0340e0354a01f05c0701c1f1301f13003215555555554511111414116001101c1c1c2c1c1c1ccc1c1c1c1d580e0381e80c0e80c0c0c0e0380c0d1c0c0c0c2c0c0c0c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c1c0c0c01f05c07130070700701c03200c0c00c4c155075075568d55555451114141104a3606401103c1c2c1e8c1c1c1c1c5c2c2c5c1c1c1c1cdcdc1c8c8c1c1c1c1c1c1c1e0380d101c1304c131540d0351f44445070b0b07a307070b0b170b0b170f07070f0f0f0f0f37370f23230f0f0f80c0c0c3e80d103c1304c131543d2340d0353b444450070f070f170b0b17131313132f371323231313130f07070f80e03400a30b02c1304c00550340d0000001f0b0b0f01b0b0b1b0f07070f0f0f0f0f1f1f0f1f1f0f0f0f80e03400a30701c00550340d000000070b073301b0b0b1b072323070707070707072f370707070780e03400701c0a300550340d01130709c0000001717231b170b170b371b230f37072307370f80e0380e03505405c02f130231300321555503503551511111414110014500c0c1c3c1c3c0c0c204c2c2c5c4c4c4c6c4cdc4c4c4c6c4c6c3c1c1c3c0e80c0013455010a3000001f17173b80e0380e030000003b1b170b170b3b1b3b0f1f071f073b0f00a00000555545000500000000000000001f17173b23171723231f1f2380e0380e03401313131313131313030300000c0e00c0c00004c04c0028c00400000000000001f17173b80e0380e03030303030b0303030f030303070303004c4c4c2c4c2c4ccc4c3c4c1c4c1c4c3c0c0ea80c0c0c0c0c0c0c0c4c0c0c4c4c0c0c0c0c00004c0000000c130115555555550354001028c00000a32020000000005c5e0380e0380c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0c005c003200c0c00c4c117540d903035035105c1709c2708a3a0a801105c5c5c5eaaa800000155555400005c00228c00000017002c00f001c0800001010005c2c2c5ea6aa95548c3c8c1c8c1c8c3e95545c0b0bc2f2208c4c08c4c11755552359551b4548c450b11111414001105c2c2c5eaaaaaa1b0f1b071b071b0fa08a1702c5b11c881b1301b1301742d51d991b1b51b5105c5c0b0b0b17a305c172200c0c0b05c6c0c0c001101c3c1c3c3c7c3c2c3c2c3c3c0a82ea5ba81ea0faa83e1faa83e0faaaaaaaa00000a301c0070000000cd1743d0743c3d43c7d65a59900002b0000000820028c00001c1c1c1eaaa0cc6c5c2c5c2ccc6e800280000000000000cd1741d07665bc8d5bc8d40000fc0020000c000000000 24 16777215 10 1023
def hc_66_5 : Nat → Nat := unpackHintV5 0xf29180eba1bcdf9b02d819e0d33938ccb1a2c3c23cbd31a4b34a7aaab2269c739096299289fb0c8600fe8039727822067171ac6b6184600ad65ac95052d1fe4b11f04800c442e1483ac20835c93e28bb44209a081b09640d935e0791800001e4 0x70f070f3b17173b0f07070f0000003b1b170b170b3b1b00070703b033b8ee3b0300005545550005000000000000000023171723070f070f403b17173b232323230f07070f131313130f0f00003c3c1c0f0f131313130004c0028c001c0010000000001328c0000070f070f0f0f0b0f0b0f0f00ec5c5cec3c1c1c3c3e0f030f83c0c4c4c4c2c4c2c4c3c3c1c1c1c1c3c3c3c3c3c3c3c3c4c3c3c4c4c3c3c3c3c4c0c4e1384c0c00001c00003c130001155555550f5554001028c000a301c0070001309c0000000001c3c1c3c3c3c2c3c2c3c3c017170f07070f0f83c0c3e0f0305c0f01c0f0f00f130045d0f41d0f0f50f55105c1700728c1c1c01c1c1c9c2701f007d101c1c1c1c5c5c5c5c1c1c1c1c00000155555400000728c0000000017002c00700302000001010001c1c1d07075550707555170b0b17070707072388c0c8e23031702c0701c1f1301f1301f07c45d55551b554547c44445050440044070707070707070707070700701c1c5c2c2c5c1c1c1c1c6e1b031b86c0c5c0b01c0706c4c06c4c07c1f05d0b41d0746c6d46d4cd33447c171702c5c0701c0f0f0170f01705c0044070707070703070707070303a08aaaaaaaaa1702c0701c1f1301f130881742d0741d2b2352b2359911f05c0b01c80f0f0a088004480e0707070b07070717aaa07a0707aa07070707a81e07a020ba8eaaaaaaa81e03aa81c5c0b28213007130070700701c881742da598d41d41c1d41d0766447c1702ca085c01c1c3c1c1c00728e2001101c1c1c1c1e07070707a030300300c0e0380e0380e80c0e80c0c5c0b01c0707c4c07c4c00c81742d0741d4723547235036447c1702c070700c070f0f0f0030300c00c800440707070b07070717070707070280c0e0ba8e07a0303a0303030381c0e0303a80c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c1c0c0c0c0c0c5c0b01c4c01c1c01c0700c803030031301742d075070750741d03640c0d40d8d447c1702c07070f0707001ca303200c0c03003031727000440741c1d541c1d41c1c1145c2c2c5c1c1c1c1cce3703338dc0c5c0b01c0707c4c07c4c07c1f15555555554511111414110011150707070b070707170707070707370707070707071b071b070707070707070707070707005c2c2c5c6e33033386c0c1e07030781c0c1c1c1c1c5c0b06c4c07c4c01c4c01c1c01c0707c1f15a342d50b50755555555451114141075070128d1001100e81c1e170b0b17aa232392cdea410ba8eaa07aa81304c1305d5541c1d44445170b0b174180c2ea3070380e03a070307032303230303034b034b03030303031304c0304c175070755511400d271550707070707070707070717230b0b0b0b17a30707070b0b070707070745170b0b171b23231b07070707232323231702c1b07c0701c1f07c1f07c4451444444400070707074b1b170b170b231b50451717070707072392c0d2e23031f05c0701c1f1301f1301f07c555541d41d5514444450504400514070707074f1b170b170b4f1b030304580e0340e0355a51f05c0701c1f1301f130032155555555545111071150504400440707070b0707073307070707020380e80c0e80c0e0380c0d1c0c0c0c2c0c0c0c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c1c0c0d51f05c07130070700701c03200c0c00c4c1555555555a365645111075070128d11414001101c1c1c1eaaa4ac6c5c2c5c2cac6e811695547c1701c072207c4c07c4c1555555555451111111414001101c1c1c2c1c1c1ccc1c1c1c1c0a82ea47aa81e07aa81ea81ea07aaaaaaaa547c1701c4c01c1c01c072130a0885555555565955a3144441d41c04a350504400440707070b07070707070707005c5c1e07030781c0c1c1c1c1c7c1701c4c01c1c01c0707c1f11741d41c1d41d075447c1705c07070f0707001ca32709c0044070f070f171717170f07070f0000005555550000000000000070f070f171717170f07070f00000055555500000001ca3000000005c00b003c00c0800430000404000f0f03030303030303070707030303030707030380e03a0a0320380c5c0b07c4c07c4c01c0700c81742d67235672350741d036447c1702c0782801c0700ca800440f5541d80e0317030b032f034b0303032303230303030703070301304c0304c1741d41d551128e241c3c1c1c2c1e8c1c1c1c1c1c1c1e0380e80c0e80c0e0380c0c5c0c0c0c2c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c0c0c0c1c0c0c0c1c0c0c01702c07070071300701c03200c0c00c4c05d0b41c1d41d41d0740d90303503511f05c0b01c1c01c5c01c0708a3a0a801101c2c1c0c1c1c0c0c0c0c0c0c2c2c0c0c0c0c0c0e0380e0380e8280c1702c0f01c2b1302b13003205d0b43d074ac8d4ac8d40d913b05c0b03c0703e0a0032a001101d50b560380c5c0c2c0c3c0c1c0cbc0d9c0c0c0c8c0c8c0c0c0c04c1300c1305d0f43d6550348d4bd1128e2541c1c2c2c1c2c1e8c1c1c1c2c2c2e0380e0380e80c0c0c0e0fa030303170303030b0303030f030303070303030f030f03030303030f0303030303005c0b03c0703c3c03c4c00c803030031301742d0f41d0f0f50f503640c0d40d44ec1702c0f01c0f0f00f170228e82a00440303555170b0b172307230f2307230f40e0355a580e031702c23130231302f0bc0321175546d55551444505044440044030303170b0b171b071b0f1b071b0f80c0e0303a032820380c5c0b06c4c06c4c16c4700c81742d1b1b51b551d03644171702c5ca017805c1700c80044 24 16777215 10 1023
def hc_66_6 : Nat → Nat := unpackHintV5 0xb54992b08930a46b089f494899617a94713c893ace8469347f29507a712e7291f86c49926a40825e3b0259a92455b0fe5420644e297e4ac0da46c8fe4169583c594438e8dc32f97c2dc14e27d97a1c2aec17313e11f15009f20005013c000140 0xb0b0000707000070b03cce3b03338ec0c5c2c2c5c3c1c1c3c0000000000ec8d4ec8d45d0b43d074ed3340000000000000000401c3c1c3c5c2c2c3cbc3d4c3c3c3c8c3c8c3c3c3c20380e0380c00005d1355400028c1c07000070b070f07070f0f07070f0f0f170b0b0b0b0f0f0f130f130f0f0f0f0f130f0f0f0f0f005c2c2c5c4e13031384c0c3c1c1c3c3e0f030f83c0c0a302c00b0000000005d0b44c4d44d43d0743c3d43d4ed33400000001309c00a301c007000000000c0c1c3c1c3c5c2c2c3c6c3c6c3c3c3c6c3cdc3c3c3c00c0c220380c000006d2f43d5f40028c1c0700ec6c5c2c5c2cec6c1c3c1c3c0c0c0020380e80020300c00000000015d174ec8d4ec8d43d0740d90000000000000000330b0b0f080e031b0b0b1b0f07070f0f0f0f0f2f370f23230f0f0f100000550340d00a30701c000070f070f0f330f0b0f0b0f0f020380e0380e80c0e80c0c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0c0c3c0c3c0c0c0c0c0c3c0c0c0c0c0c000000000028c80845d0f41d0f0f50f503640c0d40d400000a301c0070000000309c0000003c3c5c2c2c3c2aaa83c1c1c3c3c3c3c3c6c6c3c6d4c3c3c3e00000003d5f46d2f428c1c0700001c3c1c3eaa28ac6c5c2c5c2cac6c028280000000000000cd1743d07664ac8d4ac8d40000000000000000cc2c2c3c06c2c2c6c3c1c1c3c3c3c3c3c8c8c3cbd3c3c3c3ea84000003d559600a30701c000070f070f0f330f0b0f0b0f0f02a0baaa07a83eaa0faaa0f83eaaaaaaa800000000020800a33345d0f41d0f0f50f596966400000a301c0070827000000000000b0b5550707054070b43cce3703338dc0c5c2c2c5c3c1c1c3cdc4c0dc4c05c0b03c070dc331555555555451414111111001106c3cdc3c6c0ddc0c3c0d5c0e8e8e8c27541c2c1c3c1c1c3c3c1c1c3c3c3c5c2c2c2c2c3c3c3c6c3c6c3c3c3c3c3cdc3c3c3c3c3c0170b0b171b8cc0cce1b030f07070f0f83c0c3e0f031702c1b1302f1300f01c0f0f00f1300cc568d0b542d5555555514445050128d07041d4407c05105c8c6c2c2c5c5d145c8c2c2c2c3d53323239780e032f08c1304c50f43d5548d11417d27140e170b0b17aa5f3788c8ea83c1e440ba8eaaaa0f81304c131543d0f53b4444582c2e0f560380c4c131553b44170b0b174480c2ea380e030f03a5f030303032303230303030f03070303031304c0304c0f43d550348d4ed11400d27148c5c5ccd157e0b80e030f548e23aaa2f08c81303d0f55552344445231717974580c0c0c8e235f030b03a83d503032f08c0304c0f43d55548d1111405c2c2c5c4c4c4c4cbe0c4c8c8c4c4c4c1c3c1c3d020380e0380c28c2c0b04c13001543d0f40004c2700006c2c2c6d020380d7c0c2c0cbc0ddc0c0c0c8c0c8c0c0c0c3c0c1c0c00028e203d0f554000000c27006c2c2c6d020b97ea2388ea2fa3e0783ea80022028c3d0f5540000008c6c5c2c5c2c6c1c3c1c3d41505c5e23032380c3c1c1c3c170bc4c08c4c03c0701550f50f55551511141411110014500c0c1c3c1c3c5c2c2c3c6c3c6c3c3c3c6c3cdc3c3c3c00c0d660380c4c1303c131555551128c1c0747d3b1b170b170b3b1b070f070f030305480e03a55580d033b05c3b1303b1300f01c0321555555555451114141111001101c3c1c3c3ccc3c2c3c2c3c3c080e0380e03a0303a0303030303030b0303030f030303070303030f030f03030303030f030303030354ec1703c0703c3c03c4c00c8030300313055555555568d9591444128d07041d4451040d27007c05105c2c2c3c2aaa83c1c1c3c3c3c3c3c6c6c3c6d4c3c3c3e543c1304c1315555528c1c075406d2707d070f070faa9a2b1b170b170b2b1b45a0a5553305c0f01c882b1302b13055555555551444444450500044070f070f0f330f0b0f0b0f0f02a0baaa07a83eaa0faaa0f83eaaaaaaa953305c0f01c0f0f00f13084c2822155555555965568c51104a341c10754141101f01440f0f0f0f00720380c4c2c2c5c4c4c4c6c4dcc4c4c4c6c4c6c3c1c1c3c0e80c0007455010a3000000f0f170b0b0f080e0300013130f07070f0f0f0f0f1b1b0f1b530f0f0f03a0300555100a30701c000 24 16777215 10 1023
def hc_66_7 : Nat → Nat := unpackHintV5 0xd87196cfda26c3731abcc1acb0ab06aad176a9b048a8c03ca680909ed9ea9302f68d516c851a0e84004681d88a7bc98474a1ca68a3006181c85c61485462004e9174468a0241e9283b61a23292342bd9ae26a14e1cea6e13d2460df97600037e 0x2c2c1150b070b55070750b0b0b0b2b8ac0cae2b030f07070f0b02c2b1302b1300f01c2b0ac55555555551444505044440045445070b070b07070f0f072307a30b0b0b0b0b0b0b07070b0b0b0b07070b542c2c2c2c8c8c8c8c3c1c1c3c3c3c0c3c3c0c2c0b08c2303c0703c3c0f130ac2b11111114511000007070b0b07070b0f070b070b0b0b0f0b0b0b0b0b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0b542e0b030b82c0c2c2c2c2c3c1c1c3c3e0f030f83c0c2c4c02c2c02c0b03c0703c3c03c4c0ac2b10b55555555a341d507554510b50b0128d11414114ac0045407070741c1c1141c1d5542c2c2c2c1c1c1c1cae37032b8dc0c2c0b01c0707c4c07c4c07c1f15507555555551442c451141411400454001c1c1c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c2c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1d50b82c0c2e0b030b0b0b0b0781c0c1e0703070707070b1300b0b00b02c07130070700701c1f07c55555541d41d55a3551442d42c04a3505044450011500c0c1142c2c2c2cdc1cac3cdc1cac3d0380d56960380c2c0b0dc4c0dc4c0ac00c85555555555144450504444004540393c0d3c0c8da30270737074fa32f49c070b07030b0367030703a32f4bda3a327027450b0b0b0b2323232380e03a030388ea30380e03030303030b03a0303030ba03030f03030303542c0b08c230ac2f00c8030300c4c444444445140da300000b070b0b0b070b0f0b0b0b0ba0303a030380e0380e03030b0303030303030b030b03030303030b0303030b0303030f030303070303542c4c02c2c02c0b0ac00c8030300313042d55555555568d9591442d42c04a34445851040d270004540b0b0b0ba9aaa0452b0f2b072b072b0fa5550b02c2b0ac882b1302b130555565555551442c45111614466000454002c1c2c2c2c1c2c3c2c2c2c2eaa0b82eaa0baa0ba82ea07a83eaaaaaaa950b1300b0b00b02c2b0ac84c2822155555555965568c510b50b0128d114419811600115203130ec2c2dcdada38f82e80e8c4c2c2dee13a03130136b68e8c2c2c2c2c2c2c2c2dec7c7cdc0000002c2c001cc3c7c1c7c1dcc3cdc0dce738dc0c0001515554001400000000000000011002c2c2c2c7c8c7c8c2c2c2c2c8c8c8c8dac7c7cdc0b0b0b0b0b0002c2c04c3c4c4c4c3c4c0c4c4c4c0c00028c130001300040000000000000002c1c2c2c2c1c2c3c2c2c2c2c2e0b030b82c0c2c2c2c2c7c7cdc2c2c4c4c2c2c2c2c2c2c2c2c2c2c4c2c2c2c2c2c2c2c2c4c3c4c1c4c1c4c3c4c0c4e1384c0c0b04c000000004c00110b55555555554001028c0b00b0028c0000fc000000004002c1c2c2c2c1c2c3c2c2c2c2c2e0b030b82c0c2c2c2c2c2c4c02c2c02c0b0002d42c2d42d0b55440b0b170b0b002ca31705c1705c5c0041740707070780e03880c5c5c0c0c0c0c0c0c02800c0c0000000000001555555555400002c0000000000000707070780e0381ea3a030303170303030b0303a80c0c0c0000000001555555555400000b28c00000000000017007001c00300c08800300c0003000000040400070b070f85c0e030380c0e0705c5c0c0c0c0c0c0e80000c0c0000000000001555555555400000b28c000000000000070b070f85c0e0303a030381ea303170303030b0303a80c0c0c0000000001555555555400000b28c0000000000001700f001c00302000c030000c0000001010005c2c2c5c5c2c2c5ccccc00000155555400000b28c000000001700f001c00302000001010003c3d5550b070f5507075170b0b172388c0c8e23030f07070f1702c23130231300f01c2f0bc45d551b5541d5514445050444400440f0f0f070b0f070f0f07070f01c1c05c2c2c5c6e1b031b86c0c3c1c1c3c5c0b06c4c06c4c03c070cc3305d0b46c6d46d43d074cd3344171702c5c07070170700f01c1705c00440b0b03030b0b0f03a0a8070b070faaaaaaaa83cac4c0ac4c05c0b03c07220ac8d4ac8d45d0b43d076644dca0070701702c80722001100d5070f070f170b0b0f2f0f4f0f0f0f230f230f0f0f059aa1304c0f04c1765558ad2714128c1c0747d580e070b070fa83e07a0f170b0b0b0b0f0faaa0f0fa0faa020ba8eaaaaa83eaaa85c0b2821300f01c0f0f00f130881742da5943d0743c3d43d6644ec1702ca085c00728c1c1c01c1c1e201f005d1282c2c2c2c3e070b070f0303003030320380e80c0e80c0e0f0380c0c5c0b0ec4c0ec4c03c0700c81742d3b2353b2350f41d03644ec1702c030300c01c1c1c00c07070700c807c01744170b0b0f080e03950f07070f0f0f0f0f2f370f23230f0f0f03543c1304c1305d41d543d2340d0352f4a30701d441f41c2c1c3c3c5c2c2c2c2c3c3c0a030382ea383c0e0303a0303a0303a80c3c0c0c0c1c0c0c0c3c0c3c0c0c0c0c0c3c0c0c0c0c0c0c0c0c5c0b03c0703c3c03c4c00c803030031301742d0f41d0f0f50f503640c0d40d44ec1702c01ca30707007070703200c0c03003031727007c01744 24 16777215 10 1023
def hc_66_8 : Nat → Nat := unpackHintV5 0xde412cd92946d09a24cc211ec571acc05148b65a7eae0a149f83a29889be93594c89ba68816a147971fe69e3e45d43285ca0285c20205531bc4f597642e31e3cd18430a30c2b41582629461e39fc19d11a1591101031580a417c0660f8000198 0x70b070b80e0380e02c2c0c2c2c2e000c00000000005555555550002c03c00030009c000004070b070b80e0380e00c0c0c0c2c2c0c0e80000c0c000000000000155555555540000000000000000101c2c1c2e0b0380c0e80c0e07a8c0c2c0c0c0c2c0c0ea030303000000000055555555550002ca3000000800000c00000402c03c007000c03022000c030000c0000001010002c2c2c2c2c2c2c2c000001555554000b28c0000000000402c03c007000c080000040400a08a070b070b07070b0307070303aaaaaaaaa0b02c2b1302b1300f01c880b42d2b2352b2350f41d9918f02c817170a00f01c8a800440070b070f0b23230b0b0b0b0b0b0b2f4f0b0b0b0b0356a9644c0b04c1302d235543d960b42c4a34465001c1c2c2c1c1c2c3c1c2c1c2e0baaa0b82eaa0ba82ea03aaaaa0b80eaa0b81ea3aaa82c4c02c2c02c0b03c07282130880b50b0b50b42d0f41da5966440b0b170b0b002ca30f01ca085c22a00105d2b00c0c00c030307070707a07070781c1e0380e80c0e80c0e070380c0c2c0b07c4c07c4c01c0700c80b42d2b2352b2350741d036447c0b00c17170030300701c0320011000707070707070707070b070f07070707a0303a030380e0381ea3a0303030b0303030303030b030b03030303030b0303030b0303a80c0c0c2c4c02c2c02c0b01c0700c803030031300b3750b0b50b42d0741d03640c0d40cad447c0b0b170b0b002ca30701c032a00c0c030030317270004174ac07070707a08a0707030307030707aaaaa07a8eaaa82c0b01c0707c4c07c4c2202d0b41d074ac8d4ac8d66447c0b201c0705c5c2822a0011002cbd2c2c2c2c2c2c2c2c8c8c2c2c2c2c1c1c1c1c0d5aa951302c1304c0b48d55941d802d0b128d11940aa82e0baa82ea82ea0b070707070707070707070707a03aaaaaaaaaa07a8c2c4c02c2c02c0b2130a00701c880b50b0b50b42d96941d0766447c0b0b170b0b002ca385c2801c0722a00105d2b00c0c00c0303070b070b07070b81c1ea0380e80c0e80c0e0380c2c0b0ac4c0ac4c03c0700c80b42d2b2352b2350f41d03644dc0b00c17170030300f01c03200105d2b02c2c6c1c2c2c1c2c3c1c2c1e80c0e030380e0380e030b1302c2c1b06c0f01c03202cdd0b0b46d1b43d0740d913702c2c5c5c6c00c1728c3c0700ca8004174ac001c2c1c1c2c2c1c1c2c2c3c3c1c2c1c2e0ba0303a0303030382c0e0303a030381ea3030b0303030303030b030b03030303030b030303030b030b0303a80c0c0c2c4c02c2c02c0b03c0700c803030031300b3750b0b50b42d0f41d03640c0d40cdd44dc0b0b170b0b002ca30f01c032a00c0c030030317270004174ac001c1c2c2c1c1c2c3c1c2c1c2c2c2c3c7c2c2c2c2c2c2c2c2c2c2c3c3c2c2c2c2c2c2c2c2c00b82c0c2e0b030b0b0b0b0f07070f0f83c0c3e0f0302c13000000028c07001c000b50b0b50b42d0f41d0f0f50f1f52b4ad0002c02c00a3000000002b00000ac032b80f0275231306c07070701c1c0001c1c0002c2c2c2c1c1c1c1cae9b032b80c0007000000000b42d0741d2359b2354ad001300b00000fc0000003f000000fc00b2f4b0b0b0b0b0b0b0b23230b0b0b0b070707071080e0380e0300000b48d550b41d41cbd00b02c0a32309c000fc4007070707070b070b07070707070b070707070b0707070b070707070707070707070707002e0b030b82c0c2c2c2c2c1e07030781c0c1c1c1c1c000000070070028c002d42c2d42d0b41d41c1d41d0752b4004c02c02c00a301c27000000003f000000fc03030000b0b0b0b1f072b0f1f072b0f00e0300a080e0300000000000b42d37235372352b47d03640000000000000000dc002c1c2c2c2c1c2c3c2c2c2c2e80c0e80c0e0380e0380c0c2c0c0c0c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c2c0c0c0c3c0c0c0c1c0c0c002c1300000000028c8080b3750b0b50b42d2b47d03640c0d40cdd4000b00b0028c000200000309c00000dc0b0b0b0ba8aaa0002b0f1f071f072b0fa000000020000000b42d2b47d992b2352b235000000008000000000070b070f0b2f4f0b0b0b0b0b0b0b23230b0b0b0b0f07070faa1000000b48d552b65802c0b028c008400b070b0b0b070b0f0b0b0b0baa82e0baa82ea82ea0ba81ea0faaaaaaaa0000000000820028c2d42c2d42d0b4ad1f65a5990002c02c00a300000000800002b1041c3c1c3c2e0b88e23a8de37a80e82ea81ea3aa1304c81310b0b43d55923656b444454182e0ba8de37a88e230707070780eaaa81ea31304c13210b0b648d5507651f4444540070f070f0b0b0b0b1f0f1f0f0f0f1f0f1f0f0f0f080e0380e03000a30701c42c2d0f43d0f554ad00000040070b070b0707072f073707070723072307070707080e0380e03000701c0a342c2d0748d55074bd0113000709c000040070f070f82e0ba8be37a88e2381e0faa000880a342c2d2b648d55900000050450b0b0b0b2307370f3707230f0b0b0b0b238dc0cde230337370b02c231302f1300370550b50b55555454445050444400514 24 16777215 10 1023
def hc_66_9 : Nat → Nat := unpackHintV5 0xf25b4ae5733ae06942d4dae4cf296cc62242c04976b979b4b33192a5c35c9fb18491c37c85a30880a140743b1a6f094c63b2d65793084b231c48f08c3d9ad63cf8283a809e2f1ada27b9d823890c1cc1b218112c12d94e0ac20606691600019a 0x542c1c2c2c2c1c2c3c2c2c2c2c2e0b030b82c0c2c2c2c2dac7c7cdc2c2c4c4c002c2c2c2c2c2c02c2c2c2c2c2c2c2c2c2c4c4c3c4c1c4c1c4c3c4c0c4e1384c0c2c2c4c4c02c2c0b00b02c130bc4c4c1304c550b50b5568d547d55234005068d41411111114140014501c3c1c3c3dec3c2c3c2c3c3d53b3b3b3b0f07070f0f83c0c3e0f031313130b130b137b0f0f0707130707070f0f0f0f0f0f0f0f0f070070707070013031384e13031304c0f01c1c1c0f0f03c03c3c4c4c04c131555568d07541d5500141a34444505044505000440303070f070f030359130b0b1ba86c4cdc4c4c4c6c4c6c3c1c1c3c0e80c4c130bc4d55540468d11107cdc7cee0380e0380c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0d51313130b130b1333130f13071307130f0303a13a80c0c0c0c0c0c0c0c0e0aa001304c130bc4c4c03200c0c0300303131305555555a36564005068d111111414141400112a83c1c1c3e544c2c2c6c3c1c1c3ea80c0c0c6c4dcc4c4c4c6c4c6cbc4c4c131542da3546d0340468d406d3f11007cdc7ccea0baaa07a83eaaa951313130b130b1333130f13071307130fa030300aaa0aaaaa13031304c130bc4c4ca13130a208855548d551f5965568c00505444450504450500041080c2ea32b03a0f0307030303170b0b170f07070f03a0303030303272703272f03030304c000154009c000309c130047c5c5cacac5c5cac7c7cac9c6c5c2c5c2c9c6c9c3c7c1c7c1c9c3c9c0c9e2789c0c00004c0000005555550000000009c00001300000107c7c7c7c4c4c4c2c4c2c4c4c3c4c1c4c1c4c3c4c0c4e1384c0c4c1304c43131304c1315547d500141a3007c0130131300044001c1c1c1c1c1c1c1c1c1c1c1e0380e80c0e80c0e07a8e80c0c0c5c0c0c0c2c0c0c0c5c0c6c0c0c0c0c0c5c0c5c0c0c0c0ea0303031702c17130171300701c03200c0c00c4c05d0b45cad45c5d41d0740d903035032b511f00b28c2c2c02c2c2c1c0700c8030300317000440070f070f80e03170b0b1717231b171717171717172b1b9503544c1304c1310b551745d0f40d0352f4a30b02d2b49c505001c2c1c3c1c1c3c3c1c1c3c3e170380c0e80c0e80c0e80c0e07a8c0c5c0c6c0c0c0c2c0c2c0c0c0c5c0c6c0c0c0c0c0c5c0c5c0c0c0c0ea0303031702c17130171300f01c03200c0c00c4c05d0b45cad45c5d43d0740d903035035100b28c2c2c02c2c2c3c0700c803030031700044001c2c1c3c1c1c3c3c1c1c3c3c3c5c2c2c2c2c3c3c3c5c3c6c3c3c3c3c3c5c3c5c3c3c3c3c0170b0b171785c0c5e17030f07070f0f83c0c3e0f03000000028c07001c001742d172b5171750f41d0f0f50f1f52b4ad00028c0b002c0000000000000170b0b17172f1b17171717171717231b070707071080e0380e030000175541d41cbd00a30b02c00001c1c1c2c1c1c1c5c1c1c1c1c1c5c1c5c1c1c1c1c1c5c1c6c1c1c1c1c1c1c1c1c1c1c1c1c0170b0b171785c0c5e17030781c0c1e07030707070700000001c01c00a3001742d173f517175075070750741d4ad001300a302c00b00709c000000000000001c3c1c3e0380c5c2c2c5c5c8c6c5c5c5c5c5c5c5cbc6c3c1c1c3c400001540d034028c2c0b0bc270000170b0b171707170f1707170f80e03a0303a030380e0303170303030b03030317031b030303030317031703030303030f03030307030300000000000a320205d0b45ccd45c5d4ad1f40d90303503500028c0b002c000000000000001c2c1c3c1c1c3c3c1c1c3c3c3c5c2c2c2c2c3c3c3c5c3c6c3c3c3c3c3c5c3c5c3c3c3c3d5170b0b171785c0c5e17030f07070f0f83c0c3e0f031702c17130171300f01c0f0f00f1302b0ac555555568d07541d5514128d0b042d445050440044001c1c1c2c1c1c1c5c1c1c1c1c1c5c1c5c1c1c1c1c1c5c1c6c1c1c1c1c1c1c1c1c1c1c1c1d5170b0b171785c0c5e17030781c0c1e0703070707071702c171301713007130070700701c1f07c55555541d41d55a35514128d0b042d41d270510444400440717071b1b03170367030703a32f68e8c9c005c2c2c5c5c1c5c3c5c1c5c3e0380e80c0e80c0e0380c0c5c0c0c0c2c0c0c0c5c0c6c0c0c0c0c0c5c0c5c0c0c0c0c0c3c0c0c0c1c0c0d51702c17130171302b003200c0c00c4c1555555555a36564504a342c10b51111414001106c5c5c6e8e8c6c2c6c0c5c0c4c5c4c6e0303130304d2fa3a3005c2c2c5c5c1c5c3c5c1c5c3c5c2c2c5c5e17031785c0ccc7c7c4c4c2c2c2c2c4c5c4c4c4c4c4c5c4c5c4c4c4c4c4c5c4c6c4c3c4c1c4c1c4c3c4c0c4e1384c0c000000004c00115555555554001028c0a302c00b00000000000000170b0b171707170f1707170f170b0b171785c0c5e170333331702c171301713000cc1742d1751717554cd100b28c2c2c02c2c2c5c1705c17001101c2c1c2ea82c2e80c0c002a8a8028000000000015555555554000000000002000001c2c1c2e0ba82ea03aaa0b81ea3aaa800000000015555555554000b28c00000000020000100b00f001c08800800200c08800000404000707070780e03880c2c2c0c2c2c2c200c00000000005555555550002c00070030009c0001000707070780e0381c80c0c0c0c0c0c2c2c0c0c02800c0c0000000000001555555555400000000000000001c1c1c1e0380e07a8e80c0c0c2c0c0c0c2c0c0ea030303000000000055555555550002ca3000000800000c00000402c01c007000c0800300c0003000000040400a0b0baa070707070303000aaa000a881c0000000001555555555400000000000200002a0ba82c1c1c1c1e80eaaaaa81ea3000000000055555555550002ca3000000000080000402c2000880007001c08080000040400 24 16777215 10 1023
def hc_66_10 : Nat → Nat := unpackHintV5 0x8b50dc44605221742f1027a4a7dc8dd3dca469dc8474dee3d86afd1d33009f97877e4b551ba55c938277ed992dd3888d326e4275091f14898e6b47c64cba42fa4b0162a6a09d05144a590a2184ea0ed87a864549c23bb9c0e18f104e28a80d267c0001a4 0x70f070faa0ba80eaa8ee07a8eaaa1304c0f01ca084c22155555555541a3504cd50b543d50756655655595951340444450504400445050070f070f80e0380e48cbc8cbe540d51304c0f01c03200c04c1542d43d5503554bd44d4444444400514070f070f80e0380e4bc6cbc2cbc2cbc6e95540c0d5544c1303c0700c80303013130555555505415444444450500044070f070f8dc0e0303a030381ea303370303030b0303a80c0c0c4c1303c0700c8030300313055555555540d5068d4133542d50f541d50356540d035540d5544d0111111141400111414151b0b0b1b1b071b0f1b071b0f1b0b0b1b1b86c0c6e1b03331f1f33131302c4c13130131301304c1304c5555450555514445050444400441f1f1f1f1304c1304c1304c555555068d41542d50f541d50356544d01111110011141401c2c1c2c2c2c2c2c3c1c1c3c2c0b03c0704c1302c2c1c1c2c1c2c2c3c3c1c1c1c1c3c3cdc0cee3b8dc0c142d00b42d0f41d374dd10b0142c50b02c0f01c1705c00171701717044070b07a307070b0b0707070b0f0b0b0b0b0b0f07070f0b82c0c2e0b030b0b0b0b0b0b0b0b0b0b130f0f070707070f0f0b0b0b0b0b0b130b0b13130b0b0b0b13031384e13030b02c0f01c1c1c0b0b02c02c2c4c4c04c13150b42d0f41d0b0b50b235374dd00141a30b02c0f01c0b0b00b1701705c13170131300044070b070f1b0b0b1b0f07070f1302c0f01c1304c13070b0b0b0b07070f0b070707070b0b3b03338ce3b03050f406d0b43d074ed33443c050f145c0b03c070ec33000ec9c0ec9c1101c2c1c3c1d0b1b0b41c3c6c2c2c6c3c1c1c3c8c8c8c8c4c4c2c4c2c4c6c4c6c3c3c1c1c3c3c3c3c03c3c3c04c4e1384c4c0b03c07070704c4c03c1f28c4c13151702c0f01c2308c2f0bc132b04c4c0007070b0b070b07a30707070b0b0b1b0b0b1b0f07070f0f83c0c3e0f0313130b0b130b0b0b131b131b0f0f070707070f0f0f0f0f0f0f0f130f0f13130f0f0f0f13031384e13031302c0f01c1c1c0f0f03c03c3c4c4c04c13151b42d0f41d0f0f43d43c3c8d4ed334005068c5c0b03c0703c3c03cfc0ec3304cac04c4c001106c2c2c6eaaaa371302c1304c8813030b0b0b0b0303370f1f071f07370faaaa05901b42d3747d991805851702c3b07c880037270372704480e1b0b0b1ba83e07a82ea3aaaaaa13130b0b0b0b131baaa13a1313aa130f13071307130faaaa1302ca084c04c43131322151b42da588d4ed1f664005068c5c0b2823f03b07c88132b01313000440b0b0b0b82ea3a030380e03a80c3c0c0c0c1c0c0c0c0c0c2c2c2c2c2c2c2c2c4c3c4c1c4c1c4c3c0c0ea80c0c0c0c0c0c0c0c4ccc0c0c4c4c0c0c0c0c2c0b04c3b131300c80303003130542d0b4ed1f40d9030350323500141a30b02c1705c03200c0c00c5c04c5c04c4c001102c2c2c2eaaa82c0b04c4313132202c2c0c0c2c0c2c2cec3c7c1c7c1cec3eaaa816402d0b4ed1f66458416142c0b05c17220005c5c05c5c11280e07aa83c2c2c2c2eaaa82ea3aaa1313aaaaa130b0b0b0b0b0b0b0b130f13071307130faaaa84c2802c0b04c431313221588d6942d0b4ed1f664005068e170a00b02c1705c88131701313000441b0b0b1b80e038ec0e03031302c130ec4c4c03204e0b0b0b0ba3b0f1f071f073b0f0303aa03030503406d0b4ed1f40d91030140c51702c3b07c032000ec9c0ec9c1106c2c2c6e0380e0380e42c6c8c7c7c8c0d80c4c4c2c2c4c6c4c4c1c4c1c4c0c0e80c0c0c0c00c0c0c04c0b04c2f131300c8131300308ca3545c0b0bc1f00c82308c1304c001b0b0b1b80e0380e0380b1b271f1f3b0320313130b0b0b0b131b130f13071307130f0303aa0303131313271313133f1302c130ec4c4c03204c13151b42d3b47d0364fd274005068c6c2c2c6e80c0e0ba8e3b0380c0ea030f03030307030303030313130b0b0b0b131b130f13071307130f0303aa03030303030303031303031313030303031302c130ec4c4c03200c0c030030313130546d0b4ed1f40d9030340d40c0c8d4005068c5c0b0ec1f00c8030300c00c0cfc04c04c4c0011283c3c1c0c1c0eaa84c2c2c6c4c4c4c6c4dcc4c4c4c6c4c6c3c1c1c3ea84c1301c1d46d2340468c6c270ac1301c3c1c3eaaa84c1303c07220cc6cec2cec2ccc6c3c0c1c1c1c1c0c0eaaa81640cd6b43d07664601614cc03c0722000ec9c0ec9c1101c3c1c3ea82ea03aaa3b81ea3aaa84c4c4c2c4c2c4ccc3c3c1c1c1c1c3c3eaa84e84c4eaaaaaa84c0c4c1303c070707288284c4c2215335ad0f41da588d664005068ccc03c072823f088132b013130004403a07030b80e84c2c2c6e84cdea83c1c1c3c0c0c0c0c1c1c0c0d40c0c0468cac1300c0c3c3c1e0780c0e0380c4c4c4c2c2c4c2c6c4c4c4c6c4cdc4c4c4c6c4c6c3c1c1c3c0e80c4c4c4c1301c1d46cdc6d2340468c6cdc6c270ac1301c3c1c3e0380e0380c4c1303c0700c83b1b370b370b3b1b0f81c1c1c1e80c0ea80c0c140d0374dd0f41d036440c0503143703c0700c8003b2703b27044070f070f80e0380e03232323239070f0360313130b130b130f0f07070f0f030384e030303030303003030301304c0f01c1c1c03204c4c00c1f28d52f0bc0f01c03208c2304cac13130001c3c1c3e0380c0e80c0e07a8c0c0c0c0c2c0c0ea0303031313130b130b13330f0f070707070f0f0303a13a80c0c0c0c0c0c0c0c0c0c4c0c0c4c4c0c0c0c0c4c1303c07070700c8030300c00c0c4c4c15374dd0f41d03640c0d035030323500141a30dc0f01c03200c0c00cfc04cac04c4c001102c3c2c3c1c1c3c2c2c2c2c3c0702c2c0b1304c1303c1c1c1c1c3c2c2c6c6c6c6c6c42c0f41d0b0b42c8d334cd10b042d0f01c0b02c1705c001705c441b0b0b1b1b1b0b0b1b331f1f33131302c4c1304c1304c1313131b0f1b071b071b0f1b031b86e1b030513406c6d0b5ed1f4cd33444c051b145c0b01f0cc330006c6c06c9c11151b0b0b1b1b07230f1f071b0f1b0b0b1b1b88c0c8e1b03331f1f3713130b0b130b0b0b131b131b13131313130b00b0b0b0b00130f13071307130f13031384e13031302c131308c04c4c4c4c04c2f131304c1315568d0b542d555500141a344505044445050004100b0b0b0b0b0f0b0b0b0b331f1f330b1302c2c1304c1304c0b0b1b1b1b1b1b1b1b1b1b1442d551f5548d0500555a34444440044514 25 33554431 10 1023
def hc_66_11 : Nat → Nat := unpackHintV5 0xd831a8cdd298c6a9cabd325eb72184ae6a2ea899749faa3c96d23691615c8b917485c1747bea767551a66e49c269e11a6389965a125e5479664e2196447a6a3f39503839c02f62362a21502311c41e014418217812517408fa560550ea000154 0xb0b5550707555070741e07a0303a03030380e0380e031f131f07c4c7c0b0b0b0b0707070703a0355555555555555454555555555507070b07070707070707070b07a381e80c0e80c0c0c0e0380e0380c1c4c1c07070702c2c2c2c1c1c1c1c0e80d55555555559a35541d5541d075542d542d0b541d0f541d07540d4544d1554545555555555545407070b0b070b07a341c1d5542c2d5560380e0380e80c0e80c0c6c2c2c6c3c1c1c3cec4c7c3b131f00e80d55555555559a3555555551515555541c1c2c2c1c2c1e8c1c1c1c2c2c2e0380e0380e80c0e80c0c6c2c2c6c3c1c1c3c3c3c3c0f130f00e80d55555555559a35546d50b543d507543d0f5543d5540d4544d1555555454555555545405541b0b0b1b1f073b0f1f073b0f80e03a0303a030380e0340b0b0b1402c2c04c1300c855555555551444505044440044006c2c2c6c4c1c4c3c4c1c4c3e0380e80c0e80c0e0380c0b28c2c2c02c2c2c4c1300c85555555555668c511b542d51344d55135550f541d5034151305511414111100111414015147c1cdc3c7c1cdc3c2c2c2c2e80c0e80c0e0380e0380c4c4c1402c41304c03215555555554514141111110011000b070b0b0b070b0f0b0b0b0ba0303a030380e0380e030b0b130b0b002ca31304c032155555555559a31442d5542d0b5542d50b543d507540d04544d130554141111110011141401c3c1c3c3c7c3c2c3c2c3c3c080e0380e03a0303a03031304c01ca307070070707032155555555559a31456d50b543d507543d0f5543d1f5540d0544c154444505044004450504b234b23070707071580e0388ea303a030380e031304c0f101c40321475552d55075034544c4444444400443b1b3b0b3b0b3b1b07070707054580e03a0303a030380e031304c0f0f05007100c85555555555144450504444004457275727070707070580e0380e0380e031304c0f101c40321555555559a31451d50b549d553541d507540d0544c150707070b0707073307070707020380e07a0303a0303030380e031304c07070f0707001ca3032155075555555559a315451d50b541d5541d075541d507540d04544d1305511074144511104111141401c1c6c1c1c1c1c1c1c1d071b07a381c0c0e0303030380e0380e03070707071b1b1b1b0707070703a0355555555555555555555555546c6c2c2c6c6c1c6c3c6c1c6c3e030380c0e80c0e80c0e0380c6c2c2c6c6c4c6c1b131b16d0d1d0c0e80d5555555555555555151555555560380e0380d0d0d0d0c0e80d5555559a355550b543d507540d4544d15555555555554540741c2d541c1d43c3d5542c2c2c2c3c1c1c3cbe2f032f8bc0c2c0b03c0702c2c04c4c04c1315555415154551111141411001101c2c1e8c1c1c2c2c1c1c1c2c3c2c2c2c2c2c3c1c1c3c2e0b030b82c0c2c0b03c0702c2c02c4c04c13155555555541a35042d50b543d507542d0b5542d5540d5951340444450504400445050070b0741d50b546c2c2c6c3c1c1c3cbc8c8cbc4c0b03c0703c04c04c1311b5543d552f556513511111110014501c2c1d07075550b0b5551b0b0b1b0f07070f2f8bc0cbe2f031302c0f01c0f0f0131301304c55555054551544444505044004407070b0b070b07a30707070b0b0b1b0b0b1b0f07070f0f83c0c3e0f031302c0f01c0f0f00f1301304c555555543d555068d411b542d50f541d50f43d550f5550356544d011111414110011141400c0d5546c2c2c6c7c1cbc3c7c1cbc3da95696a84c0b2804c4c04c13221554151555451114141111001120386c2c2c6ea0f81ea0ba8eaaaaa8dc4c0b2821301304c885555555555068d411b542d5995595543d5075656544d011141411110011141402c2c2c2e0ba8e80c0e0380ea030f0303030703030303030b02c1304c03200c0c00c4c155555555541a35042d50b543d507540d5950340d55034cd55134044444450500044505003035551f072f0f1f072f0f0b0b0b0ba555a6aa13130a00b02c1304c8854505555551450504444440044a0381eaa0f0b0b0b0baaaa0ba8eaa84c4c28802c0b04c1322155555555541a350655599550b542d50f541d5959513405050444444004450501b0b0b1b80e60380e548c7c7cbc0d51302c1304c03200c04c11b555507503554bd44d4444444400441b0b0b1b80e60380e9554bc3c7c1c7c1cbc3c0c0d5544c0b04c1300c803030131305555555054154444444505000441b0b0b1b80e60380e149c7c7cec0c51302c1304c03204c131555555541a35046d50b543d507540d5953f549d513401b0b0b1ba030382ea38ec0e0303a80c3c0c0c0c1c0c0c0c0c0c4c0b04c1300c8030300313055555555540d5068d411b542d50f541d50356540d035540d5544d0111111144103400111414283c3c1c0c1c0eaa84c1315468d06d0b46d1b546d2f543d076644d04444070f070f2f1b2f0b2f0b2f1b0303555aa6a55a51304c0f01ca01313088555550545515444445050440044 24 16777215 10 1023
def hc_66_12 : Nat → Nat := unpackHintV5 0xe66a30e1713ed9a9f2d1720ecc6942c75944be6a3cb89176b47108acf9dea27aa09aa9f48fdab48b592083d9e07d09b4737a6469ca6c62b9c45ca186524a964c118e42b2583de13434ba4a2b126a24f18820a1141a19a210527209c9a2000272 0x1c1c2c1c1c1c1c1c1c1c1c2c1e8eaaaa0780eaaa81c4c1c07070702c2c2c2c1c1c1c1ea9555555559a3555541d5541d075542d50b541d507565151345551515555555555515015147c1cdc3c7c1cdc3c2c2c2c2eaaaaaaa84c4c1402c41304c8855555555551450504444440044002c1c2c2c2c1c2c3c2c2c2c2eaaaaaaa82c2c4c2c2c00b28c4c13221555555559a3551442d5542d0b5542d50b543d50756415130554141111110011141401c3c1c3c3c7c3c2c3c2c3c3c0aaaaaaaa1304c01ca3070700707078855555555668d54515b542d50f43d50741d50f43d550f47d5590544c15444450504400445050331b4b0b4b0b331b070707070545aaaaaaaa1304c0f0f050071221555555559545111414111100110ac9cac9c1c1c1c1c16aaaaa84c1303c40712215555559a3551451d50b549d52b541d50756415130541c1c1c2c1c1c1ccc1c1c1c1c0aaaaaa81e03aa1304c07070f0707001ca38855555555668d5455147542d5075550741d550743d50741d5904544d13055110741445111041111414151b0b0b1b1b071b0f1b071b0faaaaaaaaa1b0b0b1b1b131b06c4c6c5b434743aa55555555555555555454555555553333aaaa3343334343aa5555668d5555542d50f541d594544d1555555555555454070b81c2c2eaaaa81c1eaaaa83c3e96682c2c2c2c3c1c1c3ea8ac4c7c2b131f02d0b43d076640c0d42c0d47d3742d0b43d076645c5d05c5d05d175541c2c1e8c1c1c2c2c1c1c1c2c3c2ea0ba82ea07a83eaa0baaa0b82eaaaaaaa950b0b0b0b0f07070f0b0b0b02c4c2c84e2a2a82d0b43d0742c2d42c8d680e959a31f4dd0b42d0f41d0b0b40b17485d292645d175541c1c1e070baaaaa0b0baaa0707aaa56681c0c2c2c2c2c1c1c1c1ea87c4c7c1f131f02d0b41d0765940c0d41c0d47d1f42d0b41d076645c5d05c5d05d175541c1c2c1c1c1c1c1c1c1c1c2c1e8eaa0781eaa07aa0ba82ea07a81eaaaa0780eaaa9507130701c1c1c0b0b0b0b0707070784e2a2a81c8d41c1d42d0b41d07680e959a31f47d07174070740b42d0741d85d292645d175546c2c2c6eaaaa689c9c9c9e686c2c2c6cacfcfcaea89c9c9c9c6d0b4ad476649d274fd3f46c2c2c6eaaaaaa1b0f1b071b071b0fa59a1b0b0b1b5b434743aa1b131b06c4c6c1b1b42d51d99030351b0354351742d51d991b1b46c06c6c9d10d5542c2c2c2eaaaa8228dc3c7c1c7c1cdc3e96682c2c80b1304c8813130a00b42d2f47d99030350b03511302c0b05c172205c5c05c5c0011000b070b0b0b070b0f0b0b0b0baa82e0baa82ea82ea0ba81ea0faaaaaaaa542c2c4c2c2c00b28c4c132130a0880b2350b0b50b42d2f47da03a5668c44c0b1700b0b00b02c1705c85c2822001101c3c1c3c3c7c3c2c3c2c3c3c0a82ea5ba81ea0faa83e1faa83e0faaaaaaaa544c1300728c1c1c01c1c1e130a0882f4bd0f41d0f0f50f1f5a03a5668c44c2b0ac0f01c0f0f00f1f08ac2822001101c1c1c1eaaa8cc6cdc2cdc2ccc6e822a96684c1301c8880f0f0a02f4bd0741da599a3030350703507d13130ac2b01c07220ac9c0ac9c00110ac9cac9c1c1c1c1c01c1ea0ba91ea2ba89ea07a81eaaaaa951304c0f04c0722130a0882f4bd274ad0741da03a5668c44c0707070b070707330707070702a0ba91eaa0781eaa07aa07a81eaaaaaaa951304c07070f0707001ca384c28220bd2f41c8d41c1d41d07680e959a307d13130ac2b01c1cac01c1c0710701c8fc282201f0131102c2c2c2eaa6a82c2c6c6c6c6c6e542c2c2c2cbcbcbcbea86c6c6c6d0b568da35a3568da355a368d68da35555555546d5555542c1c2c2c2c1c2c3c2c2c2c2eaa0380eaa0b80ea0b82ea0baa07a83eaaaa0b80eaaa950b130b02c2c2c0b0b0b0b2f2f2f2f84e2a2a90b50b5568d548d659555548d5454555554545555551b0b0b0f5aaaa0f07070f0f0f0f0f1b1b0f1b4b030303950f04c1304c55a30741d5544501b4ac070f070f0f330f0b0f0b0f0f56a0baaa0781ea0f83eaa0780eaa0380eaaaaa0f80eaa952f1f2f1f0f07070f0f0f0f03c4c3c84e2a2a9555a341d5075965568d555555515151515555541c1c1c2c1c1c1ccc1c1c1c1d5a82ea47aa80e03aa81e03a81e07a81e0faaaaaa81e03aa547c7c7c7c1c4c1c07070701c1c1c1e138a8aa55235075075568d965568d547d55545455545455555553317172b271b170b170b271b270f27072707270faaaa50543305c2b0fc27130271308855555054551449c45119458004543333a82eaa81ea0faaaa54cd0ccd0d0e138a8aa3355a03a5668d0d4cd564a499435550f0f55541c2c1c1c1d541c1d60380e80c0e80c0e0380c6c2c2c6c7c4c7c1f131f01c1c1c1c0e80d555555555555555151555555541c3c1c1c2c1e8c1c1c1c1c1c1c1e0380e80c0e80c0e0380c6c2c2c6c1c1c1c07130701c1c1c1c0e80d55555555559a35546d1b542d0b541d075541d5541d507540d4544d15555454555555555454070741c1c2d541c1d43c3d5560380e0380e80c0e80c0c2c2c2c2c3c1c1c3cdc4c7c37131f00e80d555555555555555551515555541c2c1e8c1c1c2c2c1c1c1c2c3c2e0380e0380e80c0e80c0c2c2c2c2c3c1c1c3c2c2c2c0b130b00e80d55555555559a35542d50b543d0f541d07542d0b5542d5540d4544d15555554545555555454 24 16777215 10 1023
def hc_66_13 : Nat → Nat := unpackHintV5 0x91d1c646a890218673902f2507a0ddb3ac2911caf2c8d6c3ae67410831ae7c982e2a4b45b465648f927d6d392406ac89ea0640c90b1ed8630e5545c64c37a2c0597146a6608a264c40213c19b99609b2ca841231c1999be09bcc403885580b643800016c 0x70f07070b07a30707070707070780e03a0303a030380e03031b0303030b03030307030703030303030703030303030307030303070303546c2c2c6c1c1c1c07130701c1c1c1c0e80c0c0c0c03130306d0b41c1d41c8d41d0759a3a5a87d1f45d0b41c1d01d01d0740d9030340341f47d550703070b03030303070703030f0f03030303030380e0380e03a5a0342c2c2c2c3c1c1c3cdc4c7c37131f00e80c2d0b43d0742e5a503647d3742d0b43d0745c5d05c5d00d91745d55070b07a307070b0b0707070b0f0b80e0380e03a0303a0303030b0303030b0303030f030303070303030b030b03030303030b0303030303542c2c2c2c3c1c1c3c2c2c2c0b130b00e80c0c0c0c03130302d0b43d0742c2d42c8d59a3a5a87d3742d0b43d0742c2d02c5d00d903034031741745d550b0b03030303030307070303030303030707030781e80da560380e0380c7c4c7c1f131f02c2c2c2c1c1c1c1c0e80e941e50b42d0741d035947d1f45c5d05c5d02d0b41d0740d91745d5507070b07070707070707070b07a381e80c0e80c0c0c0e0380e0380c0c1c0c0c0c0c0c0c1c0c1c0c0c0c0c0c2c0c0c0c2c0c0c0c1c0c0c0c1c0c0d507130701c1c1c0b0b0b0b0707070703a0303030300c4c0c07235070750b42d0741d668e96a1f47d07174070740b42d0741d03640c0d00c5d05d175541c2c1c0c1c1c0c0c0c0c0c0c2c2c0c0c0c0c0c0e0380e0380e9680d1b0b0b1b0f07070f3b131f0ec4c7c03a031b42d0f41d0f96940da91f4ed1742d0f41d2b2742b27403647d2b5541c10b060380c5c0c2c0c3c0c1c0c9c0d3c0c0c0c9c0c9c0c0c0d44c1300c1315568e645d0f43d6500349c49d41c1c2c2c1c2c1e8c1c1c1c2c2c2e0380e0380e80c0c0c0e0fa0303031b0303030b0303030f030303070303030f030f03030303030f0303030303546c2c2c6c3c1c1c3c3c3c3c0f130f00e80c0c0c0c03130306d0b43d0743c3d43c8d59a3a5a87d3b45d0b43d0743c3d03d00d903034032b41f4ad550303031b0b0b1b1b071b0f1b071b0f80c0e0303a036960380c6c2c2c6c6c4c6c1b131b16d0d1d0c0e80c6c6d0b6946e551d03650d45d0b46c6d06c9d14740d9435550303003030307c1cec3c7c1cec3c6c2c2c6e9680d80e0380e03030300b0b00302c1304c03204e5a51b42d2f47d036444c3b2703b2701702c3b07c03200110001c3c1c3e0380c5c0c2c0c9c0d3c0c0c0c9c0c9c0c0c0c3c0c1c0d400015568e645c1309c2000309c01006c2c2c6c4c1c4c3c4c1c4c3e0380e80c0e80c0e0380c0c6c0c0c0c2c0c0c0c4c0c4c0c0c0c0c0c4c0c0c0c0c0c0c3c0c0c0c1c0c0d502ca30b0b00b0b0b1304c03200c0c00c4c06d0b44c4d44c8d4bd1f59a3a5a844c1702c131301303b07c03200c0c00cfc001100c0c00c03030b0b0b0b1f07370f1f07370f80e03a036960380c2c0304c4c00c0c04c1300c80b42da50b94bd1f40d911302c0b05c5c05c5c05c1700c80044002c1c2c2c2c1c2c3c2c2c2c2e80c0e80c0e0380e0380c0c2c0c0c0c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c2c0c0c0c3c0c0c0c1c0c0d50b0b130b0b002ca31304c03200c0c00c4c02c8d42c2d42d0b4bd1f59a3a5a844c0b1700b0b00b02c1705c03200c0c00c5c001101c3c1c3c3c7c3c2c3c2c3c3c080e0380e03a0303a0303035b0303030b0303030f030303070303030f030f03030303030f031f03030303544c1300728c1c1c01c1c1c0c803030031302f4bd0f41d0f0f50f1f5668e96a1130ac2b03c0703c3c03c7c00c803030032b00044070707073b1b3b0b3b0b3b1b030300300c0e0380e0380e80da51304c0700c0f0f0030300320bd2f41d076941e5035941f44c4c6719c0701c3b2703b270032001108c8c8c8c1c1c1c1c41c1e0380e80c0e23a8c0e0380c0d1c0c0c0c0e80c0c0c1e80c0c0c0c0c1c0d51304c0f04c0700c03200c0c03130bc2f08c2301c0700c80300c001b0b0b1b0080e0347030b0327032703030327034f0303030703070350000555a3992709c0701c0700c80300c00309c0004457275727070707070070780e0380e0380e0303470303030b030303270303035303030307030303070303544c1303c1301c0300c803030031302f4bd274bd0741d668e96a11301c1c1c2c1c1c1ccc1c1c1c1c080e03a0303a030380e0303470303030b03030307030303030303070307030303030307030303070303544c1301c1c3c1c1c00728c0c803030031302f4bd0707235070741d41d0759a3a5a81f44c4c007070070701c41c0700c803030033f007c04c44546c2c2c6c6c1c8c3c8c1c6c3e0380e80c0c0c0e23a030380e03031b031b0303030b030b0303aa03030303030ba03030303030f030303070303546c2c2c6c6c4c8c23131b0bcbcbcbc0e80c0c0c0c03130315a342d50b5555a365655555515155555151555542c2c6c2c2c2c2c6c6c6c6d030380c0d660380c2c2c2c2c6c6c6c6cbcbcbcbc0e80d0b5a355a368d5568da3555555555555555550b070b0b0b070b0f0b0b0b0b82e80c0e80c0c0c0e0380e0380c0c2e80c0c0c0ea80c0c0c0c0c2c0c0c0c0c2c0c2c0c0c0c3c0c0c0c1c0c0d50b130b02c2c2c0b0b0b0b2f2f2f2f03a0303030300c4c0c42d42d55a355568d9595554545555555454555550303070f070f1b0b0b0f1b0f1b0f0f0f1b0f37a940c0d660380c4c1303c13155568c1d0747d4444070f070f0f330f0b0f0b0f0f560380e0380e80c0c0c0e0fa0303030303030b0303030f030f0303030703070303aa030303030307a0303030354bc7cbc7c3c1c1c3c3c3c3c0f130f00e80c0c0c0c0313031555a341d50755a365651f555555545455545455550707070b0707073307070707560380e07a0303a0303030380e0303470303030b03030307a03030303aa030303030307030f0303030703070303547c7c7c7c1c4c1c07070701c1c1c1c0e80c0c0c0c031303155075075568d5a36565555551515555515155543c1c2c1e8c1c1c1c1e0380c5c2c2c5c1c1c1c1c9cbc1c9c9c1c1c1c1c1c1c1d041c1304c13155110b500749c0740d0351f517172b80e0380e03271b170b170b271b270f27072707270f50453f05c2b0fc03209c4c09c4c1555555514051149c49c45031140d042711520380e0380c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0d54343434303a0303030300c4c0c55668e96a4355503640c0d00d10d5541d070b55070750f0f555aaaaaaaa0b0b0b0b0f07070f2b131f0ac4c7caa55555555555555555454555555070b07a307070b0b0707070b0f0baaaaaaaa0b0b0b0b0f07070f0b0b0b02c4c2caa55555555668d55550b542d50f541d50b42d550b55594544d155555545455555554540b0b5550707555070741eaaa81e03aaaa1f131f07c4c7c0b0b0b0b07070707aa555555555555554545555555555 25 33554431 10 1023
def hc_66_14 : Nat → Nat := unpackHintV5 0xcef9d0c711fac15170b971f8af8a7aaa195ca1da109a59e093b1aa89b28082c9ba79326673417c6c59ba6292725c698a53923651987e4d990048b13a4331603c29c23431fe2f11482839b622f1521ea1141759d213b8e80e914a059240000164 0x9c6c5c2c5c2c9c6c1c1c1c1d4150ac5c5c9e27032789c0c1c1c1c1c7c1707c4c07c4c01c0707c1f1554151555451271141d45071149c07c051501c1c1c2c1c1c1c1c1c1c1d50781c0c1e0703070707071f1f1f1f07130701c1c1c070707071f1f1f1f507070f0707541da351f47d5074070740741d51f47d550303555070b070fa0f0faa60ba95696aa0f1b0b0b1b2b131f0ac4c7c0f07070faa5555555555555554545555555580e070b070fa83e07a82ea3aaaaaa0f1b0b0b1ba884e03c1c1c3ea9555555550768d55551b46d50b42d5995595543d6565450d513515555454555555555454070b070b82ea3a030380e03a80c3c0c0c0c1c0c0c0c0c0c2c2c2c2c3c1c1c3c0e80c0c0c0c031303155550768d555555550b542d50f50340d59950340d55034cd55143544d4555555555151555551500c0d556aa83c3c1c2c1c2e95569aa8ac4c7c2b131f02c2c2c2c3c1c1c3ea95555555555555151555555555680e81c1eaa83c3c1c2c1c2eaaa82ea3aa84e2a02c2c2c2c3c1c1c3ea9555555550768d5555955665542d33542d0b543d640d5995143544d4555151555555555551501c2c1c3e80c0e0ba8d83c0e0303a5550f0f03030303030303035551b0b0b1b0f07070f03a0337131f0dc4c7c555541da3555555555555555515155541c2c1c3e03980e03950f07070f03546c2c2c6c3c1c1c3c0e80cac7c9c7d55550768d5555551b542d50f5035654ad527544fd513515070b070fa030382ea383c0e0303a80c3c0c0c0c1c0c0c0c0c0c6c2c2c6c3c1c1c3c0e80c0c0c0c031303155550768d555555551b542d50f50356540d035540d55450d51351555555555140d4555554540554070b070f07070f0f07070f0f1b0b0b1b338dc0cce37030f07070f40b0b0b14402c2c2c03c0704c131555555555451114141111001100070b070f07070f0f07070f0f1b0b0b1b1384c0c4e13030f07070f02ca30b0b00b0b0b0f01c1304c5555555541da3551446d50b544d135544d5543d40d5941151344c154450504444004450501507070b07070f070b070b233737230b0b0b0b0f07070f13102c40f01c1304c4dd550b50f554551344c444444440044054507070b0b07070f0f070b070b378dc0cde37030b0b0b0b0f07070f13131305100b0b102c3c0704c13155555555545141411111100110007070b0b07070b0f070b070b0b82c0c2e0b030b0b0b0b0f07070f0b0b130b0b002ca30f01c1304c42d5555555541da3551442d5542d0b5542d50b543d40d5941151344c15505044444400445050070f070f80e0380e03371b370b370b371b0f0f03030303030305541304c0f01c4a8510a81555555555451111111414001101c3c1c3e0380e0380c0cdc0c0c0c2c0c0c0c3c0c0c0c1c0c0c01304c0f01c228e82a555541da3555555144cd50b543d40d5950340d55035541151344c154444445050004450500f0fa950f07070faa1304c50768d55103c3ea83c1c1c3e084c4c0c03141da3551b42d0f6646d1b546d54444d131511101c3c1c3ccc8cdc8e070707070faaaa151304c0f01c031211550f54f5564551344c444444440044070f070f2b1b2b0b2b0b2b1baaa0f0faaaa05451304c0f01c0303030510a1255555555551444445050440044070f070fa82eaa81ea0faaaa004c1303c07280e808a3555541da3655555545133542d50f59556655656504544d130551111414110011141415070b0f070f0f07070f0f07070f0f1b1b0b0b331b1b86c0c6e1b030f07070f1b0b0b1b1b131b06c4c6c0f07070f331f331f555555555555555554545555555580e070b070fa83e07a82ea3aaaaaa0f130b0b13a84e13a0f07070faa55555555555555545455555555070b070b82ea3a030380e03a80c3c0c0c0c1c0c0c0c0c0c2c2c2c2c3c1c1c3c0e80c0c0c0c4c0c4c0c0d5555555555555555555151555680e81c1eaa83c3c1c2c1c2eaaa82ea3aa84eaa130b0b0b0b0f07070faa55555555555554545555555555070b070f80e60380e543c1c1c3c0d5130b0b130f07070f03a03131313135555555555070b070fa030382ea383c0e0303a80c3c0c0c0c1c0c0c0c0c0c4c2c2c4c3c1c1c3c0e80c0c0c0c4c0c4c0c0d555555555555555555545035155541c3c1c3c3c1c1c3c4c4c4c4c3c1c1c3c4c4c4c4d5555555555555555541c3c1c3c3c1c1c3c7c7c3c1c1c3c7c7d55550768d5555542d50f503565450d513515555555555554540f0f03030303030303070707030303030707030380e03a5a0360380c6c2c2c6c7c4c7c1f131f01c1c1c1c0e80c6d0b41e5a50741d03647d1f45d0b53c9d13c9d01d0740d91f47d550f0501c80e0317030b0327034f0303032703270303030703070351304c0304c555a3991741d41d9400d2707d5 24 16777215 10 1023
def hc_66_15 : Nat → Nat := unpackHintV5 0x87f0dc407cdf1f852e4f539bc7708e53a28571c213ccd78a6068f8b3329a7898902f4bdf9a25bc0cf2b52a394b43d4a0295e4af94723a276912f2887ebab03815d21a227a0bc453455224025814410fc71073951429e3fa0de9c205147800c0728000180 0xb0b1b42c2c1c2c3d41d0b0b0b0b1b1b1b1b0f07070f0b0b0b0b1b1b1b1b0f07070f2f1f2f1f42d68d568da35a368d5555555555555555541c2c1c1c2c2c1c1c2c2c3c3c1c2c1c2c2c2c1c1c2c2c2c2c1c1c1c1c2c2c3c3c2c2c3c2c2c2c2c2c2c2c2d50b82c0c2e0b030b0b0b0b0f07070f0f83c0c3e0f030b130b02c2c2c0b0b0b0b0f07070f0f0f0f03c4c3c2f1f2f1f42d42d55a3568d07541d5555545455555454555555170b0b174180c2ea30f0380e03a0f03070327032f03030327032703030303031304c0304c44550f43d500349c49d41c3c1c3c9c6c5c2c5c2c9c6d4114ac5c5c3c1c1c3c9e27032789c0cfc1703c0709c4c09c4c0fc2b1555551415451110f1143d44042711501c3c1c3c3c3c2c3c2c3c3d50f07070f0f83c0c3e0f031f1f0f07070f0f0f0f03c4c3c1f1f541da30707507070751f550f41d0f0f40f451f555030355507070707aa0707a6a55a5aa1b0b0b1b1f131f07c4c7c07070707aa5555555555555554545555555580e07070707a81e07a82ea3aaaaaa071b0b0b1ba884e01c1c1c1ea95555550768d5555551b542d5995595541d640d599515134555551515555555551501c1c1c1e0ba8e80c0e0380ea03070303030703030303030b0b0b0b0707070703a0303030300c4c0c5541da3555555555542d50b541d40d5950340d55034cd5515134555555555151555551500c0d5541c1eaa81c1c1c1e9556a60baa1f131f07c4c7c0b0b0b0b07070707aa55555555555554545555555555a03a0707aaa070f07070707aaaa0ba8eaa138a80b0b0b0b07070707aa55555541da3555555655599550b542d5075959515134555151555555555551501c1c1c1e03980e039507070307070703546c2c2c6c1c1c1c1c0e80c7c7c7c7d1b5541d40d55375544d5555555555550707070780e60380e95540c0c0c0c1c1c0c0c0c0d5546c2c2c6c1c1c1c1c0e80c7c4c7c1f131f15555555555555555555515155541c1c1c1e03980e03950707070703546c2c2c6c1c1c1c1c0e80c7c7c7c7d550768d555555551b542d5075035655bd52754544d1507070707a030382ea381c0e0303a80c1c0c0c0c1c0c0c0c0c0c6c2c2c6c1c1c1c1c0e80c0c0c0c0313031550768d55555550355551b542d50750340d59950340d55035551513455555555545035155555151507070707070707070707070707071b0b0b1b1b86c0c6e1b03070707071b0b0b1b1b131b06c4c6c070707071f1f1f1f55555555555555554545555555507070707070707071f1f1f1f070707071f1f1f1f5541da3555555550b541d40d5951513455555555555551501c1c1c1c1c1c1c1c1c1c1d41d07071b0b0b1b070707071b86c0c6e1b031b0b1f0b1b1b070707071b131b06c4c6c1f1f1f1f1b1b42d0741d0f0f51b0f5334cd1f47d1742d0741d1b1b41b274334cd1f47d55070707070703070707070303a59aaaaaaaaa1b0b0b1b070707071f131f07c4c7caa1b42d07643c3d696647d1f45d0b41d074ac9d0ac9d2647d1f5540c1070b071707070727072707070727076707070707548aa81e031304c1301c550741d5a3176511960381c1c1c2c1c1c1c6eaa81e81c1ea81c1c1c1ea0781e9582ea3aaaaaaaa0780eaa071b0b0b1ba884e01c4c1c07070701c1c1c1ea86d0b69623507070f0707541da3991f47d1742da4901cad01c1d01d076647d1f5541c1c1c2c1c1c1c2c1c1c1c1d582ea3a0303a0303a030380e03a80c1c0ccc0c0c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c1c0c0c0c0c0c2c2c2c2c1c4c1c07070701c1c1c1c0e80c0c0c0c03130302d0b41c1c3c1c1d50768c0d903035032351f47d0b42d07174070740741d03640c0d00c5d05d175541c1c1c1c1c1c0c0c1c0c1c1e966aaa0baaaaaa0b0b0b0b070707071f131f07c4c7caa0b42d075943c3d696647d1f42d0b41d0745c5d05c5d2645d1755680e81c1eaaaa81c1c1c1c2c1c1c1c2e07aa81c1c1c1c1d5aaaa0ba8eaaaaaa138a80b0b0b0b07130701c1c1c07070707aa88d6942d0b41c1c3c1c1d50768e647d1f6174a40b42d07174070740741d991745d55070707070781c1c1c1e80c0d40d030380e0380e03a0303a03031b0b0b1b070707071f131f07c4c7c03a031b42d0740d0f0f50303503647d1f45d0b41d0751c9d11c9d00d91f47d5507070707071b07070707560380e07030380c0c0c0e0380e42c6c1c1c0c0c0c0c0c0c0c1c1c1c1c0c1c1c8e8c0d80c6c2c2c6c1c4c1c1c1c1c1c1c1c1c0e80c7c7c7c7c5d0b41d0741d0740d92348d1f47d070b0717507a0380c0c0e041c9c9c1c1c1c1c1c1c1c9dbc1c1c1c1c0c11301c1304c0741d5a3551742d0749d00741d00741d03640d1f47d550707070b0707071b07070707560380e07a0303a0303030380e0390b1b072707070707076f07070707036031b0b0b1b07130701c1c1c0707070703a031f1f1f1f1b42d07070f0707541da303657d2747d1f41c1c1c2c1c1c1c6c1c1c1c1d5a030382ea381e80c0e80c0c0c0e070380c0ea0307030303030303070307030303030307030f03030307030703030303031b0b0b1b07130701c1c1c0707070703a0303030300c4c0c1b42d07070f0707541da303640c0d03503032351f47d1742d074070740741d03640c0d031030341f47d55541c1c1c2c1c2c1c1c1c6c1c6c1c1c1c1c1c2c1c2c1c1c1c1c1c3c1c3c1c1c1c1c1c1c1c8c1c3c1c1c1c1c1c1d51b0b0b1b1b88c0c8e1b030781c0c1e0703070707071b0b0b1b1b131f07c4c6c07130701c1c1c070707071f1f1f1f568d0b542d41d41d55a35555555454545455555555070707070742c2c6c1d50b0b0b0b070707071b1b1b1b0b0b02c2c070707071b1b1b1b1f1f1f1f42d68d5a368d568da35a368d5a368d5555555555555541c1c1c1c1c2c1c2c1c1c1c1c1c2c1c3c1c1c1c2c1c2c1c1c1c2c1c1c1c1c1c1c1c1c1c1c2c1c3c1c1c1c1d50b82c0c2e0b030b0b0b0b0781c0c1e0703070707070b130b02c2c2c0b0b0b0b07130701c1c1c070707071f1f1f1f42d42d55a341d41d55a355235547d5454555454555555555170b0b174480c2ea380e030703a27032703030327032f0303030703070303031304c0304c44551741d41d9400d2707d5 25 33554431 10 1023
def hc_66_16 : Nat → Nat := unpackHintV5 0x87c8a5428657a0eb16100b1aa7ce4dd3cc86a9d8138ce6217a715070374e569a6c4eccbd1e460a1522cace915673bca0d29a4ba93023649c0fc77ac75523a337dcb17848e8a954b4460ba8201cba0e1c7c856b68c25298c0f4cd205f46c81c94c4000392 0x1c1c1c1e0380e07a8e80c0c0c5c0c0c0c2c0c0ea030303000000000055555555550000000000000000070b070f85c0e0303a030381ea303170303030b0303a80c0c0c00000000015555555554000000000000000005c2c2c5c5c2c2c5ccccc0000015555540000000000001c1c1c1e0380e07a8e80c0c0c6c0c0c0c2c0c0ea0303031b0b0b1b0707070703a0303030300c4c0c55555555555555555555555555070b070f86c0e0303a030381ea3031b0303030b0303a80c0c0c6c2c2c6c3c1c1c3c0e80c0c0c0c0313031555555555555555555555555541c2c1c3c3c6c2c2c2c2c3c3c01b0b0b1b0f07070f0f83c0c3e0f031302c01ca3070700707071304c555555555514455555555514450707070b0707071b07070707006c2c2c6c1e07030781c0c1c1c1c1c4c0b01c1c3c1c1c00728c4c1315555555554551150749d55555554551146c2c2c6e0380e0380c0c6c0c0c0c2c0c0c0c3c0c0c0c1c0c0c01302c1304c228e82a555555555514455555555514451b0b0b1b1b0b0b1b33331b0b0b1b3f3f33333f5555555555555555551b0b0b1b1b0b0b1b33331b0b0b1b43433333435542da3555555543d507540d59515134555555555555545503c3c3c1c2c3c1c3c3c1c1c3d070751b0b0b1b1b86c0c6e1b030f07070f1b0b0b1b1b131b06c4c6c0f07070f331f331f1b1b42d070751b0750f41d334cd1f5ed1742d1b1b41b2740f41d334cd1f5550b0b03030b0b0f03a5a9070b070faaaaaaaa83cac4c7c2b131f06c2c2c6c3c1c1c3eaa941c1d46d0b641d991f4dd2b2742b2741742d0f41d991f4ad5580e070b070fa83e07a0f1b0b0b0b0b0f0faaa0f0fa0faa560ba8eaaaaa83eaaa86c2c2c6ea21380f07070f0f0f0f03c4c3caa1b42da588d50768c1c1d41c1c1e647d3b45d0b6922b40f41d0f0f40f2b4991f4ad55070b070b0b0b0b0b0b0b0b0b560ba8e80c0e0380e80c0e80c0ea030f030303070303030f030f03030303030f0333030303030303030b0b0b0b0f07070f0f0f0f03c4c3c03a0303030300c4c0c0b42d41da30707507070703640c0d40c8d47d3b42d0b43d0743c3d03c5d00d903034031741745d550b0b03030b030b0b070b070ba9a5aaaaaaaa0b0b0b0b2b131f0ac4c7c0f07070faa0b42d07075a5941d6647d3b42d0b45c5d05c5d03d076645d1755680e07aa83c1c2c1c2e83eaaaa83c3c2c2c2c2c2c2c2c2d5aaaa0ba8eaaaaaa138a80b0b0b0b0f07070f0f0f0f03c4c3caa88d6942d0b50768c1c1d41c1c1e647d3b6174a40b42d0f41d0f0f40f174991745d55a0b0b0b0b0f81c2c1c3c0c0d40c0c0d80e03a0303a030383c0e03031b0b0b1b3b131f0ec4c7c0f07070f03a031b42d03035070750341c1c1d03647d3b45d0b4ac9d0ac9d03d0740d91f4ad55070b070f0f1b0b0b0b0b0f0f560380e0380e80c0e80c0e42c6c3c1c1c3c3c3c3cac3c9c3c3c0d80c6c2c2c6c3c1c1c3c3c3c3c0f130f00e80cac7c9c7c6d0b50768c1c1d41c1c1c0d92b49d1f4ed070b070f0f1b0b0b0b0b0f0f5680c0e0ba8e0f0380c0e80c0e80c0ea030f030f0303030703070303030f030f03030303030f03030303030303031b0b0b1b0f07070f0f0f0f03c4c3c03a0303030300c4c0c1b42d41da30707507070703640c0d40c8d47d3b45d0b43d0743c3d03d00d9030340c40c0cad07d2b5542c2c02c2c3c0707507070f41c2c1c3cce3b03338ec0c6c2c2c6c3c1c1c3c3c2c02c2c03c0b03c0704c1304c1d41c1d46d0b43d074bd2f444c3b2703b2701702c0f01c3b0cc0044001c2c1c3c1c1c3c3c1c1c3c3c3c6c2c2c2c2c3c3c3c4c3c4c3c3c3c3c3c4c3c3c3c3c3d51b0b0b1b1384c0c4e13030f07070f0f83c0c3e0f0302ca30b0b00b0b0b0f01c0f0f00f1301304c1b42d131351323541da3070750707072f4bd11305c0b04c4c04cac03c0703c3c03cfc0ec33001102c2c02c0b0b070b070b07070b41c1d42c2c2c2cee37033b8dc0c3c1c1c3c2c0b04c4c03c3c03c0704c1302d0b41c1d42c1d42d074bd2f444c0b02c17170171700f01c1705c004410b0b07070f0f071f07a30b070b070b07070b0b0b0b07070b0b0b0b0b0b0b548c8c8c8c2c2c2c2c3c1c1c3c3c3c3c3c4c1302c0b03c0703c3c0f1304c1305c1702c0b03c0703c0f05c17000007070b0b07070b0f070b070b0b0b0f0b0b0b0b0b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0b542e0b030b82c0c2c2c2c2c3c1c1c3c3e0f030f83c0c2c2c4c2c2c00b28c3c0703c3c03c4c04c1302c2c8d42c2d0b50b42d41da3070750707072f4bd11302c5c02c2c02c0b03c0703c3c03c5c05c17001100c0c1c3c1c3c6c2c2c3c6c3c6c3c3c3c6c3cdc3c3c3d40c0e220380c4c4e203c1306d2341da30741c1c6c2703c3f0ec6cdc2cdc2cec6c1c3c1c3c0c0d40c0c0d80e03a0a0320380c4c1303e0a00f01c0320bd2f40c0d41c1d40d0740d91130ac2b0ac9c0ac9c03c0700c80044070f070f0f330f0b0f0b0f0f560380e0380e80c0e80c0c0c0c0c0c2c0c0c0c3c0c0c0c1c0c0c0c3c0c3c0c0c0c0c0c3c0c0c0c0c0c01304c0f01c0f0f00f130228e82a2f4bd41da30707507070703640c0d40c8d444c2b0ac0f01c0f0f00f3f003200c0c00cac001103c3c6c2c2c3d6aaa83c3c3c1c1c6c1c3c3c3c3c3c6c6c3c6d2c3c3c3e084c4c3c1300c0301da30741c1c6d2343c2b06c2701c3c1c3eaaa8ac6cac2cac2cac6e6a9682284c1303c072200c0c03c0c0bd2f641d9907075a51130ac2b03c07220ac9c0ac9c001101c3c1c3c3c3c3c3d5232323230f0f070707071fa3a81c1eaaaaaaaaa1a1304c0f01c0f0f03c4c0304c882b0ac0f01c0f03c2308c8800070f070f0f330f0b0f0b0f0f56a0baaa07a83eaa0faaa0f83eaaaaaaa801304c0f01c0f0f00f130a03a0228cbd2f50768c1c1d41c1c1e88d69966444c2b0ac0f01c0f0f00f2b08ac2822001115070b070f07070f0f0f0f072307070f0f0f1b0f1b0b0b0b0b0f0b0f0f070707070b0b0b0b0f0b07070f0f0f0f546c2c2c6c6e23032386c0c3c1c1c3c3e0f030f83c0c6c2c2c6c6c4c7c23131b03c1c1c3c3c3c3c0f130f0bc7cbc7d5a342d50b55a341d5075551f555554545554545555555 25 33554431 10 1023
def hc_66_17 : Nat → Nat := unpackHintV5 0x897c9420813bc7e247c1e3c29a7470901c092266ac4ac18a94105b34ee16c001a5aa40b956e27650d89c12523c845647c8fa53683b446a0d9f26432887e8bd11a22a709a89ac1e021d89b073927a19b86585951b214204684331aa0b4cb0021118403cc8f00001e6 0xc0d40d030307070707a07070781c1e0380e80c0e80c0e070380c0c2c2c2c2c7c4c7c1f131f01c1c1c1c0e80c2d034ac6d40c0d41d0740d91f47d0b42d17174171740741d03645d1755550707070707070707070b070f07070707a0303a030380e0381ea3a0303030b0303030303030b030b03030303030b0303030b0303a80c0c0c2c4c2c0b0b0b02c2c2c2c1c1c1c1c0e80c0c0c0c03130302c2ccc2c2d50b68c1d0740d903035032351f47d0b1740b0b40b42d0741d03640c0d00c5d05d175541c1c1c1e96681c1c0c0c1c0c1c1eaaaa81ea3aaaa0b0b0b0b070707071f131f07c4c7caa0b641d074cc6d696647d1f42d0b41d0745c5d05c5d2645d175555aa82e0baa82ea82ea0b070707070707070707070707a03aaaaaaaaaa07a8c2c4c2c0b0b0b02c2c2c2e138a807070707aa0b0b330b0b542da388d6941d076647d1f42c5d02c2d02d0b6174a40741d991745d55030350340c0c1c2c1c2c1c1c2e0707a80e03a0303a030380e030b0b0b0b37131f0dc4c7c0f07070f03a030b40d331b5030350f41d03647d3742d0b45c5d05c5d03d0740d91745d550b0b1b070b0b070b0f070b07a030380c0e0380e0380c2c4c2c2c2c2c6c6c6c6c3c1c1c3c0e80c2c2c6c6c6d40d1b68c3d0740d91f4dd0b1742c2d1745d0f41d03645d175555070b0b0b070b0b0fa3070b070b82c0c0e030303a380e0380e030b0b030303030303030b0b0b0b030b0b23a39070f036030b130b0b0b0b0b0b0b0b0f07070f03a03231f231f0b1742c2d0b42d0f41d03645d1745d1755070b07070b0b07070b0b0f0f070b070b82e80c0e80c0c0c0e0b0380c0e80c0e07a8c0c2c0c0c0c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c2c0c2c0c0ea0303030b130b02c2c2c0b0b0b0b0f07070f03a0303030300c4c0c0b0b330b0b542da30f41d03640c0d03503032351f4dd0b1740b0b40b42d0f41d03640c0d00c5d05d17555507070b0b07070b0f070b070b0b0b0f1f0b0b0b0b0b0b0b0b0b0b0f0f0b0b0b0b0b0b0b0b002e0b030b82c0c2c2c2c2c3c1c1c3c3e0f030f83c0c2c2c4c4c02c2c0b00b02c01ca3070700707071304c0b0b5b0b0b542da30f41d0f0f50f1f52f4bd11302c5c02c2c02c0b03c0703c3c03c5c05c17001100dfea3037f80fa34bc1c1c1c1c1c1d41d0707070700701c1c2c2c2c2c1c1c1c1e7f037f80c2c0b01c1c0701c3c3c02c2c04c1302c2d41d0b68c1d074bc6d41c1d4bd2f41f44c4c0b02c0701c17170171701705c05c04c44542d4c2c2c2c2c2c9c2c2c2c2c1c1c1c1c1c1c1c1c1c1c1c1c01c1c2e0b030b82c0c2c2c2c2c9d5d5c9c1c1c1c1c2c4c02c2c02c0b03c1301c0704c1302c2d1c2c2d50b68c9d2f41d074bd2f444c541c1c1c1c1c2c1c2c1c1c1c1c1c2c1c1c1c1c2c1c1c1c2c1c1c1c1c1c1c1c1c1c1c1c1c00b82c0c2e0b030b0b0b0b0781c0c1e0703070707070b1300b0b00b02c07070f0707001ca31304c0b0b470b0b542da307235070750741d2f4bd07d131302c5c02c2c02c0b01c1c5c01c1c0710701c1705c05c04c44030350340c0c2c2c2c2c7c1cdc3c7c1cdc3e0380e80ca080e030b02ca00b804c1300c80b40d2f1b5030352f47d036444c0b02c17170171701705c0320011150b070b0b0b070b0f0b0b0b0ba0303a030380e0380e03030b0303030303030b030b03030303030b0303030b0303030f030303070303002c2c4c4c02c2c0b00b02c1304c228e82a0b0b330b0b542da32f47d03640c0d40c8d444c0b1700b0b00b02c1705c03200c0c00c5c001102c2c2c2eaaaa9669fc3c7c1c7c1e3c3e82282c0b04c1328880c0c02c0c02d92f47d992f1b5a511302c0b05c172205c5c05c5c0011150b070b0b0b070b0f0b0b0b0baa82e0baa82ea82ea0ba81ea0faaaaaaaa002c4c02c2c02c0b04c13280e808a30b0b330b0b542da32f47d88d6966444c0b1700b0b00b02c1705c85c28220011150b070b0b0b070b0f0b0b0b0b0b82c0c2e0b030b0b0b0b0b130b02c2c2c0b0b0b0b434343430b0b0b0b542da3554350b1740b0b40b42d1745d1745d1745d550707070780e03a680c6c6c0c0c0c0c0c0d56940c0d5546c2c2c6c1c1c1c1c0e80c7c4c7c1f131f1555555555555555555515155541c1c1c1e0380e07a8e80c0c0c6c0c0c0c2c0c0ea0303031b0b0b1b0707070703a0303030300c4c0c5542da355555555554cd41d507540d03566540d035540d554544d155555555454555555154070b070f86c0e0303a030381ea346c6c0c0c0c0c0c0e95540c0d5546c2c2c6c3c1c1c3c0e80cdc4c7c37131f1550b68d555555555555555554545555070b070f86c0e0303a030381ea3031b0303030b0303a80c0c0c6c2c2c6c3c1c1c3c0e80c0c0c0c0313031550b68d55555555553350f541d50356540d035540d554544d155555555454555555154070b070f0f1b0b0b0b0b0f0f006c2c2c6c3c1c1c3c3e0f030f83c0c4c0b00728c1c1c01c1c1c4c131550b68d55555554515b50f43d50741d50f43d550f47d55035650544c15444450504400445105401c2c2c8e8c2c2c6c8c1c1c1c1c546c2c2c6c8d2ccc8c1c1c1c1c4c0b03c407104c1312354b5541d40d54544c44444444004540707070707071b1b0707070705451b0b0b1b3391c0cce4703070707071302c0f0f05007104c131555555555451114749c1441111001106c2c2c6c1c1c1c1c1c51b0b0b1b33533353070707071302c13101c41304c55555555141b0b0b1b07070707051b0b0b1b27573327070707071302c0f101c41304c5542da35555551451d49d27554d541d507540d59415130541c1c1c2c1c2c1c1c1c6c1c6c1c1c1c1c01b0b0b1b0781c0c1e0703070707071302c07070f0707001ca31304c5542da341d5555555515451d41d5541d075541d0f541d07540d5941151344c154441d05114444104445105406c2c2c6e0380e0380c6c6c0c0c0c0c0c0cdc3c7c1c7c1cdc3c15504c0b04c1312a14281555555555451111111414001106c2c2c6e0380e0380c0c6c0c0c0c2c0c0c0c3c0c0c0c1c0c0c01302c1304c228e82a5542da355555555144cd43d507540d03566540d035540d550544c154444445050004451054150b0b0b0b1b071b0f1b071b0f0b0b0b0b1b86c0c6e1b03333333330b0b0b0b1b131b06c4c6c5b2f472f332f332f568d0b542d55555555545455555555 26 67108863 11 2047
def hc_66_18 : Nat → Nat := unpackHintV5 0xf4ea4eeb426ae4f992db3a70cc13cac449f2be6978b1733ea68aba9f79c49831d292c15c8b29e68471ae7b12587579666e41ce68497e61c1a257ba824e3a6049892c42e9a83c719e322a922c2980238a281e49501771b61259460ae1de0002b8 0x70707070741c1c1c1d41c1c01c07071b0b0b1b07070707338dc0cce37031302c0701c0f0f0130f01304c0750b50741d0b0b5070752f4bd07d131305c0b01c070dc9c0dc9c0dc330011151b230b0b0b0b23a30707070b0b070707070707070707070707070707107071b0b0b1b1b2303231b0323232323070707071302c131304c4c0f04c0701c1304c1702c1b08c2308c0701c2f0bc005170b0b171b271b2727272f27371b271b070707070080e0380e0300005a30b42d551702c1b09c02709c00701c0709c270011151b0b0b1b1b47272747531b27070707070707070707070707007071b0b0b1b1b8cc0cce1b0327573327070707071302c13130131300f04c0701c1304c42da30b0b50b0b0b274bd0741d2f4bd113150707070b0707071b0707070707370707070707071b071b070707070707070707070707006c2c2c6c6e33033386c0c1e07030781c0c1c1c1c1c4c0b04c4c04c4c01c1c3c1c1c00728c4c1310b68c2c2d42c2c2c1c1c8d41c1d0750741d2f4bd07d131305c0b06cfc0bcfc01c1c01c1c0710701c0cc07c04c440303503030347c1cdc3c7c1cdc3c6c2c2c6e8280c80e0380e031382804c0b04c1300c8030350b0b50342d2f47d036444c37270372701702c7707c0320011141c3c1c3e0380c5c2c2c5c6c9c6cbc9cdc9c9c9c6c9c6c3c1c1c3c00000168c2d0b49d235540b002709c2700c0300551b0b0b1b1b07330f1f071b0f80e03a0303a030380e03031b0303030b0303031b031b0303030303330303030303030f030303070303004c0b04c4c04c4c04c1308a3a0a90b68c2c2d42c2c2cbd1f40d9030350323511305c0b06ccc0bcdc01f00c8030300300044505554005c2c2c5cbc1c9c3c9c1cbc3c6c6c6cac6cdc6c6c5c2c2c5cbe2703278bc0c6c6c6ccc6cac6c6ccccccccc5c0b0bc4c09c4c06c6c06cbc0bc2f0bc2f15a342d555410b5555451171146d46d1b01144453300115141145c2c2c5c9c1c9c3c9c1c9c3c5c2c2c5c9e27032789c0cacacacac5c0b09c4c09c4c0ac3f0dc2b1555141555451171146d44452700115151b0b0b1b1b070f071b0f1b0b0b1b1b8cc0cce1b0333331b0b0b1b1b134304c6c434333334342da30b0b50b0b0b54cd4351742d1b4454cd43555070b070baa0b0ba0303555aa6a55a50b0b0b0b0f07070f4f131f13c4c7caa55555555555555555454555555070b070b82ea0ba80eaa82e07a8eaaa0b0b0b0b0f07070fa884e2a90b68d5555555555550b50f541d59955955640d599515134555555515155555551501c1c1c1e0380e0760303030303030b0b030355a503035550b0b0b0b0707070703a031f131f07c4c7c555555555555555555545455550707070780e0381ea3a0303030b0303030b0303a80c0c0c2c2c2c2c1c1c1c1c0e80c0c0c0c03130310b68d5555555555550b507541d50356540d035540d554544d15555555545455555454a0b0baa070707070303555aaa555a981c2c2c2c2c7c4c7c1f131f01c1c1c1ea955555555555555515155555556a0ba82c1c1c1c1e80eaaaaa81ea30b0b0b0b84e2a01c1c1c1ea90b68d5555555555550b5955665541d507565654544d15555454555555555454070b070b80e0380e42c2c0c2c2c2e540d50b0b0b0b0f07070f03a032f1f231f42d43d5503554dd5513555555555555541c2c1c2e0380e039030303030b0b0303a55503035550b0b0b0b0f07070f03a0337131f0dc4c7c555555555555555555554545555070b070b82c0e0303a030381ea3030b0303030b0303a80c0c0c2c2c2c2c3c1c1c3c0e80c0c0c0c03130310b68d5555555550355550b50f541d50340d59950340d550355515134555555555151555551501c2c1c2c2c2c2c2c2c2c2c2c00b0b0b0b0f07070f0f83c0c3e0f030b02c01ca3070700707071304c42da355555555551442d43d507543d0f5543d1f5540d59415130551111414110011141401c0707070707071b1b1b1b07103c0b04c131555555451541d46d40d54544c551111100111101c1c2c2c1c1c1c1c1c1c1c1c15142c2c2c2d2e4b034b92c0c1c1c1c1c2c0b03c3c1401c41304c42d555555555451114141111001102c2c2c2c1c1c1c1c142c2c2c2c9d5d5c9c1c1c1c1c2c0b03c407104c1310b68d55555554510b527554d507541d5035650544c150707070b070b0707070b0707070707002c2c2c2c1e07030781c0c1c1c1c1c2c0b01c1c3c1c1c00728c4c1310b68d55555555545510b5075550741d5507541d50356504544d1305511074144511104111141402c2c2c2e0380e0380c0c0c0c0c2c2c0c0cdc3c7c1c7c1cdc3c15502c0b04c131214281555555555451111111414001102c2c2c2e0380e0380c0c2c0c0c0c2c0c0c0c3c0c0c0c1c0c0c00b02c1304c228e82a42da355555555551442d43d507540d5950340d550355415130551111114140011141402c2c2c2e82c2ea93c3c7c1c7c1d3c3eaaa815142c0b04c1300c0c14211555555555451111141411001102c2c2c2ea0ba82ea07a83eaaa800b02c1304ca03a0228d0b68d5555555554510b50f541d5955665565650544c154444505044004450500b0b0b0b0b0b0b0b0b0b0b0b4343434342da35555555542d43d507540d59515134555555555555515296681c2c1c2c1c1c2c0c1c1c0c0eaaaaaaaa82c2c2c2e3c4c7c6b131f03c1c1c3ea82d9331b5a50f41d991f5ad0b42d17174171740f41d991745d55541c1c2c2c1c1c2c3c1c2c1c2e0baaa0b82eaa0ba82ea03aaaaa0b80eaa0b81ea3aaa82c4c2c0b0b0b02c2c2c2c3c1c1c3ea2138aa0b0b330b0b542da30f41da588d6647d6b42c5d02c2d02d0b43d07692174991745d55 24 16777215 10 1023
def hc_66_19 : Nat → Nat := unpackHintV5 0x8809db41c0912007364f1a3a6747d153826861b33380d1a9fc65bcc631286d97c0350b6b9d259288d29f8a7142934c9a49c04988e723406110c038080c1503d60c01d844b0cda7a05793d027492012345c07507283102601578c20700ef01cb6d4000396 0x1c2c1e8c1c1c2c2c1c1c1c2c3c2e0380e0380e80c0e80c0c0c2c0c0c0c2c0c0c0c3c0c0c0c1c0c0c0c2c0c2c0c0c0c0c0c2c0c0c0c0c0c00b02c0f01c0b0b02c02c2c4c4c08a3a0a82c2c2c2c3c1c1c3c2c2c2d0b370b40e80c0c0c0d0337034131302c0b03c0702c2c02c5c00c80303003170001705c070b070307070303030303030b0b03030303030380e0380e03a0a0304c0b03c0703e0a0032a06c2c2c6c3c1c1c3cec8cdd3b233740e80c131305c0b03c070ac9c0ac9c00c8002b0ac075070b50b80e031b030b030f0307032f037703030323032303030301304c8a38a1b1b0f0f0f0fa0303503232344c4c9c2700c2b0acac1c1c2c2c1c2c1e8c1c1c1c2c2c2e0380e0380e80c0c0c0e0fa0303031b0303030b0303030f030303070303030f030f03030303030f0303030303004c0b03c0703c3c03c4c08a3a0a86c2c2c6c3c1c1c3c3c3c3d0f0f40e80c0c0c0d03034131305c0b03c0703c3c03cfc00c803030032b0002b0ac030350340c0c6c2c2c6c7c1c8c3c7c1c8c3e0380e80c0e80c0e0380c4c0b04c4c04c4c04c1300c81b1b40d1b1b1b1b2347d036a444c1702c23270232302f07c0320012f12300c0c0c6c2c2c6c6c1c6c3c6c1c6c3e030380c0e80ca080e03131302c4ca013804c1300c81b0b0b1b1b1b1b46c6d1f1f3703a0304c4c1702c1b1b01b27007c032000dc01c2c2c1e8c1c1c2c2e0303030fa031b0b0b1b0f07070f0f0f0f0f37370f23230f0f0f140f04c880f0f50f232340c0c0c0c4c4c3c3f09c2707cdc7e0380e0380c8c6cdc2c8c2cdc6c8c3c7c1c7c1cdc3c1640c1304c1304c03204e0a02348d2347d0303640c0c0c0c44c4c4c0dc07c0320bc9c08c9c001107c5c5cae0380e0380c8c6c5c2c5c2c8c6c8c3c7c1c7c1c8c3c0c0c000000000000123555515948d000027000000000000007c5c5cae0380e0380c9c6c5c2c5c2c9c6c9c3c7c1c7c1c9c3c00000000000001174ad1f40d9275272750000270270000c00030000009c1f1f80e0380e03030303030b0303030f030303070303004c1304c1308a3a0a87c7c0e80c0c0c0d030341313001f00c8030300300000781c2eaaaa81c1eaaaa83c3e82282c0b03c0728880c0c02c0c02c2c2c2c3c1c1c3ea8ac8cad2b232b4131302c0b03c072205c5c05c5c0005c171070743d43e0b82e0783ea2388ea2f8dea804c1320388a30b0b0f0f0b0b23645c1705c8070b07a307070b0b0707070b0f0ba82e0ba82ea81ea0faa82eaa82e0baaaaaaaa002c0b03c0702c2c02c4c280e808a30b0b0b0b0f07070f0b0b0b42c2da6a6a8131302c0b03c0702c2c02c5c2170a088001705c0b0f0baaaaa81c1c1c1c3c2c2c6e283c0702c2c0b132200c0b03c1c1c3c2c2c2c2ea86c6c6c6c131303c0702c0b2205c170005c1706c2c2c6eaaaa96688c3c7c1c7c1c8c3eaaa84c0b04c132204c4c04c4c06c6d91b2347c7c7d991b1b1b11305c0b0bc1f2208c9c08c8c001106c2c2c6c6eaaaaaa1b0f1b071b071b0fa08a131302c4c1304c8803030130301b0b0b1b1f1faa1b1b1b46c6d04c4c1702c07c881b1b01b2700000b07a3070b07070f0b0b0b0b0b0f07070f0b0b0b0b23230b4f470b0b0baa110b04c0300c0f0f0b48daa13130b05c1705c1f1f33331b230b4f0b231b4f0f1f071f07230faaaa05891304c1304c0303013030882348d2347daa6a444c4c4c33007c232702f2708800441f17172b231b170b170b231b230f1f071f07230faaaaa0000000000000555548d51000000000000000001f17172b271b170b170b271b270f1f071f07270faaaa000000000000003345d2b47d2727527599000009c008008000001f1f33a82eaa81ea0faaaa004c1304c13280e808a333331f1fa6a6a813130cc01f20a088000541c6c2c1c3c3c1c6c1c6c1c1c3c3c3c3c3d0b0b07075070707070f0f0f1b0b0b1b1b1b1b331b2b1b1b0f07070f0f83c0c3e0f031b0b0b1b1b1b1b1f1b371b1b0f07070f0f0f0f03c4c3c331f331f42da30b0b50b0b0b0f0f41c8d0b0b50f0b52348d1f48d1742d1b1b51b2b50f41d0f0f40f474334cd1f4bd55070b507070741c1c3c3d507070707070707071b070707070707071b071b0781c0c1e07031b0b0b1b1b1b1b331b331b1b0707070707130701c1c1c1b0b0b1b1b1b1b1f1b1f1b1b070707071f1f1f1f070b50707542da30b0b50b0b0b072341c1d2348d1f47d078b4070741742d1b1b51b3750741d334cd1f47d550303503030341e0707a070707070707a0303a030380e0380e031f131f07c4c7c1b0b0b1b0707070703a03030350b0b50342d0741d03647d1f4ac9d0ac9d05d0b41d0740d91f47d5550707070780e03170b0b171b271b3327372727271b271b1803044c1304c13168c2d0b5550b502749c41c0d0347d5541c1c1c1c1c1c1c1c1c1c1c1e0380e80c0e80c0e07a8e80c0c0c6c0c0c0c2c0c0c0c6c0c6c0c0c0c0c0ccc0c0c0c0c0ea0303031b0b0b1b1b131f07c4c6c0707070703a0303030300c4c0c42da30b0b50b0b0b0741d03640c0d40c8d47d1f45d0b46cad0ccad01d0740d9030340341f47d550303503030341c1e81c1c3e070b070fa0303a030386c0e030380e0337131f0dc4c7c1b0b0b1b0f07070f03a03030350b0b50342c2c2d0f41d03647d374dc9d0dc9d05d0b43d0740d91f62d555070f070f80e03170b0b171b271b3327372727271b271b8103044c1304c13168c2d0b49d235550b502749c0f40d035275541c2c1c3c1c1c3c3c1c1c3c3e1b0380c0e80c0e80c0e80c0e07a8c0c6c0c6c0c0c0c2c0c2c0c0c0c6c0c6c0c0c0c0c0ccc0c0c0c0c0ea0303031b0b0b1b1b131f0cc4c6c0f07070f03a0303030300c4c0c42da30b0b50b0b0b0f41d03640c0d40c8d47d3745d0b46cad0ccad03d0740d9030340341f555050b0b1340151307130f1307130f1b0b0b1b1b1b1b371b1f1b1b1384c0c4e13031b0b0b1b1b1b1b331b331b1b331f1f33131313131302c1b13131313006c1b1304c1304c130b50b0b042da30b0b50b0b0b2347d2348d08d131304cbc04c4c05c0b06c6c06cbc0bc1f0bc2f001115070b070f07070f0f07070f0f0f1b0b0b0b0b0f0f0f1b0f1b0f0f0f0f0f1f0f1f0f0f0f0f006c2c2c6c6e33033386c0c3c1c1c3c3e0f030f83c0c4c0b04c4c04c4c00728c1c1c01c1c1c4c1310b68c2c2d42c2c2c3d0743c3d43c7d4bd2f444c1702c1b2b02f2b00f01c0f0f00f1f00cc0044 25 33554431 10 1023
def hc_66_20 : Nat → Nat := unpackHintV5 0xce18b961cca82ca48855af146a690dd50d04f27981a12c12168de1054370702010350f161e46e19533180b19706374a532604bd8d82328588f0c51065725e2bd0dd15800d0ab80105340502380c4114c0e885c0942ff25e13d88408643102403e4000240 0x707070780e0380e031b02c6c1c0707032031302c0700c03203c1f131306c2c2c6c1c1c1c1c0e80dbdbdbdbc131301c1c1c2c1c1c1c6c1c1c1c1c080e03a0303a030380e0380b1b070727270707070707073f07070707032031302c07070f0707001ca303204c1f131306c2c2c6c1c1d07070741c1c1c1c0e80cfc9c9cfc1f13131301c1c1c2c1c2c1c1c1c6c1c6c1c1c1c1c0a030382ea381e80c0e80c0c0c0e070380c0ea0307030303030303070307030303030307030f03030307030703030303031302c07070f0707001ca303200c0c0300303131301b0b0b1b070741c1c1d0707070703a0303030340c0d07c4c4c4c1702c07070070701c170701c03200c0c03003033f007c04c00386c2c2c6ea88c8e4b37aa07078442ea3aaaa81e04c0f03c1b1ba588c8d07070707a131383f09c2702c2c2c2c442ea380e0380e88c0c8c0c0c0d2c0ccc0c0c0c1c0c1c0c0c0c3c0f00c1302c2c1c1c1c1c0c0c0c0d40c8c8d13131705c0305c80e4b4baaa88c8c2c2c2c2c1e81c46a82ea3aa13203c0f223236942c2c1c1c1c1e84c4c5c81705c1b0b0b1b1180e03273f273f0f03c1b1b0707070703033f3f13131b0b0b1b1180c2ea380e030703a2303230303034b034b03030307030f030703070303030f03c0303003131306c6c1c1c1c1c0c0c0c0c0d2303513132709c03030033f12c6c8c2d2c2c8c6c1c1c1c1c141c0748e4b034b88c0c1c1c1c1c4c1303c3c04c3c01c0704c1308d2341c1c1c1d07070748d23444c4c4c0232702f2700701c00044170b0b170080c2ea380e030703a27032703030327035303030307030703030300002757d034bd1702c0701c0700c80300c00309c0002709c231b170b170b231b0707070707070002b17175f2388c0c8e23030707070700000000005548d515500002700701c000000000128c00271b170b170b271b0707070700002b17172789c0c9e270307070707000000000045d272752750741d4ad0009c027001c01c007009c0270000009c02701b27270b0b27a30b0b1b270b0b0b0707070707070701c1c001c1c6c2c2c6c6e33032b86c0c9c9c9c9c1c1c1c1c4c0b04c4c04c4c03c1301c0704c1306c2c2c6c6d1d1d47571b49c9c9c9c1c1c1c1d5cacad5c131302c2c2c2c2c9c2c2c2c2c2c2c9e8c1c1c01c1c1c07070707007070b82c0c2e0b030b0b0b0b272727275327070707070b1300b0b00b02c0f04c0701c1304c0b570b42c2c2d0b0b0b0b27272727532707070707572b2b5704c4c80e1b0b0b1ba89e2ba07070707a81e07a0070782ea3aaaaaaaa071302ca084c03c1301c8881b0b0b1ba998e49cacac9c1c1c1c1ea8131302c2c2c2c1c1c1c1c01c1e0ba8e80c0e0380e0380ea032703030353030303070303030703030303030b02c0f04c0700c03200c0c00c4c02c2c2c2c9c9c1c1c1c1c0e80c0c0c0d03630341313280e2baa89c2c2c2c2e07aa81c1c1c1c1c01c1eaaa82ea3aaaa84c2802c0b03c1301c88898e6a42c2c2c2c9cacac9c1c1c1c1ea8131320b0b1b070707070701c1e0380e0380e0380c4c0b04c1301c0300c81b0b0b1b535353530707070703a0304c4c1b0b0b1b0707070700707a030382ea380e0381c0e0303a80c9c0c9c0c0c0d4c0c0c0c0c1c0c0c0c1c0c0c0c0c0c4c0b03c1301c0300c803030031301b0b0b1b27270707070703a0303030340d8c0d04c4c27272727070707070070780e0389ea3a030380e03032b0303030b0303a80c0303030700303031304c0f04c0700c03200c0c00c4c15d5d5d5c9c9c9c9c1c1c1c1c0e80c0c0c0d032b03413132a0ba91c9c9c9c9d4c9e80c1c1c1c1e070a800707aaaaaa27a8ea84c132130a00f04c072220cd5d5cce579a92727272707070707aa04c4ca327330b034cd03a327532758c6c2c0e0352727272707070707052b2b27272727070707071304c0f101c41304c5549d275555551451d50b549d4541c1035650544c15a380ccc0cbc0e8e8e7c0cbc0c9d4e8d2f2f47530b2f0b5347272727275327541c1c1c1c1c1c01c1c1c007072b2b2b8bc0cae530327272727070707071304c13130131300f04c0701c1304c2f4bd2727272727549da30741d2f4ad11309c9c1c1c1c1c01c1c9c9c1c1c1c1c4c1303c1301c0704c1309c9c1c1c1c1c131301c1c1c1c5c5c5c5c1c1c1c1c00000155555400000000000001c1c1c2c1c1c1c1c1c1c1c00781c0c1e0703070707071304c07070f0707001ca31304c070741c1c1d0707070707c4c4c4c007070070701c0701c007c04c00703070b03030303070703030f0f03030303030380e0380e03a0a0302c0b03c0702e0a003202c2c2c2c3c1c1c3cdc8cdd37233740e80c131302c0b03c0705c5c05c5c00c8001705c 25 33554431 11 2047
def hc_66_21 : Nat → Nat := unpackHintV5 0x88a4ae41aaaa1fb5480f512267299fc38184d1aeb484ced2226490b62fa4a91712300aa239c5250b0267aab92603748942703ce5ef1c98768d075145e22862b54ef13ea7008855c03cd9d41695f60b3006858105c2489e00ea8e70470b9010b4b4000216 0x1c2c1c3c2c8c8c2c2c2c2c2c2c2cbd3c2c2c2c2c0d40eaa642c4c2c0b28c4c1308d0b43c3ea85c0b05c170007070b0b07070b0f070b070b82eaa82e0baa82ea0ba80eaaaa82e03aa82e07a8eaaa0b0b130b0b002ca30f01ca084c2202c2d0b0b0b42c2c2c2c3c1c1c3ea69aa04c4c0b1700b0b00b02c0f01ca085c220005c1700c0c00c0303070b070b07070b81c1ea0380e80c0e80c0e0380c2c0304c4c00c0c03c0700c80b0b0b0b3723374dc8cdd0f07070f03a0304c4c0b02c17170171700f01c0320005c1702c2c6c1c2c2c1c2c3c1c2c1e80c0e030380e0380e030b0b13131300306ca30f01c03202cdc2c2c2c2c6c6c6c6c3c1c1c3c0e80c131302c5c0b0b05c1703c0700c8001705c001c1c2c2c1c1c2c3c1c2c1c2e0ba0303a0303030382c0e0303a030381ea3030b0303030303030b030b03030303030b030303030b030b0303a80c0c0c2c2c4c2c2c00b28c3c0700c8030300c00c0c4c4c02cdc2d0b0b0b42c2c2c2c3c1c1c3c0e80c0c0c0d0337034131302c5c02c2c02c0b03c0700c80303003170001705c11070f070f2388ea378dea0b82e03aaa0b07a8ea84c13204c0b0b0b0b0f0f92344c4c5c17205c050b02d1f07370f1f07230f0b0b0b0b238dc0cde23030b0b0b0b1f1f3713130131300b02c1304c1304c0b0b0b0b42c2c2d2347d2348d113131305c5c05c5c02c0b05c1705c170011000b070b0b0b070b0f0b0b0b0b0b82c0c2e0b030b0b0b0b1f1f0b0b130b0b002ca31304c1304c0b0b42c2c2d0b0b0b0b1f1f04c4c0b1700b0b00b02c1705c1705c001705c03503070f070f1b0b0b0f1f0f1f0f0f0f1f0f1f0f0f0f099aa1304c0728c1c07071b1ba0f47da2709c0f07c2b2b80e070b070fa83e07a0f1b0b0b0b0b0f0faaa0f0fa0f1faa020ba8eaaaaa83eaaa84c0b28213001ca307070070707881b0b0b1ba9a43c1c1c3c3c3c3d0f1f0f6a8131305c0b2822b00f01c0f0f00f1f088002b0ac0b0b0b0b080e03690f07070f0f0f0f0f1f1f0f1f1f0f0f0f035030728c1c07071304c0b0b0f47d030303030f05c1705c070b070b0b0b0b0b0b0b0b0b020ba8e80c0e0380e80c0e80c0ea030f030303070303030f030f03030303030f031f030303030303030b02c01ca30707007070703200c0c00c4c02c2c2c2c3c1c1c3c3c3c3d0f1f0f40e80c0c0c0d03034131302c0b03c0703c3c03c5c00c80303003170001705c0340d070f070f1f0f1f0f0f0f1f0f1f0f0f0f0b0b0b0b099aa1304c0728c1c0707a0b0b0f47da1705c0f05c0a03a0707aaa0f0f070b070ba0f1faaaaa0f0f0b0b0b0b0b0b0b0b02aaa82ea3aaaaaa84c2802c0b00728c1c1c01c1c1e229a90b0b0b0b0f07070f0f0f0f43c7c3daa04c4c85c2802c0b03c0703c3c03c5c220005c1706c2c2c3c20380e583c1c1c3c3c3c3c3c7c7c3c7c7c3c3c3c0d40c1ca30701c1c4c1306c6c1c1c3c3d43c7c7d0303030313130f07c2709c070b070f0f1b0b0b0b0b0f0f020380e0380e80c0e80c0e02c6c3c1c1c3c3c3c3c7c3c7c3c3c0c80c4c0b00728c1c1c01c1c1c0c81304c1b0b0b1b0f07070f0f0f0f43c7c3d03a032b27272b04c4c070b070f0f1b0b0b0b0b0f0f0280c0e0ba8e0f0380c0e80c0e80c0ea030f030f0303030703070303030f030f03030303030f031f030303030303031302c01ca30707007070703200c0c00c4c06c2c2c6c3c1c1c3c3c3c3d0f1f0f40e80c0c0c0d03034131305c0b03c0703c3c03c7c00c8030300c00c0cac000ac2b01c3c1c3c3c7c3c2c3c2c3c3c00f07070f0f83c0c3e0f031304c01ca3070700707071304c0f07070f0f0f0f43c7c3d04c4c00f01c0f0f00f1f00000070707070707541d0707070707070707070707071b0b0b1b070707072388c0c8e23031302c0701c13130131301304c1b1b50746da30741d1b1b1b234cc8c8d11305c0b01c0708c9c08c8c0bc2f0012f12301c1c1c1c1c1c1c1c1c1c1c01c07071b0b330b1b1b070707071b86c0c6e1b03131302c4c0701c0f0f0130f01304c1b0b0b1b1b070707071b1b1b46c6d3333333304c4c1702c0701c1b1b01b270330cc000070707070703070707070303a08aaaaaaaaaa1302c07203c3c282206c2c2c6c1c1c1c1cdc8cdd3723376a8131305c0b01c070ac9c0ac9c22000ac2b00d40c1c2c1c6c1c1c1c8c1c8c1c1c1cbc1d3c1c1c1c1c266a84c1301c3c1c0728c6c6e81c8c8d07075a1f132709c072b6301c1c47c4cacae0381c1c1c2c1c1c1c6eaa81e81c1ea81c1c1c1ea0781e8082ea3aaaaaaaa0780eaa071302ca084c01c1c3c1c1c00728e206c2c2c6ea69070741c1c1d07070707aa07c4c4c4c1702ca08fc01c1cac01c1c0705c1c072201f0130ac2b01c2c1c2c20380da41c8c8c1c1c1c1c1c1c1cbcdc1c1c1c1c0d40c1c3c1c0728c4c1302c2c1c8c8d07075030303031f1307176301c1c45c1705c4c1c1c1c2c1c2c1c1c1c2c1ccc1c1c1c1c082ea3a0303a0303a030380e03a80c1c0ccc0c0c0c0c0c1c0c1c0c0c0c0c0c1c0c0c0c1c0c0c0c0c0c2c0b01c1c3c1c1c00728c0c803030031300b0b0b0b070741c1c1d0707070703a0303030340c0d07c4c4c4c0b02c0707170070701c170701c03200c0c00c5c01701305c171a38723a361c8c0e03c1c1c1c1c1c1c0c0c1c0c1c1e822aaa82ea3aaaaaa0b02c07203c3c282202c2c2c2c1c1c1c1c8e1d87236a8131302c0b01c0705c5c05c5c220005c1700d0341c1c1cbc1cdc1c1c1c8c1c8c1c2c1c2c1c1c1c1c266a84c4c4c131f0070f0701ca3a0b0b07232341c1d687c4c5c1701c5d8c0707117130a03a0707aaaaa070707070b0707070ba0707aaa070f0707070702aaa82ea3aaaaaaa13130a200b02c07070f0707001ca388a6a42c2c2c2c1c1d07070741c1c1c1ea81f1313132170a00b02c0707170070701c170701c8805c04c1705c070707070781c1c1c1e80c0c00c030380e0380e03a0303a03031302c0700c0f0f00303003206c2c2c6c1c1c1c1cec8ced3b233b40e80c1f13131305c0b01c070ecec9c9c0ec9c3b003200001c2c1c6c20380e581c8c8c1c1c1c1c1c1c1cbcdc1c1c1c1c0d40c1c3c1c0728c4c7c04c4c4c1b1b2307507070741c1c0c0c0c0c7c4c4c4c4c1cbd8c070712709c1f13 25 33554431 10 1023
def hc_66_22 : Nat → Nat := unpackHintV5 0xf9996ef00266e4aad6db6a50d4c9a8cc3a24c3523abb79f6b1ba70a9aa04a411669cd9ce9689948e4a1085025279eac670ea406a9994620a2459c21250426048b1e439e3b433f97a2ec14e2ca0882599c21d12221711800ff1c807aa120001ea 0x70f070faa0ba80eaaa07a8eaaa331f1f0f07070fa884e2a8cccc3c1c1c3ea69aa1f1f33330f07070fa8a2a87c7c0c0d40d030307070707070707070707070780e03a0303a030380e031b0b0b1b1f131f07c4c7c0707070703a031b1b40d1b1b1b1b0741d036a47d1f45d0b48c9d08c8d01d0740d91f47d4ad48d030303070707070707a07070781c1e030380c0e80c0e80c0e070380c0c6c2c2c6c6c4c6c1b131b01c1c1c1c0e80c6c2c2c6c6c6c6d1b1b41c1c1c1c0e80c7c7c7c7c5c2c2c5c6c6c5c1b271701c1c1c1c0e80c7c5c7c5cac5cac5c1c1c1c1e0380e0380c8c6cdc2c8c2cdc6c1d07a940c0d640c0c7c7c7c7c1c1c1c1c0e80c7c4c7c1f131f08d2341d07070740c0d9030303031f47d2b4ad0741d0364ac9d08c9d07d1f5541c1c1c1e0380e603231b170b170b231b450707003030451f05c0701c03207c4c07c4c155555523451149c44445110340c0015a31441c1c1c1e0380e0380c9c6c5c2c5c2c9c6c1c07a800c0c200c0c7c1701c0700c81f1301f13045d0741d03649d49c9d447c1705c9c0701c1c1c0303200c0c0c0c1f007d27101c1c1c1e0380e07a8e80c0c0c0c0c0c2c0c0ea0303031f1f1f1f0707070703a0303030300c4c0c0707070703a0303030340c0d1f1f1f1f0707070703a0303030300c0c1f1f1f1f07070707a59a0707070707070707aaaaaaaa1b0b0b1b070707071f131f07c4c7caa1b1b646c1d0746c6c6e647d1f1f1f45d0b41d0748c9d08c8d2647d1f5541c1c1c1c1c1ea0707030307030707aaaaa81eaaa86c2c7c2c6c6c1c1c1c1c6c4c6c1b131b2a86c2c2c6c1c1c1c1c6c6c6d1b1b6a87c7c7c7c5c2c2c5c1c1c1c1c6c6c5c1b27172a87c5c7c5c5c5ccc6c8c2d2c2c8c6c1c1c1c1c0c0d41c0c1daaa5a9aa1f1f1f1f1f131f07c4c7c07070707aa2348da81d07070766a47c7d1f47ccd48c9d0bc9d01d076647d1f5548c6c5c2c5c2c8c6c1c1c1c1c1c1c152aa8152987c1707c4c07c4c01c07221552355554547c445050444400514271b170b170b271b07070707030300703072aa82a2a87c1707c4c07c4c01c07220cd1749c9d49d41d0766447c1705ca81c07070722a01f007d12a0ba81c1c1c1e80eaaaaa81ea31f1f1f1f84e2a01c1c1c1ea8ccce9a907070707aa1f1f1f1f3333a2a01c1c1c1ea87c7c7c7e0381c2c1c3ea81e030303030b03a03a86c2c2c6ea83c1c1c3c0c0c0c0c6c2c2c6ea83c1c1c3c0c0c0c0c7cdc7c5c2c2c5ea83c1c1c3c0c0c0c0c7c5cac5cac5cac5c0c0d40d0303070b070f07070f0f07070f0f80e03a0303a030380e031b0b0b1b23131f08c4c7c0f07070f03a031b1b40d1b1b1b1b0f41d03647d2345d0b48c9d08c8d03d0740d91f4bd55030303070b0f070f0f07070f81c1ea030380c0e80c0e80c0e0380c6c6c2c2c6c6c4c6c1b131b03c1c1c3c0e80c6c6c2c2c6c6c6c6d1b1b43c1c1c3c0e80c7cdc7c5c6c2c2c5c6c6c5c1b271703c1c1c3c0e80c7c5c5cdc5c5c1c3c1c3e0380e0380c8c6cdc2c8c2cdc6e941d0f80c0d640c0c7cdc7c3c1c1c3c0e80cbc4c7c23131f08d2343c3d0743c0c0d9030303031f48d4dd0f41d0364bc9d08c9d07d2f5541c3c1c3e0380e039231b170b170b231b0f0f04503030452f05c0f01c03208c4c08c4c12355555548d144527111114140014501c3c1c3e0380e0380c9c6c5c2c5c2c9c6e801c0f80c0c200c0cfc1703c0700c8271302713045d0f41d03649d49c9d44fc1705c9c0f0f01c0f0303200c0c0c0c0fc27112701c3c1c3e0380c0e80c0e07a8c0c0c0c0c2c0c0ea0303031f1f0f07070f03a0303030300c4c0c0f07070f03a0303030340c0d1f1f0f07070f03a0303030300c0c1f1f0303003030301c1e81c1c3e070b070fa0303a030386c0e030380e03030300b0b00302c2c2c0f01c0320ec8cdd3b233746c2c2c6c3c1c1c3c0e80c13130ec9c0ec9c05c0b03c0700c8003720c0070f070f80e031b0b0b1b131313132f3713232313131396035030b28c2c0b0b13131304c7c02c2c4c4d44c8c8d0f0f030303031313130ac2709c2f2f001c2c1c3c1c1c3c3c1c1c3c3e1b0380c0e80c0e80c0e80c0e07a8c0c6c0c6c0c0c0c2c0c2c0c0c0c4c0c4c0c0c0c0c0c4c0c0c0c0c0ea03030302ca30b0b00b0b0b0f01c03200c0c00c4c06c2c2c6c4c4c4d131343c1c1c3c0e80c0c0c0d03034131305c0b04c4c04cac03c0700c803030033f00037010b1b070f0f0f1f071f1b50f0707070f0f2b23233b80e031302c0f0f00f131306c6c4c4c3c7c3d1344c4cac2303c2f042c6c7c8c7cee0303032388c6d40ea0f03070303031302c0304c1b1b131303230344d13132f08c030bc1b51b0781e80e031304c1340d13132709c14070f070f1b0380e0380c1ea31b031b030b030b036b03030303230323030303a03030b02c0304c1b1b13130303503232344c4c9c2700c3f0142d1b06c2c2c6c7c1c8c3c7c1c3c6c2c2c6cce23032380ccc7c7c4c0b04c2c02c2c04c1304c1306c6d0b46c4c4c4c8d1f48d23444c4c4c1702c2f2702327007c0cc00441717000170b0b171f07230f1f07230f170b0b172388c0c8e23032b1f1f2b00000000001548d5555000000000000000000000170b0b171f07270f1f07270f170b0b172789c0c9e27032b1f1f2b00000000001742d275272752b47d4ad0005c00130270000270000009c006c2c2c6c4c1c4c3c4c1c4c3c6c2c2c6c4e13031384c0ccc7c7c0b28c2c2c02c2c2c4c1304c1306c2c2c6c4c4c4d131347c7ccccc131305c0b04c4c04c01f033000282281c2c1c2c1c1c2c0c1c1c0c0eaaaaaaa82c2c80b13130a00f01c880b0b0b0b3b23374ec8cdd0f07070faa04c4c0b02c17170171700f01c88001705c 24 16777215 10 1023
def hc_66_23 : Nat → Nat := unpackHintV5 0xed92e8e7598edd4a84d70192cd5a6ac2baa8bb29e4b5816aae69c6a891769f924095ea6a8df9fc8769a47e8a387be8a87549a86b6a78608ab859d1ae5718ae4bbad842026e3b899e36913e2d4a522571f61c7a3e141a180c69ec06f95c0001be 0x7070b07070707070707070b07a3070781c0c1e0707030b0b0b0b0707070707130701c1c1c0b0b0b0b070707071f1f1f1f070741c1c1d0b0b0b0b070707071f1f1f1f07170701c1c1c0b0b0b0b070707071717171717171717171717170742c6c2d070f80c0c0c8e231b5030f503a80c0cbc7c8c7c0c1306c6c3c3c3c3c0e88c8c0e5030f0f4bc8cad2340c2b0ac8c1c2c1c3c1c1d42d1b070b0b50743c2c6c2c2c6c3c1c1c3cce23032380c6c2c2c6c3c1c1c3cbc4c7c23131f07ccc7c6c6d0b46c3c3d0743c3c3c3c8d33233347d2345d0b43d074bc9d08c9d13347d2f5541c2c1d17170450f0f045170b0b170f07070f2388c0c8e23031702c0f01c23130231302f0ac555548d5514444450504400514070b070f070700b05c1c2c2c01c0f0b170b0b170f07070f2789c0c9e27031702c0f01c27130271303f0ac1742d0f41d275272754ad13f05c5c0b05c3c3c0703c3c3c3c5c171727005c27105d2701c1c2c2c1c2c1e8c1c1c1c2c2c2c6c2c2c6c3c1c1c3c3e0f030f83c0c6c2c2c6c3c1c1c3c3c3c3c0f130f07ccc7c6c2c2c6c3c1c1c3c3c3c3d0f0f4cccc7c7c5c2c2c5c3c1c1c3c3c3c3c0f0f05ccc5c7c5c5c5c5c0c0d42d1b031b0b0b1b4f07230f23074f0faaa9a5aa1b0b0b1b2f132308c4cbc2f2faa1b1b42d1ba88d2366a48d2345d0b4bc9d08c9d163664bd2f5545c5c1145c2c2c5c8c1c8c3c8c1c8c3da95282a85c0b08c4c08c4c0ac2f2215523555954548c445050444400514030300b05c0c5c2c2c5c9c1c9c3c9c1c9c3eaaa282a85c0b09c4c09c4c0ac3f2205d0b49d49c9d4ad6644fc171702c17a85c1722a00105d2720386c2c2c6ea0f81ea0ba8eaaaaa86c2c2c6ea21384343aa1b0b0b1ba9a6a90d0c5c2c2c5ea281717aa43171717170b0b0b0b80e0380e030b42ea5230f33072307330f03035903030b0b0b0b2f2f03a032f132308c4cbc0b42c2c2d2348d0303640c0c0c0c8d2342d0b45d1740d917174171741745d550b0b0b0b82ea3a030380e03a80c3c0c0c0c1c0c0c0c0c0c2c2c2c2d0d0c0e80c0c0c0c03130302c2c2c2c0e80c0c0c0d030350d0c2c2c2c2c5c5c5c5c0e80c0c0c0c03170305c5c5c5c5c5c5c5c0c0d42c0c2d2307370f3707230f0b0b0b0ba5a9aaaa23132f0bc4c8c0b0b0b0b2f2faaa82d0b0b0b48d2366a48d2345c5d05c5d02d0b45d176645d17545d45e80e07aa83c2c2c2c2eaaa82ea3aa84e2a02c2c2c2d0d0eaa9a90b0b0b0baa434385e2a02c2c2c2c5c5c5c5ea85c5c5c5c5c5c5c5c6c2c2c6e0380e0380e942d1b88c3cdc1c8c1cdc3c0c0d640c0c6c2c2c6cbcbc0e80cbc4c8c23132f06c6d0b46c8d2340c0d9030303032348d1742d58d0364bc9d08c9d0bd2f5545c2c2c5e0380e0380c0000015555540000000000005c2c2c5e03980e031717045230f23072307230f03030451702c2b0bc03208c4c08c4c155555523451142c44445110340c0015a31445c2c2c5e0380e0380e802c1789c3c9c1c9c1c9c3c0c0c200c0c5c0b0ac3f00c827130271301742d2b503649d49c9d44fc171702c2c2c17172705c5c9c1703032a00c0c0c0c2705c2705d2705d2705c1c1c1c1e0380e0380e0b0b1b070727a30707070703a03071b0701c2c1c1c1c1c1c0c0e280c0c1c3c1c6c2c2c6c1c1c1c1c0e80c7c7c7c7c1c1c1c07130706c2c2c6c1c1c1c1c0e80c9c9c9c9c1c1c1d072b0747c7c7c7c1c2c1c3e0380e0380e0b0b1b0f07070303a03130b0b130f07070f03a030713131313131b0b0b1b0f07070f03a0327272727131313131b51b0f50f035030749c9c4c1302c2c3c3e89c9c3c3c1c2c1c3e0380e0380e0b0b1b0f0f0707070727a303a030f1b0b02c2c3c3c3c3c3c0c0e280c0c1c1c1c6c2c2c6c3c1c1c3c0e80c9c7c7c9c7c7c3c3c3c3c3f0f0f130f06c2c2c6c3c1c1c3c0e80c9c9c9c9c3c3c3d0f0f47cecec7c6c2c2c6e0380e0380e50b0b1b27272727036031b1b40b0b1b1b2b0f5f076f072b0f03034a0303546c2c2c6cacfcfcac0e80c9c9c9c9cfc4cfc3f133f06d0b4ad5f40d949da3272752727273f4fd1b0b0b1b80e60380e549c9c9c9c0d51b0b0b1b2b3f3f2b03a03272727275555555549d275546d10b543d507540d19527515134546c2c2c6e0380e0380e0b0b1b272703a031b0b0b1b3f3f03a033f27273f1b0b0b1b03a0327273f3f1b0b0b1ba030382ea380e0303a80c3c0c0c0c1c0c0c0c0c0c6c2c2c6d0d0c0e80c0c0c0c03130306c2c2c6c0e80c0c0c0d030350d0c5c2c2c5c5c5c0e80c0c0c0c0c03030310c5c5c5c5e96681c2c1c3c1c1c3c3c1c1c3c3eaaaaaaa86c2c2c6c8c4c7c23131f03c1c1c3ea86c6d91b1b1b1b0f41c1c1d991f48d1742d23274232340f41d991f4bd55a81c2c3c1c3c3c1c1c3c0c1c1c0c0eaaaaaaaa86c2c2c6c6c4c6c1b131b03c1c1c3ea86c2c2c6c6c6c6d1b1b43c1c1c3ea87c7c5c2c2c5c6c6c5c1b271703c1c1c3ea87c5c5c5c5c1c2c1c3ea82e80ea80c0c0c0c1c0e80c6c2c2c6c3c1c1c3ea80c0c0c0c6c2c2c6c3c1c1c3ea80c0c0c0c7cecec7c5c2c2c5c3c1c1c3ea80c0c0c0c0c0c7c5cec5c5c5c1c3c1c3c8c6d3c2c8c2ccc6c0c0d41d0f03aaaaa9a5331f1f0f07070f2f131f08c4c7caa2348d0f0f41d0faa6a47d234cd43d074bc9d08c9d2647d2f5541c3c1c3c8c6c5c2c5c2c8c6c3c3c116a9a95280bc1703c0708c4c08c4c221555523554511111414110014501c3c1c3c9c6c5c2c5c2c9c6c0c0c01c0f03aaaaa8a03305c0f01c2713027130883345d0f41d275272759913f05c1703c3c0703ea8a80044 24 16777215 10 1023
def hc_66_24 : Nat → Nat := unpackHintV5 0x48228483134cdf89a96616422b2842fa57048c5a0558f00002ac 0xf0f50b46c3c1c1c1c1c1c1c1d070751b0b0b1b3388c0c8e4b03070707071b0b0b1b1f131f07c4c7c070707071f1f1f1f1b1b42d1b0707070741c1c1d2348d1f47d1742d2f274232740741d4cd1f47d55171704541c1c1d501c1c05c2c2c5c8e23032388c0c1c1c1c1c5c0b07c4c07c4c01c0707c1f155235075555151f11141411110014503c3c02c170f0707070707070701c1c05c2c2c5c9e27032789c0c1c1c1c1c5c0b07c4c07c4c01c0707c1f05d0b49d49c9d41d0752b447c171702c170707070701c1c1c1705c5c9c07c01741749c070f07070b07a3070707070707071b0b0b1b0781c0c1e0703070707071b0b0b1b07070701c4c1c070707071f1f1f1f1b0b0b1b07070741c1d0707070733331f1f1f1f170b0b1707070701c1c070707071733171f171f171717070b070b0b42c1c1c1d43c3d41d0f0f0b0b0b0b0f07070f3788c0c8e37030b0b0b0b0f07070f2f131f08c4c7c371f1f0b42c2c2d0f0f41d0f0b0b0b2348d1f48d0b42d0f41d17174171741745d1745d55070b07a307070b0b0707070b0f0b0b0b0b0b0f07070f0b82c0c2e0b030b0b0b0b0f07070f0b0b0b02c4c2c1f1f0b0b0b0b0f07070f0b0b0b42c2d1f1f0b0b0b0b0f07070f0b0b0b02c5c2c171717171717171717171717aaaa07070707aa0b0b0b0b07070707aa0b0b0b0b070707071f1f1f1faa0b0b0b0b0707070717171717171717170707070703030303030303030b0b0b0b07070707030303030b0b0b0b07070707030303031f1f1f1f0b0b0b0b070707070303030317171717171717170b0b50b0b0b41c1d41c1c1d07070707238dc0cde23030b0b0b0b070707071f131f07c4c7c0b0b0b0b070707071f1f1f1f0707070b42c2c2d0741c1c1d2348d1f1f47d1f17174171740b42d0741d1745d1745d517517 23 8388607 10 1023
def nh_66 : Nat → Nat := fun p => Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_66_24 (Nat.sub p 768)) (hc_66_23 (Nat.sub p 736)) (Nat.blt p 768)) (Bool.rec (hc_66_22 (Nat.sub p 704)) (hc_66_21 (Nat.sub p 672)) (Nat.blt p 704)) (Nat.blt p 736)) (Bool.rec (Bool.rec (hc_66_20 (Nat.sub p 640)) (hc_66_19 (Nat.sub p 608)) (Nat.blt p 640)) (hc_66_18 (Nat.sub p 576)) (Nat.blt p 608)) (Nat.blt p 672)) (Bool.rec (Bool.rec (Bool.rec (hc_66_17 (Nat.sub p 544)) (hc_66_16 (Nat.sub p 512)) (Nat.blt p 544)) (hc_66_15 (Nat.sub p 480)) (Nat.blt p 512)) (Bool.rec (Bool.rec (hc_66_14 (Nat.sub p 448)) (hc_66_13 (Nat.sub p 416)) (Nat.blt p 448)) (hc_66_12 (Nat.sub p 384)) (Nat.blt p 416)) (Nat.blt p 480)) (Nat.blt p 576)) (Bool.rec (Bool.rec (Bool.rec (Bool.rec (hc_66_11 (Nat.sub p 352)) (hc_66_10 (Nat.sub p 320)) (Nat.blt p 352)) (hc_66_9 (Nat.sub p 288)) (Nat.blt p 320)) (Bool.rec (Bool.rec (hc_66_8 (Nat.sub p 256)) (hc_66_7 (Nat.sub p 224)) (Nat.blt p 256)) (hc_66_6 (Nat.sub p 192)) (Nat.blt p 224)) (Nat.blt p 288)) (Bool.rec (Bool.rec (Bool.rec (hc_66_5 (Nat.sub p 160)) (hc_66_4 (Nat.sub p 128)) (Nat.blt p 160)) (hc_66_3 (Nat.sub p 96)) (Nat.blt p 128)) (Bool.rec (Bool.rec (hc_66_2 (Nat.sub p 64)) (hc_66_1 (Nat.sub p 32)) (Nat.blt p 64)) (hc_66_0 p) (Nat.blt p 32)) (Nat.blt p 96)) (Nat.blt p 192)) (Nat.blt p 384)
def f_66 : Nat → Nat × Nat := unpackForestF 0xc14aae0c577050aa00c5fc0ca280316eff6d97fb60bfcb680315efd6877d145beca6df4114018a77b155bdcaedec154016bf7a135005adde45b4016af73135b981c5dc4f6e606b73a4bba8925d4096e74877382fb9c11dcc0d0016a772155b7e375bed8adf28b7014db7c22802d3edd2ab6cb6eb649adb44f6d906a00b4bb5ca2da758ad32bb6a155b4c2e802d1ecc8dd68155b31b75984d6cd27b66035005a1d92d92c926b60b43b1229d88d4ec56d962343b04aad84576c10aa00a5fafa3e57c516b869f5db7caedb6570d0eb969f5c16d0052bd6c596ae6df5a135ab9b5d645f6ae6cf57935abc1a55cd8c0149f56145a06b15535a2a92cb40b6fa9c9ad02daea429f52143a8ab85445f6816cf4eb6ca749ad3c9429d06940b63a5db7d2edae976cf4c034a5db1d02576946c74a155a042ed0717e838af41a5fa0d2dd0695e8d4a941a53a0d25d0691e876d744034a1db1d0612e844d742263a0c23d02172810a000a479fdaa4eb5ae7c6a93e1559d6b1cf4556756dd3c5639d49acec4f67506a00a3f9ca2c4e45566aad737d699bc9acd518a6dad73514d9aca2cd41340146f2ac5b9562bccad926506b2ab4b989b24c40d6556872aa5795527cb75a25b2b92d85d96c2e4aa91e586c92c0359551fcaa15e550aa0095f94caa48517e512892145b93cb648515e4c4892614490a29c84d7e47ce12396c91c36484d5e452892134f90cae484d1c012b72047c8b5a7c7cdf22d6971e5708b5a3c70df2386d91c1348b5a1c5a93e3469f1a3438cab84641722d48f1837c8b51fc5d1c22d46e009578aca242d16e292890b453859afc469b2232d91205488c3642cd5e212890b34f858b743ad2e1d6870b01885da5c2ed0e1749f0ba4785d1fc2c050012a6fdc6e84e323f6dbdfb6d70847c7edb3c1ad520d068fdb6382e323f69be088f90417c7ed33c0adfa056a8fda3f8063940316201298fda377ecb7bfd1b1fb2cefe3637ec2280253df92c8f846f7c235bec5f1f08cef92447c8a23e4111f08c6f816e004a5bbd589ecad0f6065779b7bbcdade9ae0ef367791b63c84d1e406af2034779b1bbc5bde1ac0ef16777db1bbc1740128eee16470a37b851add92f8e1467758a23ac111c28c6ea164709b7ba29f1d12f8e136773ca2384d3dcd288e55727292e394571c268ee116e70dafb86d6dc36aee203470da9b844d001286dfb646fc32b475bdbd6a8d1d6b6edbe34759db86a8dc05568eb1b46db9b46c8da06568d37b64df1a34ced1a5f6b1b63585b1ac0dad606c68d2bb465bda96d8d196769dbf34657da32aed256f68c1a8024fda12a8cbd6b67cbe32f59d9d2f8cbb6765dafb325b1990d8cbb5765cb70024ed958b0c256b64e3830959d91068c246263e3830899d844bec5c6062c3630895d898c0c216761e3930857d842aec204d0049bb0459170adec01545c2b5afc5f170acebe1545c2b1af4591706debc17c5c1b3ae0d7d734d8b996c5cc362e0d5d718cab816e00499adc5515aad6b5a545acaa2b558d692c8ad46f56a35acc5f15a8ceb1244588a22c41115a8c6afd7e57caa2b517d5c488ae14456a29ab45b801256ac3584deb5aaad61552a89bd6354db426f1bd378d6a83704de33a98d214c288a60444de31a935f9496b09bc5f512bf2891f944690a21444de29a855a5376c49b96f4fdb026e59d372be9e47e4dca7a755c93728e9c4634dc1e80249d276969a13549da1a4e93d312ba93a474bc9aa4e8fd2729e939474ad2ba4e4fd296909445349c9380217d250a88e45f488a22441111c8b69006c4722ba3a5111d0888e4530042da331f11928a76b4f45dbe1dad2d14ae08a15d3b5a3a22df1116d876b433b527a1ad0d0d29e85d7042cae9da91d096f876a3f41a3820c534ed46e8034f401a3a0093d0048e802373b4b69fb1f0fd2f87694f3eeb81da51cf56f87be803ddc61ea95cf52f87693f3ce381da4dcf16b07745f3b9b81dc5f0ed24e008573ac221d116ce908874453004299cc554bc8dc71c6438cb2978dbce06a8701352f1b19bb190dd2ca5e26f365bf1b2d50d926a5e23f356391ab160d529a5e23734a321a48fcbc2de64563321b799cdb0c86c66435f321a99909bcc847e642372f0a298adf8c56a85e13f30a39185160bc26e5ed7e2f5b917ad60bd2a85e1270042780212cb928a555622deb4154dbcb56d8553632ceb41545bcaf6de57b632bcb7154574ad6d85513f2ae301544dc0108e540340042194ad90a52ca42d6f289aa14455485ac650155215b713ad909d2ca42a6f2152f932db0992da42a57255b212a97c954ae4296f249bf124d50852be4836c214ab9155bc8aac64526f2292f91495c8526a4347e219a410c5108524e0083f0041d9044d46d8c436a5f1fa300fc5b46d4ae3dc721ee2c0da57c798c0369571d92f8ec95c6d29a39d721cda80da49c6d0d4385701b8238dc0f46d0cc00837004198d317c698a60082b166b18b31bc598c63257e1662f8c51f8598a630453164b78bd5f8592be2e47e164a78b55c85928e0082715cb20675bc544a82a1540ceb18a2990512c819c6f13ca206718c4bafc25c7212caa06717c4928819c5b11b3908c5b0338ae21a4410ca206714c412c819b6f0cdaf8759c83d8f81d4730edb18745b0336ae1c1440cda786b5c8352b819b470ccb700207c310a814c5f0bc2205316c2d0d814c570a8a2054110298a60081b032b784c5500cac6121640323781918c20afc104720322f81916c1dce40645706a3f0345100c8a60c453031b7818d7c13ce40a47c04e39818d5c118fc0634f03eb9018d1c0c4dc060660040b814150028be0394401c2200516c050d80145700c2200514c010260003f 10 11
def ch_66 : Nat → Bool := dagCheckNodeV5 fullMask g_66 ep_66 6 63 bds_66 776 (dagTraceF fullMask rootStock 11 f_66) cur_66 nh_66
set_option maxHeartbeats 0 in
theorem rc_66 : dagCheckRootsV5 fullMask g_66 ep_66 6 63 776 bds_66 (dagTraceF fullMask rootStock 11 f_66) (cur_66 0) (nh_66 0) rootStock 11 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_0 : treeBlockF 0 32 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_1 : treeBlockF 32 64 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_2 : treeBlockF 64 96 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_3 : treeBlockF 96 128 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_4 : treeBlockF 128 160 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_5 : treeBlockF 160 192 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_6 : treeBlockF 192 224 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_7 : treeBlockF 224 256 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_8 : treeBlockF 256 288 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_9 : treeBlockF 288 320 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_10 : treeBlockF 320 352 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_11 : treeBlockF 352 384 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_12 : treeBlockF 384 416 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_13 : treeBlockF 416 448 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_14 : treeBlockF 448 480 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_15 : treeBlockF 480 512 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_16 : treeBlockF 512 544 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_17 : treeBlockF 544 576 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_18 : treeBlockF 576 608 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_19 : treeBlockF 608 640 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_20 : treeBlockF 640 672 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_21 : treeBlockF 672 704 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_22 : treeBlockF 704 736 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_23 : treeBlockF 736 768 ch_66 = true := by decide +kernel
set_option maxHeartbeats 0 in
theorem nb_66_24 : treeBlockF 768 776 ch_66 = true := by decide +kernel
theorem nj_66_1 : ∀ i, 0 ≤ i → i < 64 → ch_66 i = true := block_join (fun _ h1 h2 => treeBlockF_at nb_66_0 h1 h2) (fun _ h1 h2 => treeBlockF_at nb_66_1 h1 h2)
theorem nj_66_2 : ∀ i, 0 ≤ i → i < 96 → ch_66 i = true := block_join nj_66_1 (fun _ h1 h2 => treeBlockF_at nb_66_2 h1 h2)
theorem nj_66_3 : ∀ i, 0 ≤ i → i < 128 → ch_66 i = true := block_join nj_66_2 (fun _ h1 h2 => treeBlockF_at nb_66_3 h1 h2)
theorem nj_66_4 : ∀ i, 0 ≤ i → i < 160 → ch_66 i = true := block_join nj_66_3 (fun _ h1 h2 => treeBlockF_at nb_66_4 h1 h2)
theorem nj_66_5 : ∀ i, 0 ≤ i → i < 192 → ch_66 i = true := block_join nj_66_4 (fun _ h1 h2 => treeBlockF_at nb_66_5 h1 h2)
theorem nj_66_6 : ∀ i, 0 ≤ i → i < 224 → ch_66 i = true := block_join nj_66_5 (fun _ h1 h2 => treeBlockF_at nb_66_6 h1 h2)
theorem nj_66_7 : ∀ i, 0 ≤ i → i < 256 → ch_66 i = true := block_join nj_66_6 (fun _ h1 h2 => treeBlockF_at nb_66_7 h1 h2)
theorem nj_66_8 : ∀ i, 0 ≤ i → i < 288 → ch_66 i = true := block_join nj_66_7 (fun _ h1 h2 => treeBlockF_at nb_66_8 h1 h2)
theorem nj_66_9 : ∀ i, 0 ≤ i → i < 320 → ch_66 i = true := block_join nj_66_8 (fun _ h1 h2 => treeBlockF_at nb_66_9 h1 h2)
theorem nj_66_10 : ∀ i, 0 ≤ i → i < 352 → ch_66 i = true := block_join nj_66_9 (fun _ h1 h2 => treeBlockF_at nb_66_10 h1 h2)
theorem nj_66_11 : ∀ i, 0 ≤ i → i < 384 → ch_66 i = true := block_join nj_66_10 (fun _ h1 h2 => treeBlockF_at nb_66_11 h1 h2)
theorem nj_66_12 : ∀ i, 0 ≤ i → i < 416 → ch_66 i = true := block_join nj_66_11 (fun _ h1 h2 => treeBlockF_at nb_66_12 h1 h2)
theorem nj_66_13 : ∀ i, 0 ≤ i → i < 448 → ch_66 i = true := block_join nj_66_12 (fun _ h1 h2 => treeBlockF_at nb_66_13 h1 h2)
theorem nj_66_14 : ∀ i, 0 ≤ i → i < 480 → ch_66 i = true := block_join nj_66_13 (fun _ h1 h2 => treeBlockF_at nb_66_14 h1 h2)
theorem nj_66_15 : ∀ i, 0 ≤ i → i < 512 → ch_66 i = true := block_join nj_66_14 (fun _ h1 h2 => treeBlockF_at nb_66_15 h1 h2)
theorem nj_66_16 : ∀ i, 0 ≤ i → i < 544 → ch_66 i = true := block_join nj_66_15 (fun _ h1 h2 => treeBlockF_at nb_66_16 h1 h2)
theorem nj_66_17 : ∀ i, 0 ≤ i → i < 576 → ch_66 i = true := block_join nj_66_16 (fun _ h1 h2 => treeBlockF_at nb_66_17 h1 h2)
theorem nj_66_18 : ∀ i, 0 ≤ i → i < 608 → ch_66 i = true := block_join nj_66_17 (fun _ h1 h2 => treeBlockF_at nb_66_18 h1 h2)
theorem nj_66_19 : ∀ i, 0 ≤ i → i < 640 → ch_66 i = true := block_join nj_66_18 (fun _ h1 h2 => treeBlockF_at nb_66_19 h1 h2)
theorem nj_66_20 : ∀ i, 0 ≤ i → i < 672 → ch_66 i = true := block_join nj_66_19 (fun _ h1 h2 => treeBlockF_at nb_66_20 h1 h2)
theorem nj_66_21 : ∀ i, 0 ≤ i → i < 704 → ch_66 i = true := block_join nj_66_20 (fun _ h1 h2 => treeBlockF_at nb_66_21 h1 h2)
theorem nj_66_22 : ∀ i, 0 ≤ i → i < 736 → ch_66 i = true := block_join nj_66_21 (fun _ h1 h2 => treeBlockF_at nb_66_22 h1 h2)
theorem nj_66_23 : ∀ i, 0 ≤ i → i < 768 → ch_66 i = true := block_join nj_66_22 (fun _ h1 h2 => treeBlockF_at nb_66_23 h1 h2)
theorem nj_66_24 : ∀ i, 0 ≤ i → i < 776 → ch_66 i = true := block_join nj_66_23 (fun _ h1 h2 => treeBlockF_at nb_66_24 h1 h2)
theorem nc_66 : ∀ i, 0 ≤ i → i < 776 → ch_66 i = true := nj_66_24
theorem lb_66 : LowerBin fullMask rootStock g_66 12 :=
  lowerDagV5 (kn_cons lb_20 (kn_cons lb_21 (kn_cons lb_63 (kn_cons lb_59 (kn_cons lb_60 (kn_cons lb_57 (kn_cons lb_61 (kn_cons lb_62 (kn_cons lb_28 (kn_cons lb_56 (kn_cons lb_38 (kn_cons lb_65 (kn_cons lb_64 (kn_cons lb_13 (kn_cons lb_14 (kn_cons lb_53 (kn_cons lb_15 (kn_cons lb_10 (kn_cons lb_43 (kn_cons lb_58 (kn_cons lb_52 (kn_cons lb_33 (kn_cons lb_49 (kn_cons lb_26 (kn_cons lb_7 (kn_cons lb_12 (kn_cons lb_36 (kn_cons lb_18 (kn_cons lb_11 (kn_cons lb_32 (kn_cons lb_23 (kn_cons lb_46 (kn_cons lb_0 (kn_cons lb_2 (kn_cons lb_50 (kn_cons lb_1 (kn_cons lb_16 (kn_cons lb_8 (kn_cons lb_6 (kn_cons lb_39 (kn_cons lb_17 (kn_cons lb_51 (kn_cons lb_42 (kn_nil)))))))))))))))))))))))))))))))))))))))))))) rc_66 nc_66 (by decide +kernel)

def wg : List Gate := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.or, [16, 17]⟩]
theorem wfits : Monotone2 ⟨wg, 18⟩ := by
  intro g hg; simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem weval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970484224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel
theorem root_lb : LowerBin fullMask rootStock (canon fullMask (4276676776 * 2 ^ 32 + 3970484224)) (13 - 1) := by
  rw [show canon fullMask (4276676776 * 2 ^ 32 + 3970484224) = g_66 by decide]
  exact lb_66

end PEqualNP.Outside.L_meta_48681

theorem PEqualNP.Outside.L_meta_48681 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676776 * 2 ^ 32 + 3970484224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676776 * 2 ^ 32 + 3970484224) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_48681.table2_from_lowerBin (4276676776 * 2 ^ 32 + 3970484224) 13 PEqualNP.Outside.L_meta_48681.root_lb PEqualNP.Outside.L_meta_48681.wg 18 rfl PEqualNP.Outside.L_meta_48681.wfits PEqualNP.Outside.L_meta_48681.weval
