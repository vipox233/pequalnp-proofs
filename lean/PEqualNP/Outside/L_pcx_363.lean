import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_363

abbrev Role := Fin 4 × Bool
abbrev Inc := Bool × Fin 9 × Bool

def ends (j : Fin 9) (b : Bool) : Role :=
  let table : Fin 9 → Fin 2 → Role :=
  ![![((0,true) : Role),(1,true)],![(1,true),(2,true)],![(2,true),(0,true)],
    ![(0,false),(2,false)],![(2,false),(3,false)],![(3,false),(0,false)],
    ![(1,false),(2,false)],![(2,false),(3,false)],![(3,false),(1,false)]]
  table j (if b then 1 else 0)

def localPin (r : Inc) : Role :=
  let p := ends r.2.1 r.2.2
  (p.1, if r.1 then !p.2 else p.2)

def turn (r : Inc) : Inc := (r.1, r.2.1, if r.1 then r.2.2 else !r.2.2)

theorem turn_inv : Function.Involutive turn := by
  rintro ⟨b,j,t⟩
  cases b <;> simp [turn]

def loc (h : Role → Bool) : ℕ :=
  (Finset.univ.filter fun r : Inc => h (localPin r) ≠ h (localPin (turn r))).card

def evalRole (A B Z : Bool) (p : Role) : Bool :=
  let t := ![A,B,Z,false] p.1
  if p.2 then !t else t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_le : ∀ h : Role → Bool, loc h ≤ 12 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem loc_top : ∀ A B Z : Bool, loc (evalRole A B Z) = 12 ↔ Z = !(A && B) := by decide +kernel

def pairCost (h : Bool → Bool) : ℕ :=
  (Finset.univ.filter fun t : Bool => h t ≠ h (!t)).card

theorem pair_le : ∀ h, pairCost h ≤ 2 := by decide +kernel

theorem pair_top : ∀ h, pairCost h = 2 ↔ h true = !(h false) := by decide +kernel

theorem cyc (m : ℕ) (g : Fin m → Bool) (h : ∀ i, g (finRotate m i) = g i) (i j : Fin m) :
    g i = g j := by
  cases m with
  | zero => exact i.elim0
  | succ m =>
    have : ∀ i : Fin (m+1), g i = g 0 := fun i => by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih => rw [← ih, ← h i.castSucc, finRotate_apply, Fin.coeSucc_eq_succ]
    rw [this i, this j]

theorem rot {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) :
    ∃ σ : Equiv.Perm α, (∀ a, f (σ a) = f a) ∧
      ∀ g : α → Bool, (∀ a, g (σ a) = g a) → ∀ a b, f a = f b → g a = g b := by
  classical
  let F := Equiv.sigmaFiberEquiv f
  let φ : ∀ b, {a // f a = b} ≃ Fin (Fintype.card {a // f a = b}) := fun b => Fintype.equivFin _
  let τ : ∀ b, Equiv.Perm {a // f a = b} := fun b => (φ b).trans ((finRotate _).trans (φ b).symm)
  let σ : Equiv.Perm α := F.symm.trans ((Equiv.sigmaCongrRight τ).trans F)
  have hσ : ∀ b (a : {a // f a = b}), σ a.1 = (τ b a).1 := by
    rintro b ⟨a, rfl⟩
    rfl
  refine ⟨σ, fun a => ?_, fun g hg a b hab => ?_⟩
  · rw [hσ (f a) ⟨a, rfl⟩]
    exact (τ (f a) ⟨a, rfl⟩).2
  · have := cyc _ (fun i => g ((φ (f b)).symm i).1) (fun i => by
      have := hg ((φ (f b)).symm i).1
      rw [hσ (f b)] at this
      simpa [τ] using this) (φ (f b) ⟨a, hab⟩) (φ (f b) ⟨b, rfl⟩)
    simpa using this


abbrev Key (v : ℕ) := Option (Fin v)
abbrev Wire (v : ℕ) := Key v × Bool
abbrev Slot (v g : ℕ) := Wire v ⊕ (Fin g × Inc)

variable {v g : ℕ}

def nameAt (a b z : Fin g → Fin v) (j : Fin g) : Fin 4 → Key v :=
  ![some (a j), some (b j), some (z j), none]

def keyAt (a b z : Fin g → Fin v) : Slot v g → Wire v
  | .inl w => w
  | .inr (j,r) => (nameAt a b z j (localPin r).1, (localPin r).2)

def matchEnd : Slot v g → Slot v g
  | .inl (q,b) => .inl (q,!b)
  | .inr (j,r) => .inr (j,turn r)

theorem match_inv : Function.Involutive (@matchEnd v g) := by
  rintro (⟨q,b⟩ | ⟨j,r⟩)
  · simp [matchEnd]
  · simp [matchEnd,turn_inv r]

def changeSign : Slot v g → Slot v g
  | .inl (q,b) => .inl (q,!b)
  | .inr (j,(d,k,b)) => .inr (j,(!d,k,b))

theorem sign_inv : Function.Involutive (@changeSign v g) := by
  rintro (⟨q,b⟩ | ⟨j,d,k,b⟩) <;> simp [changeSign]

theorem sign_key (a b z : Fin g → Fin v) (s : Slot v g) :
    keyAt a b z (changeSign s) = ((keyAt a b z s).1, !(keyAt a b z s).2) := by
  rcases s with ⟨q,c⟩ | ⟨j,d,k,c⟩
  · rfl
  · cases d <;> simp [keyAt, changeSign, localPin]

def gateView (a b z : Fin g → Fin v) (h : Wire v → Bool) (j : Fin g) (p : Role) :=
  h (nameAt a b z j p.1, p.2)

def score (a b z : Fin g → Fin v) (h : Wire v → Bool) :=
  (∑ q : Key v, pairCost (fun t => h (q,t))) +
    ∑ j : Fin g, loc (gateView a b z h j)

theorem cost_form (a b z : Fin g → Fin v) (h : Wire v → Bool) :
    (Finset.univ.filter (fun s : Slot v g =>
      h (keyAt a b z s) ≠ h (keyAt a b z (matchEnd s)))).card = score a b z h := by
  classical
  simp only [score, pairCost, loc, Finset.card_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  rfl

theorem cost_bound (a b z : Fin g → Fin v) (h : Wire v → Bool) :
    score a b z h ≤ 2*(v+1+6*g) ∧
    (score a b z h = 2*(v+1+6*g) ↔
      (∀ q, h (q,true) = !(h (q,false))) ∧
      (∀ j, loc (gateView a b z h j) = 12)) := by
  classical
  let p := fun q : Key v => pairCost (fun t => h (q,t))
  let s := fun j : Fin g => loc (gateView a b z h j)
  have hp : ∀ q, p q ≤ 2 := fun q => pair_le _
  have hs : ∀ j, s j ≤ 12 := fun j => loc_le _
  have cp : (∑ _ : Key v, (2:ℕ)) = 2*(v+1) := by simp [Key, Nat.mul_comm, Nat.add_comm]
  have cs : (∑ _ : Fin g, (12:ℕ)) = 12*g := by simp [Nat.mul_comm]
  have ep := Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun q _ => hp q)
  have es := Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun j _ => hs j)
  have lp := Finset.sum_le_sum (s:=Finset.univ) (fun q _ => hp q)
  have ls := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hs j)
  rw [cp] at lp ep
  rw [cs] at ls es
  change (∑ q, p q) + (∑ j, s j) ≤ _ ∧ ((∑ q, p q) + (∑ j, s j) = _ ↔ _)
  refine ⟨by omega, ?_⟩
  constructor
  · intro hh
    exact ⟨fun q => (pair_top _).1 ((ep.1 (by omega)) q (Finset.mem_univ _)),
      fun j => (es.1 (by omega)) j (Finset.mem_univ _)⟩
  · rintro ⟨h1,h2⟩
    have h3 := ep.2 (fun q _ => (pair_top _).2 (h1 q))
    have h4 := es.2 (fun j _ => h2 j)
    omega

def baseVal (x : Fin v → Bool) : Key v → Bool
  | none => false
  | some i => x i

def enc (x : Fin v → Bool) (w : Wire v) : Bool :=
  if w.2 then !(baseVal x w.1) else baseVal x w.1

theorem enc_gate (a b z : Fin g → Fin v) (x : Fin v → Bool) (j : Fin g) :
    gateView a b z (enc x) j = evalRole (x (a j)) (x (b j)) (x (z j)) := by
  funext p
  rcases p with ⟨k,t⟩
  fin_cases k <;> cases t <;> rfl

theorem enc_top (a b z : Fin g → Fin v) (x : Fin v → Bool) :
    score a b z (enc x) = 2*(v+1+6*g) ↔
      ∀ j, x (z j) = !(x (a j) && x (b j)) := by
  rw [(cost_bound a b z (enc x)).2]
  simp only [enc_gate,loc_top]
  exact and_iff_right (fun q => rfl)

theorem negate_half {A : Type} [Fintype A] (f : A → Bool) (e : Equiv.Perm A)
    (h : ∀ x, f (e x) = !(f x)) :
    2 * (Finset.univ.filter (fun x => f x = true)).card = Fintype.card A := by
  classical
  have eq : (Finset.univ.filter (fun x => f x = true)).card =
      (Finset.univ.filter (fun x => f x = false)).card := by
    apply Finset.card_equiv e
    intro x
    cases hh : f x <;> simp [h,hh]
  have add : (Finset.univ.filter (fun x => f x = true)).card +
      (Finset.univ.filter (fun x => f x = false)).card = Fintype.card A := by
    rw [Finset.card_filter,Finset.card_filter,← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : A, (1:ℕ) := Finset.sum_congr rfl (fun x _ => by cases hh : f x <;> simp [hh])
      _ = _ := by simp
  omega

end PEqualNP.Outside.L_pcx_363

open PEqualNP.Outside.L_pcx_363 in
theorem PEqualNP.Outside.L_pcx_363 : ∀ (v g : ℕ) (a b z : Fin g → Fin v),
  ∃ n : ℕ, n ≤ 2*(v+1+18*g) ∧
    let V := Bool × Fin n
    let X := V → Bool
    let T := 2*(v+1+6*g)
    ∃ (M : Fin 3 → Equiv.Perm (Fin n)) (port : (Bool × Fin v) ↪ V)
      (anchor : V),
      (∀ j, port j ≠ anchor) ∧
      let cost := fun (y : X) (j : Fin 3) =>
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,M j i))).card
      let feasible := (Finset.univ : Finset X).filter (fun y =>
        y anchor = false ∧ cost y 0 = 0 ∧ cost y 1 = 0 ∧ cost y 2 = T)
      (∀ y : X, cost y 0 = 0 → cost y 1 = 0 → cost y 2 ≤ T) ∧
      (∀ y ∈ feasible, (Finset.univ.filter (fun u : V => y u = true)).card = n ∧
        ∀ i : Fin v, y (port (true,i)) = !(y (port (false,i)))) ∧
      ∀ x : Fin v → Bool,
        (feasible.filter (fun y => ∀ i, y (port (false,i)) = x i)).card =
          if ∀ j : Fin g, x (z j) = !(x (a j) && x (b j)) then 1 else 0 := by
  classical
  intro v g a b z
  let n := Fintype.card (Slot v g)
  have sz : n = 2*(v+1+18*g) := by
    simp [n, Slot, Wire, Key, Inc, Fintype.card_sum, Fintype.card_prod]
    <;> ring
  refine ⟨n, sz.le, ?_⟩
  intro V X T
  let φ : Fin n ≃ Slot v g := (Fintype.equivFin _).symm
  let key := fun i : Fin n => keyAt a b z (φ i)
  let rep := fun w : Wire v => φ.symm (.inl w)
  have hr (w : Wire v) : key (rep w) = w := by simp [key, rep, keyAt]
  obtain ⟨σ,hσ,hcon⟩ := rot key
  let τ : Equiv.Perm (Slot v g) := Function.Involutive.toPerm matchEnd match_inv
  let M : Fin 3 → Equiv.Perm (Fin n) := ![1, σ, φ.trans (τ.trans φ.symm)]
  let port : (Bool × Fin v) ↪ V :=
    ⟨fun p => (false, rep (some p.2,p.1)), by
      rintro ⟨t,i⟩ ⟨s,j⟩ h
      have hh := congrArg (fun p : V => key p.2) h
      change key (rep (some i,t)) = key (rep (some j,s)) at hh
      rw [hr,hr] at hh
      simpa [Prod.mk.injEq, and_comm] using hh⟩
  let anchor : V := (false, rep (none,false))
  refine ⟨M,port,anchor,?_,?_⟩
  · rintro ⟨s,j⟩ h
    have hh := congrArg (fun p : V => key p.2) h
    change key (rep (some j,s)) = key (rep (none,false)) at hh
    simp [hr] at hh
  intro cost feasible
  let Y := fun (h : Wire v → Bool) (p : V) => h (key p.2)
  have Ya (h : Wire v → Bool) : Y h anchor = h (none,false) := by
    change h (key (rep _)) = _; rw [hr]
  have Yp (h : Wire v → Bool) (t : Bool) (i : Fin v) :
      Y h (port (t,i)) = h (some i,t) := by
    change h (key (rep _)) = _; rw [hr]
  have zero (h : Wire v → Bool) : cost (Y h) 0 = 0 ∧ cost (Y h) 1 = 0 := by
    constructor <;> change (Finset.univ.filter _).card = 0 <;>
      rw [Finset.card_eq_zero,Finset.filter_eq_empty_iff] <;> intro i _ <;> simp [Y,M,hσ]
  have normal (y : X) (h0 : cost y 0 = 0) (h1 : cost y 1 = 0) :
      ∃ h, y = Y h := by
    have e0 : ∀ i, y (false,i) = y (true,i) := by
      intro i
      have ht := Finset.card_eq_zero.1 h0
      rw [Finset.filter_eq_empty_iff] at ht
      simpa [M] using ht (Finset.mem_univ i)
    have e1 : ∀ i, y (false,i) = y (true,σ i) := by
      intro i
      have ht := Finset.card_eq_zero.1 h1
      rw [Finset.filter_eq_empty_iff] at ht
      simpa [M] using ht (Finset.mem_univ i)
    have hc := hcon (fun i => y (false,i)) (fun i => (e0 (σ i)).trans (e1 i).symm)
    refine ⟨fun w => y (false,rep w),?_⟩
    funext p
    obtain ⟨t,i⟩ := p
    have ht := hc i (rep (key i)) (hr _).symm
    cases t
    · exact ht
    · exact (e0 i).symm.trans ht
  have last (h : Wire v → Bool) : cost (Y h) 2 = score a b z h := by
    rw [← cost_form]
    refine Finset.card_equiv φ (fun i => ?_)
    have hh : φ (M 2 i) = matchEnd (φ i) := by simp [M,τ]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Y,key,hh]
  have memF (y : X) : y ∈ feasible ↔
      y anchor = false ∧ cost y 0 = 0 ∧ cost y 1 = 0 ∧ cost y 2 = T := by
    simp [feasible]
  have bal (h : Wire v → Bool) (hp : ∀ q, h (q,true) = !(h (q,false))) :
      (Finset.univ.filter (fun p : V => Y h p = true)).card = n := by
    let ss : Equiv.Perm (Slot v g) := Function.Involutive.toPerm changeSign sign_inv
    let flipI := φ.trans (ss.trans φ.symm)
    let E : Equiv.Perm V := Equiv.prodCongr (Equiv.refl Bool) flipI
    have hφ (i : Fin n) : φ (flipI i) = changeSign (φ i) := by simp [flipI,ss]
    have anti (w : Wire v) : h (w.1,!w.2) = !(h w) := by
      rcases w with ⟨q,t⟩
      cases t
      · exact hp q
      · simp [hp q]
    have ht := negate_half (Y h) E (by
      rintro ⟨t,i⟩
      change h (keyAt a b z (φ (flipI i))) = !(h (keyAt a b z (φ i)))
      rw [hφ, sign_key]
      exact anti _)
    have hc : Fintype.card V = 2*n := by simp [V]
    rw [hc] at ht
    omega
  refine ⟨?_,?_,?_⟩
  · intro y h0 h1
    obtain ⟨h,rfl⟩ := normal y h0 h1
    rw [last]
    exact (cost_bound a b z h).1
  · intro y hy
    obtain ⟨_,h0,h1,ht⟩ := (memF y).1 hy
    obtain ⟨h,rfl⟩ := normal y h0 h1
    rw [last] at ht
    have pp := ((cost_bound a b z h).2.1 ht).1
    refine ⟨bal h pp,fun i => ?_⟩
    rw [Yp,Yp]; exact pp _
  · intro x
    let ok := ∀ j, x (z j) = !(x (a j) && x (b j))
    let yx := Y (enc x)
    have iffF (y : X) : (y ∈ feasible ∧ ∀ i, y (port (false,i)) = x i) ↔ ok ∧ y = yx := by
      constructor
      · rintro ⟨hy,pin⟩
        obtain ⟨ha,h0,h1,ht⟩ := (memF y).1 hy
        obtain ⟨h,rfl⟩ := normal y h0 h1
        rw [Ya] at ha
        rw [last] at ht
        have hp := ((cost_bound a b z h).2.1 ht).1
        have raw (q : Key v) : h (q,false) = baseVal x q := by
          cases q with
          | none => exact ha
          | some i => simpa only [Yp,baseVal] using pin i
        have eq : h = enc x := by
          funext w
          rcases w with ⟨q,t⟩
          cases t
          · exact raw q
          · exact (hp q).trans (congrArg (fun u : Bool => !u) (raw q))
        rw [eq] at ht ⊢
        exact ⟨(enc_top a b z x).1 ht,rfl⟩
      · rintro ⟨hx,rfl⟩
        have he := (enc_top a b z x).2 hx
        refine ⟨(memF _).2 ⟨?_,(zero _).1,(zero _).2,?_⟩,?_⟩
        · exact (Ya (enc x)).trans rfl
        · exact (last (enc x)).trans he
        · intro i
          exact (Yp (enc x) false i).trans rfl
    by_cases hx : ok
    · have he : (feasible.filter (fun y => ∀ i, y (port (false,i)) = x i)) = {yx} := by
        ext y
        rw [Finset.mem_filter,iffF,Finset.mem_singleton]
        simp [hx]
      rw [he,Finset.card_singleton,if_pos hx]
    · have he : (feasible.filter (fun y => ∀ i, y (port (false,i)) = x i)) = ∅ := by
        ext y
        rw [Finset.mem_filter,iffF]
        simp [hx]
      rw [he,Finset.card_empty,if_neg hx]
