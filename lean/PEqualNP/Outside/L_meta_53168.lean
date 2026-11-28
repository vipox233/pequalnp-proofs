import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53168_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inp (N k : ℕ) : List Bool := List.ofFn (fun i : Fin N => decide (i.val < k)) ++ [false,true]

private def M_run (gs : List Gate) (w : List Bool) := gs.foldl
  (fun a g => a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]) w

private def M_tick (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def M_code : List Gate → List Bool → List Bool
  | [], _ => []
  | g::gs, w =>
    let a := M_tick w g
    match g.op with
    | .not => (g.op.eval (g.inputs.map fun i => w.getD i false)) :: M_code gs a
    | _ => M_code gs a

private def M_mark (g : Gate) : Bool := match g.op with | .not => true | _ => false

private theorem M_code_len (gs : List Gate) (w : List Bool) :
    (M_code gs w).length = (gs.filter M_mark).length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [M_code,h,M_mark,List.filter_cons,ih]

private def M_ordered (x y : List Bool) :=
  x.length=y.length ∧ ∀ i, x.getD i false=true → y.getD i false=true

private theorem M_extend_order {x y : List Bool} (w : M_ordered x y) {a b : Bool}
    (ab : a=true → b=true) : M_ordered (x++[a]) (y++[b]) := by
  refine ⟨by simp [w.1],?_⟩
  intro i
  by_cases before : i < x.length
  · rw [List.getD_append _ _ _ _ before,List.getD_append _ _ _ _ (w.1 ▸ before)]
    exact w.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by rw [←w.1]; omega),←w.1]
    cases i-x.length <;> simpa using ab <;> simp

private theorem M_output_order {gs : List Gate}
    (ops : ∀ g∈gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    {x y : List Bool} (w : M_ordered x y) (same : M_code gs x=M_code gs y) :
    M_ordered (M_run gs x) (M_run gs y) := by
  induction gs generalizing x y with
  | nil => exact w
  | cons g gs ih =>
    have rest (a) (ha : a∈gs) := ops a (List.mem_cons_of_mem _ ha)
    change M_ordered (M_run gs (M_tick x g)) (M_run gs (M_tick y g))
    have casesG := ops g (List.mem_cons_self ..)
    rcases casesG with h|h|h
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.all_eq_true,List.mem_map,forall_exists_index,and_imp]
      intro all z i hi ei
      subst z
      exact w.2 i (all _ _ hi rfl)
    · apply ih rest (M_extend_order w ?_) (by simpa only [M_code,M_tick,h] using same)
      simp only [h,GateOp.eval,List.any_eq_true,List.mem_map]
      rintro ⟨z,⟨i,hi,rfl⟩,yes⟩
      exact ⟨_,⟨i,hi,rfl⟩,w.2 i yes⟩
    · simp only [M_code,h,List.cons.injEq] at same
      apply ih rest (M_extend_order w ?_) same.2
      rw [h]
      exact fun e => same.1.symm.trans e

private theorem M_input_order {n : Nat} {x y : Fin n → Bool} (xy : ∀ i, x i=true → y i=true) :
    M_ordered (List.ofFn x ++ [false,true]) (List.ofFn y ++ [false,true]) := by
  refine ⟨by simp,?_⟩
  intro i
  by_cases h : i<n
  · rw [List.getD_append _ _ _ _ (by simpa),List.getD_append _ _ _ _ (by simpa)]
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,h] using xy ⟨i,h⟩
  · rw [List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h)]
    simp
private def M_driverNumber : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 0 else 2^bs.length) + M_driverNumber bs

private theorem M_driver_bound (l : List Bool) : M_driverNumber l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b bs ih => cases b <;> simp [M_driverNumber,pow_succ] <;> omega

private theorem M_driver_injective {a b : List Bool} (len : a.length=b.length)
    (num : M_driverNumber a=M_driverNumber b) : a=b := by
  induction a generalizing b with
  | nil => simpa using len.symm
  | cons x xs ih =>
    cases b with
    | nil => simp at len
    | cons y ys =>
      have sz : xs.length=ys.length := by simpa using len
      have h₁ := M_driver_bound xs
      have h₂ := M_driver_bound ys
      rw [sz] at h₁
      cases x <;> cases y <;> simp [M_driverNumber,sz] at num ⊢ <;> first | exact ih sz num | omega

private theorem M_driver_mono (gs : List Gate) (ops : ∀ g∈gs, g.op=.and ∨ g.op=.or ∨ g.op=.not)
    {a b : List Bool} (ab : M_ordered a b) :
    M_driverNumber (M_code gs a) ≤ M_driverNumber (M_code gs b) := by
  induction gs generalizing a b with
  | nil => rfl
  | cons g gs ih =>
    have tailops := fun h (hh : h∈gs) => ops h (by simp [hh])
    have oneops : ∀ u ∈ [g], u.op=.and ∨ u.op=.or ∨ u.op=.not := by
      simpa using ops g (by simp)
    have growth (same : M_code [g] a=M_code [g] b) : M_ordered (M_tick a g) (M_tick b g) :=
      M_output_order oneops ab same
    rcases ops g (by simp) with eq|eq|eq
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · simp only [M_code,eq]
      exact ih tailops (growth (by simp [M_code,eq]))
    · let out (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
      have anti : out b=true → out a=true := by
        cases inp : g.inputs with
        | nil => simp [out,eq,inp,GateOp.eval]
        | cons i more =>
          simp only [out,eq,inp,GateOp.eval,List.map_cons,List.headD_cons,Bool.not_eq_true']
          intro bz
          cases az : a.getD i false
          · rfl
          · have := ab.2 i az
            simp_all
      have len : (M_code gs (M_tick a g)).length=(M_code gs (M_tick b g)).length := by simp [M_code_len]
      change M_driverNumber (M_code (g::gs) a) ≤ M_driverNumber (M_code (g::gs) b)
      simp only [M_code,eq]
      rw [←eq]
      change M_driverNumber (out a :: M_code gs (M_tick a g)) ≤ M_driverNumber (out b :: M_code gs (M_tick b g))
      by_cases same : out a=out b
      · have next : M_ordered (M_tick a g) (M_tick b g) := M_extend_order ab (by change out a=true → out b=true; rw [same]; exact id)
        simpa only [M_driverNumber,same,len,Nat.add_le_add_iff_left] using
          Nat.add_le_add_left (ih tailops next) (if out b then 0 else 2^(M_code gs (M_tick b g)).length)
      · have zero : out b=false := by cases hb : out b <;> simp_all
        have one : out a=true := by cases ha : out a <;> simp_all
        have bound := M_driver_bound (M_code gs (M_tick a g))
        rw [len] at bound
        simp only [M_driverNumber,one,zero,Bool.false_eq_true,if_false,if_true,Nat.zero_add]
        omega

theorem M_circuit_rank {n : Nat} (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) :
    ∃ h : (Fin n → Bool) → Nat, Monotone h ∧ (∀ x, h x < 2^PEqualNP.NotBracket.notCount C) ∧
      ∀ x y, x ≤ y → h x = h y → ∀ w,
        (C.wires (List.ofFn x ++ [false,true])).getD w false=true →
        (C.wires (List.ofFn y ++ [false,true])).getD w false=true := by
  let raw (x : Fin n → Bool) := List.ofFn x ++ [false,true]
  let h (x : Fin n → Bool) := M_driverNumber (M_code C.gates (raw x))
  have ops (g : Gate) (mem : g ∈ C.gates) := (fan g mem).1
  have order {x y : Fin n → Bool} (xy : x ≤ y) : M_ordered (raw x) (raw y) := by
    apply M_input_order
    intro i hi
    have v := xy i
    rw [hi] at v
    exact le_antisymm (by cases y i <;> decide) v
  have size : (C.gates.filter M_mark).length = PEqualNP.NotBracket.notCount C := by
    unfold PEqualNP.NotBracket.notCount
    congr 1
    apply List.filter_congr
    intro g _
    cases eq : g.op <;> simp [M_mark,eq]
  refine ⟨h,fun x y xy => M_driver_mono _ ops (order xy),?_,?_⟩
  · intro x
    simpa only [h,M_code_len,size] using M_driver_bound (M_code C.gates (raw x))
  · intro x y xy eq w
    have same : M_code C.gates (raw x)=M_code C.gates (raw y) := M_driver_injective (by simp [M_code_len]) eq
    exact (M_output_order ops (order xy) same).2 w

theorem M_main (b N : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hb : PEqualNP.NotBracket.notCount C ≤ b) (w0 : ℕ)
    (hg : ∀ i < 2^b - 1, (C.wires (inp N (2*i))).getD w0 false = true ∧
      (C.wires (inp N (2*i+1))).getD w0 false = false) :
    ∀ w k1 k2, 2*(2^b-1) ≤ k1 → k1 ≤ k2 →
      (C.wires (inp N k1)).getD w false = true → (C.wires (inp N k2)).getD w false = true := by
  obtain ⟨h, hmono, hlt, hsame⟩ := M_circuit_rank (n := N) C hf
  let x : ℕ → Fin N → Bool := fun k i => decide (i.val < k)
  have hx : ∀ k1 k2, k1 ≤ k2 → x k1 ≤ x k2 := by
    intro k1 k2 hk i
    by_cases h1 : i.val < k1
    · have h2 : i.val < k2 := by omega
      simp [x, h1, h2]
    · simp [x, h1]
  have hinp : ∀ k, inp N k = List.ofFn (x k) ++ [false,true] := fun k => rfl
  have hH : ∀ k1 k2, k1 ≤ k2 → h (x k1) ≤ h (x k2) := fun k1 k2 hk => hmono (hx k1 k2 hk)
  have hpow : 2 ^ PEqualNP.NotBracket.notCount C ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hbd : ∀ k, h (x k) ≤ 2^b - 1 := by
    intro k; have := hlt (x k); have : 0 < 2^b := Nat.pow_pos (by norm_num); omega
  have hstep : ∀ i < 2^b - 1, h (x (2*i)) < h (x (2*i+1)) := by
    intro i hi
    rcases lt_or_eq_of_le (hH (2*i) (2*i+1) (by omega)) with h1 | h1
    · exact h1
    · exfalso
      have := hsame (x (2*i)) (x (2*i+1)) (hx _ _ (by omega)) h1 w0
        (by rw [← hinp]; exact (hg i hi).1)
      rw [← hinp, (hg i hi).2] at this
      exact Bool.false_ne_true this
  have hind : ∀ i ≤ 2^b - 1, i ≤ h (x (2*i)) := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have a1 := ih (by omega)
      have a2 := hstep i (by omega)
      have a3 := hH (2*i+1) (2*(i+1)) (by omega)
      omega
  intro w k1 k2 hk1 hk12 hw
  have e1 : h (x k1) = 2^b - 1 := by
    have := hind (2^b-1) le_rfl
    have := hH (2*(2^b-1)) k1 hk1
    have := hbd k1
    omega
  have e2 : h (x k2) = 2^b - 1 := by
    have := hH k1 k2 hk12
    have := hbd k2
    omega
  have := hsame (x k1) (x k2) (hx _ _ hk12) (e1.trans e2.symm) w (by rw [← hinp]; exact hw)
  rw [hinp]; exact this

def C_step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def C_run (w : List Bool) (gs : List Gate) : List Bool := gs.foldl C_step w

theorem C_run_append (w : List Bool) (a b : List Gate) : C_run w (a ++ b) = C_run (C_run w a) b :=
  List.foldl_append

theorem C_run_single (w : List Bool) (g : Gate) : C_run w [g] = C_step w g := rfl

theorem C_run_len : ∀ (gs : List Gate) (w : List Bool), (C_run w gs).length = w.length + gs.length
  | [], w => by simp [C_run]
  | g :: gs, w => by
    have := C_run_len gs (C_step w g)
    simp only [C_run, List.foldl_cons] at this ⊢
    rw [this]; simp [C_step]; omega

theorem C_step_pre (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (C_step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ h

theorem C_step_last (w : List Bool) (g : Gate) :
    (C_step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  unfold C_step; rw [List.getD_append_right _ _ _ _ le_rfl]; simp

theorem C_run_pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
    (C_run w gs).getD i false = w.getD i false
  | [], w, i, _ => rfl
  | g :: gs, w, i, h => by
    have := C_run_pre gs (C_step w g) i (by simp [C_step]; omega)
    simp only [C_run, List.foldl_cons] at this ⊢
    rw [this, C_step_pre w g i h]

def C_R (b : ℕ) : ℕ := 2*(2^b-1)

theorem C_R_succ (b : ℕ) : C_R (b+1) = 2 * C_R b + 2 := by
  unfold C_R; have := Nat.two_pow_pos b; rw [pow_succ]; omega

def C_yl (ins : ℕ → ℕ) (t M s : ℕ) : ℕ → List Gate
  | 0 => []
  | r+1 => C_yl ins t M s r ++ [⟨GateOp.and, [ins r, t]⟩, ⟨GateOp.or, [s + 2*r, ins (r+M+1)]⟩]

def C_len : ℕ → ℕ
  | 0 => 0
  | b+1 => C_len b + 2 * C_R b + 3

def C_out : ℕ → (ℕ → ℕ) → ℕ → ℕ → ℕ
  | 0, _, tr, _ => tr
  | b+1, _, _, base => base + 2 + 2 * C_R b + C_len b

def C_gs : ℕ → (ℕ → ℕ) → ℕ → ℕ → List Gate
  | 0, _, _, _ => []
  | b+1, ins, tr, base =>
    [⟨GateOp.not, [ins (C_R b)]⟩] ++ C_yl ins base (C_R b + 1) (base+1) (C_R b) ++
      [⟨GateOp.or, [base, ins (C_R b + 1)]⟩] ++
      C_gs b (fun j => base + 2 + 2*j) tr (base + 2 + 2 * C_R b) ++
      [⟨GateOp.and, [C_out b (fun j => base + 2 + 2*j) tr (base + 2 + 2 * C_R b),
        base + 1 + 2 * C_R b]⟩]

theorem C_yl_len (ins : ℕ → ℕ) (t M s : ℕ) : ∀ r, (C_yl ins t M s r).length = 2 * r
  | 0 => rfl
  | r+1 => by simp [C_yl, C_yl_len ins t M s r]; omega

theorem C_gs_len : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ), (C_gs b ins tr base).length = C_len b
  | 0, _, _, _ => rfl
  | b+1, ins, tr, base => by
    simp [C_gs, C_len, C_yl_len, C_gs_len b]; omega

theorem C_out_lt : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ), tr < base → C_out b ins tr base < base + C_len b
  | 0, _, _, _, h => by simpa [C_out, C_len] using h
  | b+1, _, _, _, _ => by simp [C_out, C_len]; omega

theorem C_len_le : ∀ b : ℕ, C_len b ≤ b + 6*(2^b-1)
  | 0 => by simp [C_len]
  | b+1 => by
    have ih := C_len_le b
    have := Nat.two_pow_pos b
    simp only [C_len, C_R]; rw [pow_succ]; omega

theorem C_yl_sem (ins : ℕ → ℕ) (t M s : ℕ) : ∀ (r : ℕ) (w : List Bool), w.length = s →
    (∀ j < r, ins j < s ∧ ins (j+M+1) < s) → t < s →
    (C_run w (C_yl ins t M s r)).length = s + 2*r ∧ ∀ j < r,
      (C_run w (C_yl ins t M s r)).getD (s+2*j+1) false =
        ((w.getD (ins j) false && w.getD t false) || w.getD (ins (j+M+1)) false)
  | 0, w, hw, _, _ => by simp [C_yl, C_run, hw]
  | r+1, w, hw, h, ht => by
    obtain ⟨e, v⟩ := C_yl_sem ins t M s r w hw (fun j hj => h j (by omega)) ht
    have hr := h r (by omega)
    set w' := C_run w (C_yl ins t M s r) with hw'
    have pre : ∀ i < s, w'.getD i false = w.getD i false := fun i hi =>
      C_run_pre _ _ _ (by omega)
    simp only [C_yl, C_run_append]
    have e1 : (C_run w' [⟨GateOp.and, [ins r, t]⟩, ⟨GateOp.or, [s + 2*r, ins (r+M+1)]⟩]) =
        C_step (C_step w' ⟨GateOp.and, [ins r, t]⟩) ⟨GateOp.or, [s + 2*r, ins (r+M+1)]⟩ := rfl
    rw [e1]
    refine ⟨by simp [C_step, e]; omega, fun j hj => ?_⟩
    by_cases hjr : j < r
    · rw [C_step_pre _ _ _ (by simp [C_step, e]; omega), C_step_pre _ _ _ (by omega), v j hjr]
    · have hj' : j = r := by omega
      subst hj'
      have l1 : (C_step w' ⟨GateOp.and, [ins j, t]⟩).length = s + 2*j + 1 := by simp [C_step, e]
      rw [← l1, C_step_last]
      have l2 : s + 2*j = w'.length := by omega
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id]
      rw [l2, C_step_last, C_step_pre _ _ _ (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
        Bool.and_true, Bool.or_false]
      rw [pre _ hr.1, pre _ ht, pre _ hr.2]

theorem C_bool (j k R : ℕ) :
    ((decide (j<k) && !decide (R<k)) || decide (j+(R+1)+1 < k)) =
      decide (j < (if k ≤ R then k else if k = R+1 then 0 else k - (R+2))) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  split_ifs <;> omega

theorem C_bool2 (k R : ℕ) (hRe : R % 2 = 0) :
    (decide ((if k ≤ R then k else if k = R+1 then 0 else k - (R+2)) % 2 = 0) &&
      (!decide (R<k) || decide (R+1 < k))) = decide (k % 2 = 0) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not]
  split_ifs <;> omega

theorem C_sem : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ) (w : List Bool) (k : ℕ),
    w.length = base → tr < base → w.getD tr false = true →
    (∀ j < C_R b, ins j < base ∧ w.getD (ins j) false = decide (j < k)) → k ≤ C_R b →
    (C_run w (C_gs b ins tr base)).getD (C_out b ins tr base) false = decide (k % 2 = 0)
  | 0, ins, tr, base, w, k, _, _, htr, _, hk => by
    simp [C_R] at hk; subst hk
    simp only [C_gs, C_out, C_run, List.foldl_nil, htr]; decide
  | b+1, ins, tr, base, w, k, hw, htr, htrv, hins, hk => by
    have hR := C_R_succ b
    have hRe : C_R b % 2 = 0 := by unfold C_R; omega
    rw [hR] at hins hk
    rw [C_gs.eq_2, C_out.eq_2]
    simp only [C_run_append]
    set R := C_R b with hRdef

    set w1 := C_run w [⟨GateOp.not, [ins R]⟩] with hw1
    have e1 : w1.length = base + 1 := by simp [w1, C_run_len, hw]
    have p1 : ∀ i < base, w1.getD i false = w.getD i false := fun i hi =>
      C_run_pre _ _ _ (by omega)
    have v1 : w1.getD base false = !decide (R < k) := by
      have := C_step_last w ⟨GateOp.not, [ins R]⟩
      rw [hw] at this
      rw [hw1, C_run_single, this]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rw [(hins R (by omega)).2]

    obtain ⟨e2, v2⟩ := C_yl_sem ins base (R+1) (base+1) R w1 e1
      (fun j hj => ⟨by have := (hins j (by omega)).1; omega,
        by have := (hins (j+(R+1)+1) (by omega)).1; omega⟩) (by omega)
    set w2 := C_run w1 (C_yl ins base (R + 1) (base + 1) R) with hw2
    have p2 : ∀ i < base + 1, w2.getD i false = w1.getD i false := fun i hi =>
      C_run_pre _ _ _ (by omega)

    set w3 := C_run w2 [⟨GateOp.or, [base, ins (R + 1)]⟩] with hw3
    have e3 : w3.length = base + 2 + 2 * R := by simp [w3, C_run_len, e2]; omega
    have p3 : ∀ i < base + 1 + 2 * R, w3.getD i false = w2.getD i false := fun i hi =>
      C_run_pre _ _ _ (by omega)
    have v3 : w3.getD (base + 1 + 2 * R) false = (!decide (R < k) || decide (R + 1 < k)) := by
      have := C_step_last w2 ⟨GateOp.or, [base, ins (R + 1)]⟩
      rw [e2] at this
      rw [hw3, C_run_single, this]
      have hi := hins (R+1) (by omega)
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id,
        Bool.or_false]
      rw [p2 _ (by omega), v1, p2 _ (by omega), p1 _ hi.1, hi.2]

    have hih := C_sem b (fun j => base + 2 + 2*j) tr (base + 2 + 2 * R) w3
      (if k ≤ R then k else if k = R+1 then 0 else k - (R+2)) e3 (by omega)
      (by rw [p3 _ (by omega), p2 _ (by omega), p1 _ htr, htrv])
      (fun j hj => by
        refine ⟨by omega, ?_⟩
        have hj1 := hins j (by omega)
        have hj2 := hins (j+(R+1)+1) (by omega)
        rw [p3 _ (by omega), show base + 2 + 2*j = base + 1 + 2*j + 1 by omega, v2 j hj,
          v1, p1 _ hj1.1, p1 _ hj2.1, hj1.2, hj2.2]
        exact C_bool j k R)
      (by split_ifs <;> omega)

    set w4 := C_run w3 (C_gs b (fun j => base + 2 + 2 * j) tr (base + 2 + 2 * R)) with hw4
    have e4 : w4.length = base + 2 + 2 * R + C_len b := by simp [w4, C_run_len, e3, C_gs_len]
    have hout := C_out_lt b (fun j => base + 2 + 2 * j) tr (base + 2 + 2 * R) (by omega)
    have := C_step_last w4 ⟨GateOp.and, [C_out b (fun j => base + 2 + 2 * j) tr (base + 2 + 2 * R),
      base + 1 + 2 * R]⟩
    rw [e4] at this
    rw [C_run_single, this]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
      Bool.and_true]
    rw [hih, C_run_pre _ _ _ (by omega), v3]
    exact C_bool2 k R hRe

def C_RB (s : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < s + j

theorem C_RB_append (s : ℕ) (gs1 gs2 : List Gate) (h1 : C_RB s gs1)
    (h2 : C_RB (s + gs1.length) gs2) : C_RB s (gs1 ++ gs2) := by
  intro j hj i hi
  by_cases hj1 : j < gs1.length
  · rw [List.getD_append _ _ _ _ hj1] at hi; exact h1 j hj1 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    have := h2 (j - gs1.length) (by rw [List.length_append] at hj; omega) i hi; omega

theorem C_RB_one (s : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < s) : C_RB s [g] := by
  intro j hj i hi
  have : j = 0 := by simp at hj; omega
  subst this
  have := h i (by simpa using hi); omega

theorem C_RB_yl (ins : ℕ → ℕ) (t M s : ℕ) : ∀ r, (∀ j < r, ins j < s ∧ ins (j+M+1) < s) → t < s →
    C_RB s (C_yl ins t M s r)
  | 0, _, _ => by intro j hj; simp [C_yl] at hj
  | r+1, h, ht => by
    simp only [C_yl]
    apply C_RB_append _ _ _ (C_RB_yl ins t M s r (fun j hj => h j (by omega)) ht)
    rw [C_yl_len]
    have hr := h r (by omega)
    have : [(⟨GateOp.and, [ins r, t]⟩ : Gate), ⟨GateOp.or, [s + 2*r, ins (r+M+1)]⟩] =
      [⟨GateOp.and, [ins r, t]⟩] ++ [⟨GateOp.or, [s + 2*r, ins (r+M+1)]⟩] := rfl
    rw [this]
    apply C_RB_append
    · apply C_RB_one; intro i hi; simp at hi; omega
    · simp only [List.length_singleton]
      apply C_RB_one; intro i hi; simp at hi; omega

theorem C_RB_gs : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ), (∀ j < C_R b, ins j < base) → tr < base →
    C_RB base (C_gs b ins tr base)
  | 0, _, _, _, _, _ => by intro j hj; simp [C_gs] at hj
  | b+1, ins, tr, base, h, ht => by
    rw [C_R_succ] at h
    simp only [C_gs]
    have hout := C_out_lt b (fun j => base + 2 + 2 * j) tr (base + 2 + 2 * C_R b) (by omega)
    refine C_RB_append _ _ _ (C_RB_append _ _ _ (C_RB_append _ _ _ (C_RB_append _ _ _ ?_ ?_) ?_) ?_) ?_
    · apply C_RB_one; intro i hi; simp at hi; have := h (C_R b) (by omega); omega
    · simp only [List.length_singleton]
      apply C_RB_yl
      · intro j hj; have := h j (by omega); have := h (j + (C_R b + 1) + 1) (by omega); omega
      · omega
    · simp only [List.length_append, List.length_singleton, C_yl_len]
      apply C_RB_one; intro i hi; simp at hi; have := h (C_R b + 1) (by omega); omega
    · simp only [List.length_append, List.length_singleton, C_yl_len]
      have := C_RB_gs b (fun j => base + 2 + 2 * j) tr (base + 2 + 2 * C_R b)
        (fun j hj => by omega) (by omega)
      rwa [show 1 + 2 * C_R b + 1 = 2 + 2 * C_R b by omega, ← Nat.add_assoc]
    · simp only [List.length_append, List.length_singleton, C_yl_len, C_gs_len]
      apply C_RB_one; intro i hi; simp at hi; omega

def C_FT (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem C_FT_append (a b : List Gate) (ha : C_FT a) (hb : C_FT b) : C_FT (a ++ b) := by
  intro g hg; rcases List.mem_append.1 hg with h | h; exact ha g h; exact hb g h

theorem C_FT_yl (ins : ℕ → ℕ) (t M s : ℕ) : ∀ r, C_FT (C_yl ins t M s r)
  | 0 => by intro g hg; simp [C_yl] at hg
  | r+1 => by
    simp only [C_yl]
    apply C_FT_append _ _ (C_FT_yl ins t M s r)
    intro g hg; simp at hg; rcases hg with rfl | rfl <;> simp

theorem C_FT_gs : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ), C_FT (C_gs b ins tr base)
  | 0, _, _, _ => by intro g hg; simp [C_gs] at hg
  | b+1, ins, tr, base => by
    simp only [C_gs]
    refine C_FT_append _ _ (C_FT_append _ _ (C_FT_append _ _ (C_FT_append _ _ ?_ (C_FT_yl _ _ _ _ _))
      ?_) (C_FT_gs _ _ _ _)) ?_ <;>
      (intro g hg; simp at hg; subst hg; simp)

def C_nc (gs : List Gate) : ℕ :=
  (gs.filter fun g => @decide (g.op = GateOp.not) (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq _ _)).length

theorem C_nc_append (a b : List Gate) : C_nc (a ++ b) = C_nc a + C_nc b := by
  simp [C_nc, List.filter_append]

theorem C_nc_yl (ins : ℕ → ℕ) (t M s : ℕ) : ∀ r, C_nc (C_yl ins t M s r) = 0
  | 0 => rfl
  | r+1 => by simp only [C_yl, C_nc_append, C_nc_yl ins t M s r]; simp [C_nc]

theorem C_nc_gs : ∀ (b : ℕ) (ins : ℕ → ℕ) (tr base : ℕ), C_nc (C_gs b ins tr base) = b
  | 0, _, _, _ => rfl
  | b+1, ins, tr, base => by
    simp only [C_gs, C_nc_append, C_nc_yl, C_nc_gs b]
    simp [C_nc]
    omega

theorem C_inp_lt (N k j : ℕ) (hj : j < N) : (inp N k).getD j false = decide (j < k) := by
  unfold inp
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem C_inp_tr (N k : ℕ) : (inp N k).getD (N+1) false = true := by
  unfold inp
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem C_inp_len (N k : ℕ) : (inp N k).length = N + 2 := by simp [inp]

theorem C_main (b N : ℕ) (hN : 2*(2^b-1) ≤ N) :
    ∃ (C : Circuit) (g : ℕ), FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+2) C ∧
      C.output < N+2+C.size ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ b + 6*(2^b-1) ∧
      g < N+2+C.size ∧ ∀ i < 2^b - 1, (C.wires (inp N (2*i))).getD g false = true ∧
        (C.wires (inp N (2*i+1))).getD g false = false := by
  let C : Circuit := ⟨C_gs b id (N+1) (N+2), C_out b id (N+1) (N+2)⟩
  have hsize : C.size = C_len b := C_gs_len b id (N+1) (N+2)
  have hout : C.output < N+2+C.size := by
    rw [hsize]; exact C_out_lt b id (N+1) (N+2) (by omega)
  have hval : ∀ k ≤ C_R b, (C.wires (inp N k)).getD C.output false = decide (k % 2 = 0) := by
    intro k hk
    exact C_sem b id (N+1) (N+2) (inp N k) k (C_inp_len N k) (by omega) (C_inp_tr N k)
      (fun j hj => ⟨by unfold C_R at hj; show j < N+2; omega, C_inp_lt N k j (by unfold C_R at hj; omega)⟩) hk
  refine ⟨C, C.output, C_FT_gs b id (N+1) (N+2), ?_, hout, ?_, ?_, hout, fun i hi => ?_⟩
  · intro j hj i hi
    exact C_RB_gs b id (N+1) (N+2) (fun j hj => by unfold C_R at hj; show j < N+2; omega) (by omega) j hj i hi
  · have := C_nc_gs b id (N+1) (N+2)
    unfold PEqualNP.NotBracket.notCount; unfold C_nc at this; rw [this]
  · rw [hsize]; exact C_len_le b
  · refine ⟨?_, ?_⟩
    · rw [hval (2*i) (by unfold C_R; omega)]; simp
    · rw [hval (2*i+1) (by unfold C_R; omega)]; simp

theorem wires_getD_lt (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  unfold Circuit.wires
  suffices h : ∀ (gs : List Gate) (y : List Bool), i < y.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD i false
        = y.getD i false from h _ _ hi
  intro gs
  induction gs with
  | nil => intro y _; rfl
  | cons g gs ih =>
    intro y hy
    simp only [List.foldl_cons]
    rw [ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hy

theorem inp_false (N k : ℕ) (C : Circuit) : (C.wires (inp N k)).getD N false = false := by
  rw [wires_getD_lt _ _ _ (by simp [inp])]
  simp [inp, List.getD_append_right]

theorem inp_true (N k : ℕ) (C : Circuit) : (C.wires (inp N k)).getD (N+1) false = true := by
  rw [wires_getD_lt _ _ _ (by simp [inp])]
  simp [inp, List.getD_append_right]

end PEqualNP.Outside.L_meta_53168_aux

theorem PEqualNP.Outside.L_meta_53168 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n T b : Nat) (E : Finset (Fin n × Fin n)), (∀ e ∈ E, e.1 < e.2) →
  let d := 2^b-1
  let N := 2*d+n
  let G := {e : Fin n × Fin n // e ∈ E}
  let K := Sum G (Fin n)
  let J := Sum Unit K
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let input := fun k : Nat => List.ofFn (fun i : Fin N => decide (i.val < k)) ++ [false,true]
  let taps := fun (C : Circ) => J → Fin (N+2+C.size)
  let valid := fun (C : Circ) => PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+2) C ∧ C.output < N+2+C.size ∧
    PEqualNP.NotBracket.notCount C ≤ b
  let val := fun (C : Circ) (a : taps C) (k : Nat) (j : J) =>
    (C.wires (input k)).getD (a j).val false
  let guarded := fun (C : Circ) (a : taps C) => ∀ i : Fin d,
    val C a (2*i.val) (Sum.inl ()) = true ∧ val C a (2*i.val+1) (Sum.inl ()) = false
  let good := fun (C : Circ) (a : taps C) (v : Fin n) =>
    val C a (2*d+v.val) (Sum.inr (Sum.inr v)) = true ∧ ∀ e : G,
      (e.val.1 = v → val C a (2*d+v.val) (Sum.inr (Sum.inl e)) = true) ∧
      (e.val.2 = v → val C a (2*d+v.val) (Sum.inr (Sum.inl e)) = false)
  let proper := fun (col : Fin n → Finset (Fin T)) => ∀ e : G,
    Disjoint (col e.val.1) (col e.val.2)
  (∀ q : Fin n → Nat,
    (∃ (cs : Fin T → Circ) (a : ∀ t, taps (cs t)),
      (∀ t, valid (cs t) ∧ guarded (cs t) (a t)) ∧ ∀ v,
        ((Finset.univ : Finset (Fin T)).filter (fun t => good (cs t) (a t) v)).card = q v) ↔
    ∃ col : Fin n → Finset (Fin T), proper col ∧ ∀ v, (col v).card = q v) ∧
  ∃ (C : Circ) (g : Fin (N+2+C.size)), valid C ∧ C.size ≤ b+6*d ∧
    ∀ col : Fin n → Finset (Fin T), proper col →
      ∃ a : Fin T → taps C, (∀ t, a t (Sum.inl ()) = g ∧ guarded C (a t) ∧
        ∀ k : K, (a t (Sum.inr k)).val = N ∨ (a t (Sum.inr k)).val = N+1) ∧
      ∀ t v, (good C (a t) v ↔ t ∈ col v)) := by
  intro n T b E hE d N G K J Circ input taps valid val guarded good proper
  have hin : ∀ k, input k = PEqualNP.Outside.L_meta_53168_aux.inp N k := by
    intro k; simp only [input, PEqualNP.Outside.L_meta_53168_aux.inp]; congr 1; congr; funext i; congr
  have hval : ∀ (C : Circ) (a : taps C) k j,
      val C a k j = (C.wires (PEqualNP.Outside.L_meta_53168_aux.inp N k)).getD (a j).val false := by
    intro C a k j; simp only [val, hin]

  have hsec : ∃ (C : Circ) (g : Fin (N+2+C.size)), valid C ∧ C.size ≤ b+6*d ∧
      ∀ col : Fin n → Finset (Fin T), proper col →
        ∃ a : Fin T → taps C, (∀ t, a t (Sum.inl ()) = g ∧ guarded C (a t) ∧
          ∀ k : K, (a t (Sum.inr k)).val = N ∨ (a t (Sum.inr k)).val = N+1) ∧
        ∀ t v, (good C (a t) v ↔ t ∈ col v) := by
    obtain ⟨C, g, hf, hrb, hout, hnc, hsz, hg, hguard⟩ :=
      PEqualNP.Outside.L_meta_53168_aux.C_main b N (by simp only [N, d]; omega)
    refine ⟨C, ⟨g, hg⟩, ⟨hf, hrb, hout, hnc⟩, hsz, fun col hcol => ?_⟩
    let cst := fun (bit : Bool) => (if bit then ⟨N+1, by omega⟩ else ⟨N, by omega⟩ : Fin (N+2+C.size))
    have hcst : ∀ k bit, (C.wires (PEqualNP.Outside.L_meta_53168_aux.inp N k)).getD (cst bit).val false
        = bit := by
      intro k bit; cases bit
      · exact PEqualNP.Outside.L_meta_53168_aux.inp_false N k C
      · exact PEqualNP.Outside.L_meta_53168_aux.inp_true N k C
    let a : Fin T → taps C := fun t j => match j with
      | Sum.inl () => ⟨g, hg⟩
      | Sum.inr (Sum.inl e) => cst (decide (t ∈ col e.val.1))
      | Sum.inr (Sum.inr v) => cst (decide (t ∈ col v))
    refine ⟨a, fun t => ⟨rfl, fun i => ?_, fun k => ?_⟩, fun t v => ?_⟩
    · rw [hval, hval]; exact hguard i.val i.isLt
    · rcases k with e | v
      · by_cases h : t ∈ col e.val.1 <;> simp [a, cst, h]
      · by_cases h : t ∈ col v <;> simp [a, cst, h]
    · simp only [good, hval, a, hcst, decide_eq_true_eq, decide_eq_false_iff_not]
      constructor
      · exact fun h => h.1
      · intro htv
        refine ⟨htv, fun e => ⟨fun h1 => h1 ▸ htv, fun h2 hc => ?_⟩⟩
        exact Finset.disjoint_left.mp (hcol e) hc (h2 ▸ htv)
  refine ⟨fun q => ⟨?_, ?_⟩, hsec⟩
  · rintro ⟨cs, a, hv, hq⟩
    refine ⟨fun v => (Finset.univ : Finset (Fin T)).filter (fun t => good (cs t) (a t) v),
      fun e => ?_, fun v => by convert hq v⟩
    rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨⟨hf, -, -, hnc⟩, hgd⟩ := hv t
    have hM := PEqualNP.Outside.L_meta_53168_aux.M_main b N (cs t) hf hnc (a t (Sum.inl ())).val
      (fun i hi => by
        have := hgd ⟨i, hi⟩
        rw [hval, hval] at this; exact this)
    have t1 := (h1.2 e).1 rfl
    have t2 := (h2.2 e).2 rfl
    rw [hval] at t1 t2
    have := hM _ (2*d + e.val.1.val) (2*d + e.val.2.val) (by simp only [d]; omega)
      (by have := hE e.val e.property; simp only [Fin.lt_def] at this; omega) t1
    rw [this] at t2; exact Bool.noConfusion t2
  · rintro ⟨col, hcol, hq⟩
    obtain ⟨C, g, hvC, -, hall⟩ := hsec
    obtain ⟨a, ha, hgood⟩ := hall col hcol
    refine ⟨fun _ => C, a, fun t => ⟨hvC, (ha t).2.1⟩, fun v => ?_⟩
    rw [← hq v]; congr 1; ext t; simp [hgood t v]
