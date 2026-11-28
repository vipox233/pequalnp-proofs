import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_43138

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276808360 * 2 ^ 32 + 3941263872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x8000040ad8215856#64 ++ 0xa0000102b6085615#64 ++ 0x64023c7ff9e3f8ff#64 ++ 0xd9008f1ffe78fe3f#64 : BitVec 256),
   (0x041cd1a62aaccb30#64 ++ 0xc10734698aab32cc#64 ++ 0xec3dd3a63ebccf33#64 ++ 0xbb0f74e98faf33cc#64 : BitVec 256),
   (0x09c162c745370dc3#64 ++ 0x027058b1d14dc370#64 ++ 0xffc1e3c7c73f0fc3#64 ++ 0x7ff078f1f1cfc3f0#64 : BitVec 256),
   (0x02ee037007c006a8#64 ++ 0x00bb80dc01f001aa#64 ++ 0xfbfe03f807c00ffe#64 ++ 0xfeff80fe01f003ff#64 : BitVec 256),
   (0x0377b80007daa000#64 ++ 0x00ddee0001f6a800#64 ++ 0xfffffc0007fff001#64 ++ 0xffffff0001fffc00#64 : BitVec 256),
   (0x13bbfffdb0000000#64 ++ 0x04eeffff6c000000#64 ++ 0xd3fffffff8000003#64 ++ 0xf4fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0111b800001aa000 0x00446e000006a800 0x0001c000001c0000 0x0000700000070000

def z1 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z2 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc0007fff001 0xffffff0001fffc00

def z3 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z4 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z5 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z6 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x64023c7ff9e3f8ff 0xd9008f1ffe78fe3f

def z7 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0xd3ffff8000000001 0xf4ffffe000000000

def z8 : W := mkw 0x09c1224345330cc3 0x02704890d14cc330 0x77c02047c12308c3 0x5df00811f048c230

def z9 : W := mkw 0x0840000005160581 0x0210000001458160 0x08000000061c0700 0x02000000018701c0

def z10 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0xc83dd3a63e1c0703 0xb20f74e98f8701c0

def z11 : W := mkw 0x8000000248215856 0xa000000092085615 0x2400000001e3f8fc 0x090000000078fe3f

def z12 : W := mkw 0x03e32a5005522488 0x00f8ca9401548922 0x13c22c58014330cc 0x44f08b160050cc33

def z13 : W := mkw 0x0000000240210842 0x0000000090084210 0x6402207fc1e308ff 0xd900881ff078c23f

def z14 : W := mkw 0x822e05389ac0523c 0xa08b814e26b0148f 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z15 : W := mkw 0x0000000208204810 0x8000000082081204 0x6400102638a0c833 0x990004098e28320c

def z16 : W := mkw 0x841cd5aefaaddb76 0xe107356bbeab76dd 0xec3fffffffffffff 0xfb0fffffffffffff

def z17 : W := mkw 0x09c963f745370feb 0x027258fdd14dc3fa 0xffc1e3ffc73f0fff 0x7ff078fff1cfc3ff

def z18 : W := mkw 0x0d1df1a76abfcb73 0xc3477c69daaff2dc 0xec3df3a7febfcf33 0xbb0f7ce9ffaff3cc

def z19 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0xd3fe03f800000002 0xf4ff80fe00000000

def z20 : W := mkw 0x108847fdb0000000 0x042211ff6c000000 0x000003fff8000002 0x000000fffe000000

def z21 : W := mkw 0x0018d5acb0000000 0x0006356b2c000000 0xc03ffffff8000003 0xf00ffffffe000000

def z22 : W := mkw 0x018162c500000000 0x006058b140000000 0xd3c1e3c7c0000003 0x74f078f1f0000000

def z23 : W := mkw 0x1bfbfffff5370dc3 0x06fefffffd4dc370 0xffffffffff3f0fc3 0xffffffffffcfc3f0

def z24 : W := mkw 0x8000040898005014 0xa000010226001405 0x00021c3838c0f03c 0x8000870e0e303c0f

def z25 : W := mkw 0x89c166cfdd375dd7 0xa27059b3f74dd775 0xffc3ffffffffffff 0xfff0ffffffffffff

def z26 : W := mkw 0x02ee077897c006a8 0x00bb81de25f001aa 0xfbfe3fffffc00fff 0xfeff8ffffff003ff

def z27 : W := mkw 0x000c012002800220 0x0003004800a00088 0x003c002000800030 0x800f00080020000c

def z28 : W := mkw 0x123a9d38b0000000 0x048ea74e2c000000 0x003e1c3838000000 0x800f870e0e000000

def z29 : W := mkw 0x0ffff3f76fffcffb 0xc3fffcfddbfff3fe 0xfffff3ffffffcfff 0xfffffcfffffff3ff

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x64023c0001e3f001 0xd9008f000078fc00

def z31 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3ffc7c7ffffc3 0xfff0fff1f1fffff0

def z32 : W := mkw 0x041c91202a88c230 0xc10724480aa2308c 0x003c10203880c030 0x800f04080e20300c

def z33 : W := mkw 0x09c12241451304c3 0x027048905144c130 0x13c02041c10300c0 0x44f008107040c030

def z34 : W := mkw 0x0018d1a420000000 0x0006346908000000 0xc03dd3a638000003 0xb00f74e98e000000

def z35 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0x883dc380061c0700 0x220f70e0018701c0

def z36 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfe03d8074007cc 0x66ff80f601d001f3

def z37 : W := mkw 0x80000408d0011046 0x2000010234004411 0x00022c59c14330cc 0x40008b167050cc33

def z38 : W := mkw 0x03ffbb7007daa6a8 0x00ffeedc01f6a9aa 0x9bfdc380061c0700 0x26ff70e0018701c0

def z39 : W := mkw 0x06fed3f62feccfb8 0xc1bfb4fd8bfb33ee 0xffffd3fe3ffccfff 0xfffff4ff8fff33ff

def z40 : W := mkw 0x0111b800001aa000 0x00446e000006a800 0x6403fc0001fff001 0xd900ff00007ffc00

def z41 : W := mkw 0x8000000040011046 0x2000000010004411 0x00000000014330cc 0x000000000050cc33

def z42 : W := mkw 0x0c5cd1a66fbfcff3 0xc31734699beff3fc 0xec3dd3a63fbfcff3 0xbb0f74e98feff3fc

def z43 : W := mkw 0x884000024d375dd7 0xa2100000934dd775 0x2c00000007fffffc 0x0b00000001ffffff

def z44 : W := mkw 0x0044000007c00000 0x0011000001f00000 0x2800000007c00000 0x0a00000001f00000

def z45 : W := mkw 0x0044000007c006a8 0x0011000001f001aa 0x2800000007c00ffc 0x0a00000001f003ff

def z46 : W := mkw 0x1111fc8db0000000 0x04447f236c000000 0x0001fc07f8000001 0x00007f01fe000000

def z47 : W := mkw 0x0333bc0890000000 0x00ccef0224000000 0xd3fffc7ff8000003 0xf4ffff1ffe000000

def z48 : W := mkw 0x841c952afaa9da76 0xe107254abeaa769d 0x643e3c7ff9e3f8ff 0xd90f8f1ffe78fe3f

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x00020058014000cc 0x4000801600500033

def z50 : W := mkw 0x0040000005000480 0x0010000001400120 0x2800000007000fc0 0x0a00000001c003f0

def z51 : W := mkw 0x063ed9a62aeceb30 0xc18fb6698abb3acc 0xec3fdfa63efcff33 0xbb0ff7e98fbf3fcc

def z52 : W := mkw 0x0333b800001aa000 0x00ccee000006a800 0xd7fffc00003ff001 0xf5ffff00000ffc00

def z53 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x2400007ff9e3f8fe 0x0900001ffe78fe3f

def z54 : W := mkw 0x088042c740250dc3 0x022010b1d0094370 0x000003c7c0000fc2 0x000000f1f00003f0

def z55 : W := mkw 0x13fffffdb7daa000 0x04ffffff6df6a800 0xdbfffffffe1c0003 0xf6ffffffff870000

def z56 : W := mkw 0x04040000028c8320 0x4101000000a320c8 0x08000000061c0700 0x02000000018701c0

def z57 : W := mkw 0x0844000247f70feb 0x0211000091fdc3fa 0x2c00000007ff0ffc 0x0b00000001ffc3ff

def z58 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0x9bc1e3c1c71f07c0 0x66f078f071c7c1f0

def z59 : W := mkw 0x07fffbf62ffeefb8 0xc1fffefd8bffbbee 0xfffffffe3fffffff 0xffffffff8fffffff

def z60 : W := mkw 0x0901200140130043 0x024048005004c010 0x00002001c0030000 0x000008007000c000

def z61 : W := mkw 0x0000000000000000 0x0000000000000000 0x6002007801c008fe 0xd800801e0070023f

def z62 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fd3fe3ffccfff 0xfb0ff4ff8fff33ff

def z63 : W := mkw 0x077ff9a62ffeeb30 0xc1dffe698bffbacc 0xffffffa63fffff33 0xffffffe98fffffcc

def z64 : W := mkw 0x0000408600240900 0x0000102180090240 0xec01c386063c0f03 0x3b0070e1818f03c0

def z65 : W := mkw 0x0be32a41455324c3 0x02f8ca905154c930 0x13c22c41c14330c0 0x44f08b107050cc30

def z66 : W := mkw 0x041c91222aa8ca30 0xc10724488aaa328c 0x643c102638a0c833 0x990f04098e28320c

def z67 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0xd3fdd3a638000003 0xb4ff74e98e000000

def z68 : W := mkw 0x89c12649d51314c7 0x227049927544c531 0x13c22c59c14330cc 0x44f08b167050cc33

def z69 : W := mkw 0x00c042c605240d80 0x003010b181490360 0xffc1c3c6073c0fc3 0x7ff070f181cf03f0

def z70 : W := mkw 0x19d1fecff5370dc3 0x06747fb3fd4dc370 0xffc1ffc7ff3f0fc3 0x7ff07ff1ffcfc3f0

def z71 : W := mkw 0x077fb9202fdae230 0xc1dfee480bf6b88c 0xfffffc203ffff031 0xffffff080ffffc0c

def z72 : W := mkw 0x041cd1a42a88c230 0xc10734690aa2308c 0xc03dd3a63880c033 0xb00f74e98e20300c

def z73 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x000003f800000ffe 0x000000fe000003ff

def z74 : W := mkw 0x8bef67ffdff75fff 0xa2fbd9fff7fdd7ff 0xffffffffffffffff 0xffffffffffffffff

def z75 : W := mkw 0x0000408400000000 0x0000102100000000 0xc001c38600000003 0x300070e180000000

def z76 : W := mkw 0x8000000248215856 0xa000000092085615 0x64023c0001e3f8fd 0xd9008f000078fe3f

def z77 : W := mkw 0x17bfffffbaaccb30 0xc5efffffeeab32cc 0xfffffffffebccf33 0xffffffffffaf33cc

def z78 : W := mkw 0x0018d1a620240900 0x0006346988090240 0xec3dd3a63e3c0f03 0xbb0f74e98f8f03c0

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000000001c008fc 0x080000000070023f

def z80 : W := mkw 0x13fffffdb7c006a8 0x04ffffff6df001aa 0xdbfffffffe000703 0xf6ffffffff8001c0

def z81 : W := mkw 0x0014900002888000 0x0005240000a22000 0x883dc000061c0000 0x220f700001870000

def z82 : W := mkw 0x93bbfffff8215856 0xa4eefffffe085615 0xf7fffffff9e3f8ff 0xfdfffffffe78fe3f

def z83 : W := mkw 0x13a32e5990000000 0x04e8cb9664000000 0x13c22c59c0000000 0x44f08b1670000000

def z84 : W := mkw 0x80c0064add215cd6 0xa0300192b7485735 0xffc23fffffe3ffff 0xfff08ffffff8ffff

def z85 : W := mkw 0x13bffffdb2c8a000 0x04efffff6cb22800 0xd3fffffff8c0f003 0xf4fffffffe303c00

def z86 : W := mkw 0x82369c089ac8f014 0xa08da70226b23c05 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z87 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe038007c00700 0xfeff80e001f001c0

def z88 : W := mkw 0x018162c700240900 0x006058b1c0090240 0xffc1e3c7c63c0f03 0x7ff078f1f18f03c0

def z89 : W := mkw 0x0276980007daa000 0x009da60001f6a800 0x2c3e1c0007fff000 0x8b0f870001fffc00

def z90 : W := mkw 0x0000000240210842 0x0000000090084210 0x64002047c12308c3 0x59000811f048c230

def z91 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0x883dd3a03e9cc730 0xa20f74e80fa731cc

def z92 : W := mkw 0x0000040890000000 0x0000010224000000 0x40023c7ff8000003 0xd0008f1ffe000000

def z93 : W := mkw 0x0266000007c00000 0x0099800001f00000 0xfbfe000007c00000 0xfeff800001f00000

def z94 : W := mkw 0x0800408740250943 0x02001021d0094250 0x00000007c0000000 0x00000001f0000000

def z95 : W := mkw 0x82ee077adfe15efe 0xa0bb81deb7f857bf 0xfbfe03ffffc00ffe 0xfeff80fffff003ff

def z96 : W := mkw 0x0199f3e520000000 0x00667cf948000000 0xd3fdf3e7f8000003 0xf4ff7cf9fe000000

def z97 : W := mkw 0x0dddf3e76fbfcff3 0xc3777cf9dbeff3fc 0xfffdf3e7ffbfcff3 0xffff7cf9ffeff3fc

def z98 : W := mkw 0x041c912022888220 0x4107244808a22088 0x003c000000000000 0x000f000000000000

def z99 : W := mkw 0x0bef63f747f70feb 0x02fbd8fdd1fdc3fa 0xffffe3ffc7ff0fff 0xfffff8fff1ffc3ff

def z100 : W := mkw 0x0363280005522000 0x00d8ca0001548800 0x13c22c0001433000 0x44f08b000050cc00

def z101 : W := mkw 0x040841a628244b30 0xc10210698a0912cc 0x000003a638000f32 0x000000e98e0003cc

def z102 : W := mkw 0x040400020aaccb30 0xc101000082ab32cc 0x2c00000006bccf30 0x0b00000001af33cc

def z103 : W := mkw 0x0840000245370dc3 0x02100000914dc370 0x2c000000073f0fc0 0x0b00000001cfc3f0

def z104 : W := mkw 0x82ee077adfe15efe 0xa0bb81deb7f857bf 0xfffe3fffffe3ffff 0xffff8ffffff8ffff

def z105 : W := mkw 0x0be36ac745772dc3 0x02f8dab1d15dcb70 0xffc3efc7c77f3fc3 0x7ff0fbf1f1dfcff0

def z106 : W := mkw 0x088042c740250dc3 0x022010b1d0094370 0x640023c7c1230fc3 0x590008f1f048c3f0

def z107 : W := mkw 0x09c162c505160581 0x027058b141458160 0xffc1e380073f0701 0x7ff078e001cfc1c0

def z108 : W := mkw 0x0044000007daa000 0x0011000001f6a800 0x2c00000007fff000 0x0b00000001fffc00

def z109 : W := mkw 0x09c162c505160581 0x027058b141458160 0x9bc1c380061c0700 0x26f070e0018701c0

def z110 : W := mkw 0x0014900002888000 0x0005240000a22000 0xec3dd00006bcc001 0xbb0f740001af3000

def z111 : W := mkw 0x0232980000000000 0x008ca60000000000 0x003e1c0000000000 0x800f870000000000

def z112 : W := mkw 0x03ffbb7007c006a8 0x00ffeedc01f001aa 0xfbfffff807c00fff 0xfefffffe01f003ff

def z113 : W := mkw 0x077ff9a427dea320 0x41dffe6909f7a8c8 0xffffff8007fff701 0xffffffe001fffdc0

def z114 : W := mkw 0x0bf7fac507dea581 0x02fdfeb141f7a960 0xffffff8007fff701 0xffffffe001fffdc0

def z115 : W := mkw 0x8000040898005014 0xa000010226001405 0x00001c003800f000 0x000007000e003c00

def z116 : W := mkw 0x033bf9a420000000 0x00cefe6908000000 0xd3ffffa638000003 0xf4ffffe98e000000

def z117 : W := mkw 0x0014900002888000 0x0005240000a22000 0xec3ffc0007fff001 0xfb0fff0001fffc00

def z118 : W := mkw 0x9bfbfffffd375dd7 0xa6feffffff4dd775 0xffffffffffffffff 0xffffffffffffffff

def z119 : W := mkw 0x1119fdadb0000000 0x04467f6b6c000000 0xc03dffa7f8000003 0xb00f7fe9fe000000

def z120 : W := mkw 0x00c0024005000480 0x0030009001400120 0xfbc003c007000fc2 0x7ef000f001c003f0

def z121 : W := mkw 0x02ea0370054006a8 0x00ba80dc015001aa 0x13c203f801400ffe 0x44f080fe005003ff

def z122 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x003c13a63880cf32 0x800f04e98e2033cc

def z123 : W := mkw 0x000c012002800220 0x0003004800a00088 0xe83e03f807c00ffe 0xfa0f80fe01f003ff

def z124 : W := mkw 0x03ef63f507c006a8 0x00fbd8fd41f001aa 0xfbffe3ffc7c00fff 0xfefff8fff1f003ff

def z125 : W := mkw 0x13fffffdb7c006a8 0x04ffffff6df001aa 0xfbffffffffc00fff 0xfefffffffff003ff

def z126 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9ffdfc00063ff001 0x27ff7f00018ffc00

def z127 : W := mkw 0x908847fff8215856 0xa42211fffe085615 0x64023ffff9e3f8ff 0xd9008ffffe78fe3f

def z128 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x64003c27f8a3f833 0x99000f09fe28fe0c

def z129 : W := mkw 0x001cd1a422888000 0x0007346908a22000 0xec3dd3a63ebcc003 0xbb0f74e98faf3000

def z130 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x0000007ff80008fe 0x0000001ffe00023f

def z131 : W := mkw 0x0dddf3e72fbecfb1 0xc3777cf9cbefb3ec 0xfffdd3a63ebccf33 0xbfff74e98faf33cc

def z132 : W := mkw 0x0418d1a6282cc910 0xc10634698a0b3244 0xc43dd3a6383cc003 0xb10f74e98e0f3000

def z133 : W := mkw 0x040400000a88c230 0xc101000002a2308c 0x000000000080c030 0x000000000020300c

def z134 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf3fffffff9c008ff 0xfcfffffffe70023f

def z135 : W := mkw 0x03ef2b7007d226a8 0x00fbcadc01f489aa 0xfbfe2ff807c33ffe 0xfeff8bfe01f0cfff

def z136 : W := mkw 0x118967fdb0000000 0x046259ff6c000000 0xd3c1e3fff8000003 0x74f078fffe000000

def z137 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0xd3fffc0000000001 0xf4ffff0000000000

def z138 : W := mkw 0x02ee037007c00000 0x00bb80dc01f00000 0xfbfe03f807c00002 0xfeff80fe01f00000

def z139 : W := mkw 0x0044000007daa000 0x0011000001f6a800 0x08000000061c0000 0x0200000001870000

def z140 : W := mkw 0x0c8843e768254ff3 0xc32210f9da0953fc 0x000003e7f8000ff2 0x000000f9fe0003fc

def z141 : W := mkw 0x022e013002c00228 0x008b804c00b0008a 0x003e003800c0003c 0x800f800e0030000f

def z142 : W := mkw 0x0bef63f507d607a9 0x02fbd8fd41f581ea 0x9bfdc380061c0700 0x26ff70e0018701c0

def z143 : W := mkw 0x09c562c747f70feb 0x027158b1d1fdc3fa 0xffc1e3c7c7ff0fff 0x7ff078f1f1ffc3ff

def z144 : W := mkw 0x10080538b0000000 0x0402014e2c000000 0x0000003838000000 0x0000000e0e000000

def z145 : W := mkw 0x0c4400024fbfcff3 0xc311000093eff3fc 0x2c00000007bfcff0 0x0b00000001eff3fc

def z146 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffefd9c0000000 0x64fffbf670000000

def z147 : W := mkw 0x02ea037005000480 0x00ba80dc01400120 0xfbfe03f807000fc2 0xfeff80fe01c003f0

def z148 : W := mkw 0x82369c0adae9f856 0xa08da702b6ba7e15 0x643e3c7ff9e3f8ff 0xd90f8f1ffe78fe3f

def z149 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9bfdc000061c0000 0x26ff700001870000

def z150 : W := mkw 0x0226000002c00000 0x0089800000b00000 0x003e000000c00000 0x800f800000300000

def z151 : W := mkw 0x03ffbb7007daa6a8 0x00ffeedc01f6a9aa 0xfffffff807ffffff 0xfffffffe01ffffff

def z152 : W := mkw 0x0000000208204810 0x8000000082081204 0x6402107e39e0c8ff 0xd900841f8e78323f

def z153 : W := mkw 0x0410d086282cc910 0xc10434218a0b3244 0x0401d006383cc001 0x010074018e0f3000

def z154 : W := mkw 0x022e013002c00228 0x008b804c00b0008a 0x003c000000000000 0x000f000000000000

def z155 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x6400107ff8a0c8ff 0x9900041ffe28323f

def z156 : W := mkw 0x0044000007daa000 0x0011000001f6a800 0x6c023c0007fff001 0xdb008f0001fffc00

def z157 : W := mkw 0x0111b800001aa000 0x00446e000006a800 0x0401fc00003ff001 0x01007f00000ffc00

def z158 : W := mkw 0x133bbd38b0000000 0x04ceef4e2c000000 0xd3fffc3838000001 0xf4ffff0e0e000000

def z159 : W := mkw 0x0080024000000480 0x0020009000000120 0x000003c000000fc2 0x000000f0000003f0

def z160 : W := mkw 0x80000408d0011046 0x2000010234004411 0x00000059c00000cc 0x0000001670000033

def z161 : W := mkw 0x93fffffffffbf856 0xa4fffffffffefe15 0xfffffffffffff8ff 0xfffffffffffffe3f

def z162 : W := mkw 0x1bbbfffff0250dc3 0x06eefffffc094370 0xd3fffffff8000fc3 0xf4fffffffe0003f0

def z163 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfc038006000700 0x26ff00e0018001c0

def z164 : W := mkw 0x0000000240210842 0x0000000090084210 0x00000047c00008c2 0x00000011f0000230

def z165 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0xf3fe03f801c008fe 0xfcff80fe0070023f

def z166 : W := mkw 0x8088077ad8215efe 0xa02201deb60857bf 0x000003fff8000ffe 0x000000fffe0003ff

def z167 : W := mkw 0x0000000000000000 0x0000000000000000 0x40023c0000000001 0xd0008f0000000000

def z168 : W := mkw 0x022e013002c00228 0x008b804c00b0008a 0x603e007801c008fe 0xd80f801e0070023f

def z169 : W := mkw 0x0008012000000220 0x0002004800000088 0x000003a000000f32 0x000000e8000003cc

def z170 : W := mkw 0x04000002082cc910 0xc1000000820b3244 0x04000000003cc000 0x01000000000f3000

def z171 : W := mkw 0x06bed3f62aaccb30 0xc1afb4fd8aab32cc 0xffffd3fe3ebccf33 0xfffff4ff8faf33cc

def z172 : W := mkw 0x13e32e5995400488 0x04f8cb9665500122 0x13c22c59c14000cc 0x44f08b1670500033

def z173 : W := mkw 0x01c162c505000480 0x007058b141400120 0xfbc1e3c7c7000fc3 0x7ef078f1f1c003f0

def z174 : W := mkw 0x8044040adfe15efe 0xa0110102b7f857bf 0x6c023c7fffe3ffff 0xdb008f1ffff8ffff

def z175 : W := mkw 0x0beb63f745370dc3 0x02fad8fdd14dc370 0xffffe3ffc73f0fc3 0xfffff8fff1cfc3f0

def z176 : W := mkw 0x06ee43f62fe44fb8 0xc1bb90fd8bf913ee 0xfbfe03fe3fc00ffe 0xfeff80ff8ff003ff

def z177 : W := mkw 0x001490020aa8c810 0x8005240082aa3204 0xec3dd0263ebcc833 0xbb0f74098faf320c

def z178 : W := mkw 0x041cd5aebaaccb30 0xc107356baeab32cc 0xec3ffffffebccf33 0xfb0fffffffaf33cc

def z179 : W := mkw 0x0b77f88747ffa943 0x02ddfe21d1ffea50 0xfffffc07c7fff001 0xffffff01f1fffc00

def z180 : W := mkw 0x89c166cfd5371dc7 0x227059b3f54dc771 0xffc3efdfc77f3fcf 0x7ff0fbf7f1dfcff3

def z181 : W := mkw 0x0337b80002daa000 0x00cdee0000b6a800 0x043ffc0000fff001 0x810fff00003ffc00

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x00021c0000c0f000 0x8000870000303c00

def z183 : W := mkw 0x8000040898005014 0xa000010226001405 0x64023c3839e3f03d 0xd9008f0e0e78fc0f

def z184 : W := mkw 0x8000040890001004 0x2000010224000401 0x00020c180040300c 0x0000830600100c03

def z185 : W := mkw 0x0018d1a420000000 0x0006346908000000 0x803dc38000000000 0x200f70e000000000

def z186 : W := mkw 0x0dddf3e767bf8fe3 0x43777cf9d9efe3f8 0xfffde3c7c73f0fc3 0x7fff78f1f1cfc3f0

def z187 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x64023c07f9e3f001 0xd9008f01fe78fc00

def z188 : W := mkw 0x82e20658d54114ce 0x20b8819635504533 0x13c22c59c14330cc 0x44f08b167050cc33

def z189 : W := mkw 0x12aa47fdb0000000 0x04aa91ff6c000000 0xd3fe03fff8000002 0xf4ff80fffe000000

def z190 : W := mkw 0x0151b800051aa000 0x00546e000146a800 0xffc1fc00073ff001 0x7ff07f0001cffc00

def z191 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x24003c07f9e3f8fd 0x09000f01fe78fe3f

def z192 : W := mkw 0x0000000240210842 0x0000000090084210 0x64023c47c1e3f8c3 0xd9008f11f078fe30

def z193 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x6400207ff92308ff 0x5900081ffe48c23f

def z194 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9bc1c3c7c61c0fc2 0x26f070f1f18703f0

def z195 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x13fe007801c000fc 0xc4ff801e0070003f

def z196 : W := mkw 0x10109c08b0000000 0x040427022c000000 0x00001c0038000000 0x000007000e000000

def z197 : W := mkw 0x89c166cfdd375dd7 0xa27059b3f74dd775 0xffc1e3ffff3f0fff 0x7ff078ffffcfc3ff

def z198 : W := mkw 0x13fffbf527daa000 0x04fffefd49f6a800 0xffffff8007fff001 0xffffffe001fffc00

def z199 : W := mkw 0x148847ffb8244b30 0xc52211ffee0912cc 0x000003fff8000f32 0x000000fffe0003cc

def z200 : W := mkw 0x13a32a5100000000 0x04e8ca9440000000 0x13c0000000000000 0x04f0000000000000

def z201 : W := mkw 0x0014900002888000 0x0005240000a22000 0x003c10000080c000 0x800f040000203000

def z202 : W := mkw 0x93a32e59d0011046 0x24e8cb9674004411 0x13c22c59c14330cc 0x44f08b167050cc33

def z203 : W := mkw 0x041c91202a88c230 0xc10724480aa2308c 0xec3dd0203ebcc031 0xbb0f74080faf300c

def z204 : W := mkw 0x13bffffdb2800220 0x04efffff6ca00088 0xfbfffffffe800f33 0xfeffffffffa003cc

def z205 : W := mkw 0x04dcd3e62faccfb0 0xc13734f98beb33ec 0xfffdd3e63fbccff3 0xffff74f98fef33fc

def z206 : W := mkw 0x8000040898005014 0xa000010226001405 0x60021c7839c0f8fe 0xd800871e0e703e3f

def z207 : W := mkw 0x108847fdb00006a8 0x042211ff6c0001aa 0x000003fff8000ffe 0x000000fffe0003ff

def z208 : W := mkw 0x13bffffdb2888000 0x04efffff6ca22000 0xfffffffffebcc003 0xffffffffffaf3000

def z209 : W := mkw 0x023e993002c8a228 0x008fa64c00b2288a 0x003e1c3800c0f03c 0x800f870e00303c0f

def z210 : W := mkw 0x17bffffdba88c230 0xc5efffff6ea2308c 0xd3fffffff880c033 0xf4fffffffe20300c

def z211 : W := mkw 0x09c162c705360d81 0x027058b1c14d8360 0xffc1c386063c0f03 0x3ff070e1818f03c0

def z212 : W := mkw 0x0141200005120000 0x0050480001448000 0xffc1e000073f0001 0x7ff0780001cfc000

def z213 : W := mkw 0x018162c740210842 0x006058b1d0084210 0xf7c1e3c7c12308c3 0x7df078f1f048c230

def z214 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xdbfffc00061c0001 0xf6ffff0001870000

def z215 : W := mkw 0x13bffffdb2c00228 0x04efffff6cb0008a 0xd3fffffff8c0003f 0xf4fffffffe30000f

def z216 : W := mkw 0x804400024ffbf856 0xa011000093fefe15 0x2c00000007fff8fc 0x0b00000001fffe3f

def z217 : W := mkw 0x8377bc0adffbf856 0xa0ddef02b7fefe15 0xfffffc7ffffff8ff 0xffffff1ffffffe3f

def z218 : W := mkw 0x1bfffffff7ffadc3 0x06fffffffdffeb70 0xffffffffffffffc3 0xfffffffffffffff0

def z219 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x883dc3a63e1c0f32 0x220f70e98f8703cc

def z220 : W := mkw 0x0bef63f507d607a9 0x02fbd8fd41f581ea 0xfbffc3f807dc0ffe 0xfefff0fe01f703ff

def z221 : W := mkw 0x0bef63f747f70feb 0x02fbd8fdd1fdc3fa 0xfffde3c7c73f0fc3 0x7fff78f1f1cfc3f0

def z222 : W := mkw 0x0bf7fac747ffadc3 0x02fdfeb1d1ffeb70 0xffffffc7c7ffffc3 0xfffffff1f1fffff0

def z223 : W := mkw 0x0145200007daa000 0x0051480001f6a800 0xffc1e00007fff001 0x7ff0780001fffc00

def z224 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xbffdc00007fff000 0x2fff700001fffc00

def z225 : W := mkw 0x09c162c505160581 0x027058b141458160 0xdbc1e3c7c61c0703 0x76f078f1f18701c0

def z226 : W := mkw 0x0511f886283ee910 0xc1447e218a0fba44 0x0401fc06383ff001 0x01007f018e0ffc00

def z227 : W := mkw 0x045cd1a62ffeeb30 0xc11734698bffbacc 0xec3dd3a63fffff33 0xbb0f74e98fffffcc

def z228 : W := mkw 0x0363280005522000 0x00d8ca0001548800 0xffc3ec00077f3001 0x7ff0fb0001dfcc00

def z229 : W := mkw 0x8111bc0ad83bf856 0xa0446f02b60efe15 0x6403fc7ff9fff8ff 0xd900ff1ffe7ffe3f

def z230 : W := mkw 0x026e013007c006a8 0x009b804c01f001aa 0x283e003807c00ffc 0x8a0f800e01f003ff

def z231 : W := mkw 0x0901608740370943 0x02405821d00dc250 0x0401e007c03f0001 0x01007801f00fc000

def z232 : W := mkw 0x0101200000000000 0x0040480000000000 0xd3c1e00000000001 0x74f0780000000000

def z233 : W := mkw 0x0bf3fac745370dc3 0x02fcfeb1d14dc370 0xffffffc7c73f0fc3 0xfffffff1f1cfc3f0

def z234 : W := mkw 0x8018d5aef8215856 0xa006356bbe085615 0xe43ffffff9e3f8ff 0xf90ffffffe78fe3f

def z235 : W := mkw 0x93bbfffdb8005014 0xa4eeffff6e001405 0xd3fffffff8c0f03f 0xf4fffffffe303c0f

def z236 : W := mkw 0x11012c0990000000 0x04404b0264000000 0x00002c01c0000000 0x00000b0070000000

def z237 : W := mkw 0x041c91222aaccb30 0xc10724488aab32cc 0x2c3c10203ebccf30 0x8b0f04080faf33cc

def z238 : W := mkw 0x8901648fd8375957 0xa2405923f60dd655 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z239 : W := mkw 0x01c162c505120000 0x007058b141448000 0xffc1e3c7c73f0003 0x7ff078f1f1cfc000

def z240 : W := mkw 0x0040000005000000 0x0010000001400000 0xfbc0000007000000 0x7ef0000001c00000

def z241 : W := mkw 0x063e91302ac8c238 0xc18fa44c0ab2308e 0x003e103838c0c03c 0x800f840e0e30300f

def z242 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x04003c07f823f001 0x01000f01fe08fc00

def z243 : W := mkw 0x1199fffdb0000000 0x04667fff6c000000 0x0001fffff8000003 0x00007ffffe000000

def z244 : W := mkw 0x0000408600240900 0x0000102180090240 0x0401c006003c0001 0x01007001800f0000

def z245 : W := mkw 0x00cc037007c006a8 0x003300dc01f001aa 0x280003f807c00ffe 0x0a0000fe01f003ff

def z246 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf7fffffff9e3f003 0xfdfffffffe78fc00

def z247 : W := mkw 0x8000000248215856 0xa000000092085615 0x6400102639e3f8ff 0x990004098e78fe3f

def z248 : W := mkw 0x088843f740250feb 0x022210fdd00943fa 0x000003ffc0000ffe 0x000000fff00003ff

def z249 : W := mkw 0x08800241400104c3 0x0220009050004130 0x00000041c00000c0 0x0000001070000030

def z250 : W := mkw 0x0941200245370dc3 0x02504800914dc370 0xffc1e000073f0fc1 0x7ff0780001cfc3f0

def z251 : W := mkw 0x004c012007c006a8 0x0013004801f001aa 0xe83c03a007c00ffe 0xba0f00e801f003ff

def z252 : W := mkw 0x06fed3f62feccfb8 0xc1bfb4fd8bfb33ee 0xfffdd3a63ebccf33 0xbfff74e98faf33cc

def z253 : W := mkw 0x02e6025007c006a8 0x00b9809401f001aa 0x3bc2005807c00ffc 0x4ef0801601f003ff

def z254 : W := mkw 0x0000040890000000 0x0000010224000000 0x0000007ff8000002 0x0000001ffe000000

def z255 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x8c3dd3863e3cc701 0x230f74e18f8f31c0

def z256 : W := mkw 0x83632c0add737856 0xa0d8cb02b75cde15 0x77c23c7ff9e3f8ff 0xddf08f1ffe78fe3f

def z257 : W := mkw 0x0014d08602ac8900 0x0005342180ab2240 0xec3dd38606bccf03 0xbb0f74e181af33c0

def z258 : W := mkw 0x0266000007c006a8 0x0099800001f001aa 0xfbfe000007c00ffc 0xfeff800001f003ff

def z259 : W := mkw 0x06ee03720feccfb8 0xc1bb80dc83fb33ee 0xfffe03f807fccffe 0xffff80fe01ff33ff

def z260 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0x93fdc38000000000 0x24ff70e000000000

def z261 : W := mkw 0x82ee07789fc056bc 0xa0bb81de27f015af 0xfbfe1ff83fc0fffe 0xfeff87fe0ff03fff

def z262 : W := mkw 0x0018d1a628204810 0x800634698a081204 0xe43dd3a638a0c833 0xb90f74e98e28320c

def z263 : W := mkw 0x923a9d38b8005014 0xa48ea74e2e001405 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z264 : W := mkw 0x040c01220aaccb30 0xc103004882ab32cc 0xec3c03a006bccf32 0xbb0f00e801af33cc

def z265 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfbffc00007dc0000 0xfefff00001f70000

def z266 : W := mkw 0x040c41a62aaccb30 0xc10310698aab32cc 0x2c0003a63ebccf32 0x0b0000e98faf33cc

def z267 : W := mkw 0x13bbfffff0210842 0x04eefffffc084210 0xf7fffffff92308c3 0xfdfffffffe48c230

def z268 : W := mkw 0x0be762c747f70dc3 0x02f9d8b1d1fdc370 0xffffe3c7c7ff0fc3 0xfffff8f1f1ffc3f0

def z269 : W := mkw 0x8901648fd8375957 0xa2405923f60dd655 0x6403fc7ff9fff8ff 0xd900ff1ffe7ffe3f

def z270 : W := mkw 0x13fffffdb7daa000 0x04ffffff6df6a800 0xfffffffffffff003 0xfffffffffffffc00

def z271 : W := mkw 0x93bbfffff8215856 0xa4eefffffe085615 0xd3fffffff80008ff 0xf4fffffffe00023f

def z272 : W := mkw 0x888046cfd8255dd7 0xa22011b3f6095775 0x000003fff8000ffe 0x000000fffe0003ff

def z273 : W := mkw 0x044400020ffeeb30 0xc111000083ffbacc 0x2c00000007ffff30 0x0b00000001ffffcc

def z274 : W := mkw 0x822e053adae15a7e 0xa08b814eb6b8569f 0x643e3c7ff9e3f8ff 0xd90f8f1ffe78fe3f

def z275 : W := mkw 0x00c4024007c006a8 0x0031009001f001aa 0xfbc003c007c00ffe 0x7ef000f001f003ff

def z276 : W := mkw 0x0266000007c00000 0x0099800001f00000 0x9bfc000006000000 0x26ff000001800000

def z277 : W := mkw 0x17ffffffbfeccfb8 0xc5ffffffeffb33ee 0xfffffffffffccfff 0xffffffffffff33ff

def z278 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x44023c7ff823f003 0xd1008f1ffe08fc00

def z279 : W := mkw 0x8000000248215856 0xa000000092085615 0x64002047c1e3f8ff 0x59000811f078fe3f

def z280 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x0000038000000700 0x000000e0000001c0

def z281 : W := mkw 0x09c12241451304c3 0x027048905144c130 0xfbc023c1c7030fc2 0x7ef008f071c0c3f0

def z282 : W := mkw 0x0000040890000000 0x0000010224000000 0x64023c7ff9e3f003 0xd9008f1ffe78fc00

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z284 : W := mkw 0x02e2025005400488 0x00b8809401500122 0x13c20058014000cc 0x44f0801600500033

def z285 : W := mkw 0x0418d1a6282ccb30 0xc10634698a0b32cc 0x0401d3a6383ccf33 0x010074e98e0f33cc

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0x00022c0001433000 0x40008b000050cc00

def z287 : W := mkw 0x040440860aaccb30 0xc101102182ab32cc 0xec01c38606bccf33 0x3b0070e181af33cc

def z288 : W := mkw 0x0266000007c00000 0x0099800001f00000 0xfbfe007807c008fe 0xfeff801e01f0023f

def z289 : W := mkw 0x0000000008004010 0x8000000002001004 0x000010203880c030 0x800004080e20300c

def z290 : W := mkw 0x0414d0862aacc910 0xc10534218aab3244 0xec3dd0063ebcc001 0xbb0f74018faf3000

def z291 : W := mkw 0x0000040890000000 0x0000010224000000 0x00003c07f8000001 0x00000f01fe000000

def z292 : W := mkw 0x000841a420000000 0x0002106908000000 0x000003a638000002 0x000000e98e000000

def z293 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc1f3e7ffbfcff3 0xfff07cf9ffeff3fc

def z294 : W := mkw 0x13bbfffdb01aa000 0x04eeffff6c06a800 0xd7fffffff83ff003 0xf5fffffffe0ffc00

def z295 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x6002007ff9c008fe 0xd800801ffe70023f

def z296 : W := mkw 0x022a013000000000 0x008a804c00000000 0x003e003800000000 0x800f800e00000000

def z297 : W := mkw 0x0266000007c00000 0x0099800001f00000 0xfffe3c0007e3f001 0xffff8f0001f8fc00

def z298 : W := mkw 0x0000000248214852 0x8000000092085214 0x64003067f9a3c8f3 0xd9000c19fe68f23c

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x6002000001c00000 0xd800800000700000

def z300 : W := mkw 0x000c41a602a40b20 0x0003106980a902c8 0xec3dc3a606bc0f33 0xbb0f70e981af03cc

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400100000a0c001 0x9900040000283000

def z302 : W := mkw 0x12badffdb0000000 0x04aeb7ff6c000000 0x003e1ffff8000002 0x800f87fffe000000

def z303 : W := mkw 0x0367280007daa000 0x00d9ca0001f6a800 0x3fc22c0007fff000 0x4ff08b0001fffc00

def z304 : W := mkw 0x923a9d3af8215856 0xa48ea74ebe085615 0x643e3c7ff9e3f8ff 0xd90f8f1ffe78fe3f

def z305 : W := mkw 0x0004000002800220 0x0001000000a00088 0x2800000006800f30 0x0a00000001a003cc

def z306 : W := mkw 0x13fbfffdb5522000 0x04feffff6d548800 0xd3fffffff9433003 0xf4fffffffe50cc00

def z307 : W := mkw 0x0000040890000000 0x0000010224000000 0x00021c3838000000 0x8000870e0e000000

def z308 : W := mkw 0x08c042c745250dc3 0x023010b1d1494370 0xfbc003c7c7000fc2 0x7ef000f1f1c003f0

def z309 : W := mkw 0x1bfbfffdb5160581 0x06feffff6d458160 0xdbfffffffe1c0703 0xf6ffffffff8701c0

def z310 : W := mkw 0x0088037000000000 0x002200dc00000000 0x000003f800000002 0x000000fe00000000

def z311 : W := mkw 0x13bbfffdb00006a8 0x04eeffff6c0001aa 0xd3fffffff8000fff 0xf4fffffffe0003ff

def z312 : W := mkw 0x0266000007daa000 0x0099800001f6a800 0xfffe000007fff000 0xffff800001fffc00

def z313 : W := mkw 0x03ef237007d206a8 0x00fbc8dc01f481aa 0xffffe3f807ff0fff 0xfffff8fe01ffc3ff

def z314 : W := mkw 0x1111fc8db01aa000 0x04447f236c06a800 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z315 : W := mkw 0x8000000248215856 0xa000000092085615 0x00000000000008fc 0x000000000000023f

def z316 : W := mkw 0x0840408645370dc3 0x02101021914dc370 0xec01c386073f0fc3 0x3b0070e181cfc3f0

def z317 : W := mkw 0x12fe9f78b7c006a8 0x04bfa7de2df001aa 0xfbfe1ff83fc00ffe 0xfeff87fe0ff003ff

def z318 : W := mkw 0x0000040ad0210842 0x00000102b4084210 0x64023c7ff92308c3 0xd9008f1ffe48c230

def z319 : W := mkw 0x0008012000000000 0x0002004800000000 0xc03c03a000000002 0xb00f00e800000000

def z320 : W := mkw 0x0be32251455304cb 0x02f8c8945154c132 0x13c22059c14300cc 0x44f088167050c033

def z321 : W := mkw 0x0363280005522000 0x00d8ca0001548800 0x13c0000000000000 0x04f0000000000000

def z322 : W := mkw 0x13ef2f7997c006a8 0x04fbcbde65f001aa 0xfbfe2ff9c7c00ffe 0xfeff8bfe71f003ff

def z323 : W := mkw 0x02a2025000000000 0x00a8809400000000 0x13c2005800000000 0x44f0801600000000

def z324 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3dd3a63fffffff 0xbb0f74e98fffffff

def z325 : W := mkw 0x804400024fe15efe 0xa011000093f857bf 0x2c00000007e3fffc 0x0b00000001f8ffff

def z326 : W := mkw 0x1fffffffffbfcff3 0xc7ffffffffeff3fc 0xffffffffffbfcff3 0xffffffffffeff3fc

def z327 : W := mkw 0x8410d48ef82dd956 0xe1043523be0b7655 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z328 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0xf7fffc0001e3f001 0xfdffff000078fc00

def z329 : W := mkw 0x0222000000000000 0x0088800000000000 0xd3fe000000000000 0xf4ff800000000000

def z330 : W := mkw 0x077ff9a62ffeeb30 0xc1dffe698bffbacc 0xfffdd3a63ebccf33 0xbfff74e98faf33cc

def z331 : W := mkw 0x1bfffffff7f70feb 0x06fffffffdfdc3fa 0xffffffffffff0fff 0xffffffffffffc3ff

def z332 : W := mkw 0x02ae037002c006a8 0x00ab80dc00b001aa 0x003e03f800c00ffe 0x800f80fe003003ff

def z333 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93fdc3fff8000002 0x24ff70fffe000000

def z334 : W := mkw 0x02aa077890000000 0x00aa81de24000000 0xd3fe3ffff8000003 0xf4ff8ffffe000000

def z335 : W := mkw 0x8014940adaa9d856 0xa0052502b6aa7615 0xec3ffc7ffffff8ff 0xfb0fff1ffffffe3f

def z336 : W := mkw 0x0236980002c8a000 0x008da60000b22800 0x003e1c0000c0f000 0x800f870000303c00

def z337 : W := mkw 0x0101608500000000 0x0040582140000000 0x0001e007c0000001 0x00007801f0000000

def z338 : W := mkw 0x0377b80007daa6a8 0x00ddee0001f6a9aa 0xfffffc0007fffffd 0xffffff0001ffffff

def z339 : W := mkw 0x1000448db0000000 0x040011236c000000 0x00000007f8000000 0x00000001fe000000

def z340 : W := mkw 0x163e9d38ba88c230 0xc58fa74e2ea2308c 0x003e1c383880c030 0x800f870e0e20300c

def z341 : W := mkw 0x059df3e72aaccb30 0xc1677cf9caab32cc 0xfffdf3e7febccf33 0xffff7cf9ffaf33cc

def z342 : W := mkw 0x8000040898005014 0xa000010226001405 0x40023c7ff8c0f03f 0xd0008f1ffe303c0f

def z343 : W := mkw 0x000c012002800220 0x0003004800a00088 0xe83c03a006800f32 0xba0f00e801a003cc

def z344 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x04023c5ff963f0cd 0x41008f17fe58fc33

def z345 : W := mkw 0x0080024000000000 0x0020009000000000 0xd3c003c000000002 0x74f000f000000000

def z346 : W := mkw 0x0000000208204810 0x8000000082081204 0x0000002638000832 0x000000098e00020c

def z347 : W := mkw 0x1111f88520000000 0x04447e2148000000 0x0001c00000000000 0x0000700000000000

def z348 : W := mkw 0x163eddbebaaccb30 0xc58fb76faeab32cc 0xec3fdfbe3ebccf33 0xbb0ff7ef8faf33cc

def z349 : W := mkw 0x0377bc0897daa000 0x00ddef0225f6a800 0xfffffc7ffffff003 0xffffff1ffffffc00

def z350 : W := mkw 0x0be362d745770dcb 0x02f8d8b5d15dc372 0xffc3e3dfc77f0fcf 0x7ff0f8f7f1dfc3f3

def z351 : W := mkw 0x93bbfffff8215856 0xa4eefffffe085615 0xd7fffffff823f003 0xf5fffffffe08fc00

def z352 : W := mkw 0x09d9f3e765370dc3 0x02767cf9d94dc370 0xfffdf3e7ff3f0fc3 0xffff7cf9ffcfc3f0

def z353 : W := mkw 0x1511fc8fb82cc910 0xc5447f23ee0b3244 0x0401fc07f83cc001 0x01007f01fe0f3000

def z354 : W := mkw 0x8410d48ef82dd956 0xe1043523be0b7655 0x6403fc7ff9fff8ff 0xd900ff1ffe7ffe3f

def z355 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x13c023c7c1030fc2 0x44f008f1f040c3f0

def z356 : W := mkw 0x0000000200200800 0x0000000080080200 0x6400000600200803 0x1900000180080200

def z357 : W := mkw 0x067ed1a62feccb30 0xc19fb4698bfb32cc 0xffffd3a63ffccf33 0xfffff4e98fff33cc

def z358 : W := mkw 0x02aa0370000006a8 0x00aa80dc000001aa 0xd3fe03f800000ffe 0xf4ff80fe000003ff

def z359 : W := mkw 0x1333fc8db0000000 0x04ccff236c000000 0xd3fffc07f8000001 0xf4ffff01fe000000

def z360 : W := mkw 0x09d1fac7453fadc3 0x02747eb1d14feb70 0xffc1ffc7c73fffc3 0x7ff07ff1f1cffff0

def z361 : W := mkw 0x02fe9b7007c8a6a8 0x00bfa6dc01f229aa 0xfbfe1ff807c0fffe 0xfeff87fe01f03fff

def z362 : W := mkw 0x02ee037007daa6a8 0x00bb80dc01f6a9aa 0xfffe03f807fffffe 0xffff80fe01ffffff

def z363 : W := mkw 0x17bffbf5228c8320 0x45effefd48a320c8 0x9bfdc380061c0700 0x26ff70e0018701c0

def z364 : W := mkw 0x137fbd38b7daa000 0x04dfef4e2df6a800 0xfffffc383ffff001 0xffffff0e0ffffc00

def z365 : W := mkw 0x03ffbb7007daa000 0x00ffeedc01f6a800 0xfffffff807fff003 0xfffffffe01fffc00

def z366 : W := mkw 0x0000000208204810 0x8000000082081204 0x64023c2639e3f833 0xd9008f098e78fe0c

def z367 : W := mkw 0x8000040a98205814 0xa0000102a6081605 0x64021c3e38e0f83f 0x9900870f8e383e0f

def z368 : W := mkw 0x19c967fff5370dc3 0x067259fffd4dc370 0xffc1e3ffff3f0fc3 0x7ff078ffffcfc3f0

def z369 : W := mkw 0x02ae037002800220 0x00ab80dc00a00088 0xfbfe03f806800f32 0xfeff80fe01a003cc

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0xe800038006000f02 0x3a0000e0018003c0

def z371 : W := mkw 0x93ffffffffe15efe 0xa4fffffffff857bf 0xffffffffffe3ffff 0xfffffffffff8ffff

def z372 : W := mkw 0x09c1224105120481 0x0270489041448120 0x13c0000000000000 0x04f0000000000000

def z373 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc1e3c7c7ffffff 0x7ff078f1f1ffffff

def z374 : W := mkw 0x0040000005400488 0x0010000001500122 0x00000000014000cc 0x0000000000500033

def z375 : W := mkw 0x0901608500160101 0x0240582140058040 0x0001c000001c0000 0x0000700000070000

def z376 : W := mkw 0x0bf7fac507dea581 0x02fdfeb141f7a960 0x9bfdc380061c0700 0x26ff70e0018701c0

def z377 : W := mkw 0x03bbbb7000000000 0x00eeeedc00000000 0xd3fffff800000003 0xf4fffffe00000000

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0xec01c000063c0001 0x3b007000018f0000

def z379 : W := mkw 0x0377b8020ffae810 0x80ddee0083feba04 0xfffffc263ffff833 0xffffff098ffffe0c

def z380 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0xd3fde3c7c0000003 0x74ff78f1f0000000

def z381 : W := mkw 0x13fffffdb7daa6a8 0x04ffffff6df6a9aa 0xffffffffffffffff 0xffffffffffffffff

def z382 : W := mkw 0x0115b800029aa000 0x00456e0000a6a800 0xec3dfc0006bff001 0xbb0f7f0001affc00

def z383 : W := mkw 0x03ab63f500000000 0x00ead8fd40000000 0xd3ffe3ffc0000003 0xf4fff8fff0000000

def z384 : W := mkw 0x123a993020000000 0x048ea64c08000000 0x003c000000000000 0x000f000000000000

def z385 : W := mkw 0x800c052adaa15a76 0xa003014ab6a8569d 0xec3e3fffffe3ffff 0xfb0f8ffffff8ffff

def z386 : W := mkw 0x00c0024005000480 0x0030009001400120 0x9bc0038006000700 0x26f000e0018001c0

def z387 : W := mkw 0x8000040898005014 0xa000010226001405 0x000000383800003c 0x0000000e0e00000f

def z388 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x00000007f8000000 0x00000001fe000000

def z389 : W := mkw 0x0367280007d22000 0x00d9ca0001f48800 0xfbfe2c0007c33000 0xfeff8b0001f0cc00

def z390 : W := mkw 0x1911fc8ff0370943 0x06447f23fc0dc250 0x0401fc07f83f0001 0x01007f01fe0fc000

def z391 : W := mkw 0x0276980007c8a000 0x009da60001f22800 0xfbfe1c0007c0f000 0xfeff870001f03c00

def z392 : W := mkw 0x001cd1a422800220 0x0007346908a00088 0xe83dd3a63e800f33 0xba0f74e98fa003cc

def z393 : W := mkw 0x0000000000000000 0x0000000000000000 0x6400200001230001 0x590008000048c000

def z394 : W := mkw 0x03f7fac507daa000 0x00fdfeb141f6a800 0xffffffc7c7fff003 0xfffffff1f1fffc00

def z395 : W := mkw 0x098162c740370943 0x026058b1d00dc250 0xd7c1e3c7c03f0003 0x75f078f1f00fc000

def z396 : W := mkw 0x00c0024245210cc2 0x0030009091484330 0xffc023c7c7230fc3 0x7ff008f1f1c8c3f0

def z397 : W := mkw 0x13fbfffdb5120000 0x04feffff6d448000 0xffffffffff3f0003 0xffffffffffcfc000

def z398 : W := mkw 0x0333b80000000000 0x00ccee0000000000 0x93fdc00000000000 0x24ff700000000000

def z399 : W := mkw 0x13fffbf527daa000 0x04fffefd49f6a800 0x9bfdc380061c0000 0x26ff70e001870000

def z400 : W := mkw 0x0000000040010042 0x0000000010004010 0x00002041c10300c0 0x400008107040c030

def z401 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc7807fff8ff 0xffffff1e01fffe3f

def z402 : W := mkw 0x0b77b80247ffadc3 0x02ddee0091ffeb70 0xfffffc0007ffffc1 0xffffff0001fffff0

def z403 : W := mkw 0x0044000007daa6a8 0x0011000001f6a9aa 0x2c00000007fffffc 0x0b00000001ffffff

def z404 : W := mkw 0x123e9d38b2c00228 0x048fa74e2cb0008a 0x003e1c3838c0003c 0x800f870e0e30000f

def z405 : W := mkw 0x840845aef8255b76 0xe102116bbe0956dd 0x64023ffff9e3ffff 0xd9008ffffe78ffff

def z406 : W := mkw 0x0363280005522000 0x00d8ca0001548800 0x77c23c0001e3f001 0xddf08f000078fc00

def z407 : W := mkw 0x0000408600240900 0x0000102180090240 0x0000038600000f02 0x000000e1800003c0

def z408 : W := mkw 0x00c80370050006a8 0x003200dc014001aa 0xfbc003f807000ffe 0x7ef000fe01c003ff

def z409 : W := mkw 0x0bef237147d306eb 0x02fbc8dc51f4c1ba 0xfbfe23f9c7c30ffe 0xfeff88fe71f0c3ff

def z410 : W := mkw 0x037ff9a427daa000 0x00dffe6909f6a800 0xffffffa63ffff003 0xffffffe98ffffc00

def z411 : W := mkw 0x0840000245370dc3 0x02100000914dc370 0x6c002047c73f0fc3 0x5b000811f1cfc3f0

def z412 : W := mkw 0x040c41a62aa44b30 0xc10310698aa912cc 0xe83c03a63e800f32 0xba0f00e98fa003cc

def z413 : W := mkw 0x03ffbb7007daa6a8 0x00ffeedc01f6a9aa 0xffffff8007fff701 0xffffffe001fffdc0

def z414 : W := mkw 0x063e99202ac8e230 0xc18fa6480ab2388c 0x003e1c2038c0f030 0x800f87080e303c0c

def z415 : W := mkw 0x03b3fac500000000 0x00ecfeb140000000 0xd3ffffc7c0000003 0xf4fffff1f0000000

def z416 : W := mkw 0x00000000000006a8 0x00000000000001aa 0x0000000000000ffc 0x00000000000003ff

def z417 : W := mkw 0x13fffbf527c006a8 0x04fffefd49f001aa 0x9bfdc38006000700 0x26ff70e0018001c0

def z418 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fffa63fffff33 0xfb0fffe98fffffcc

def z419 : W := mkw 0x09c1224345370dc3 0x02704890d14dc370 0x3fc02041c73f0fc0 0x4ff0081071cfc3f0

def z420 : W := mkw 0x13a32e5990000000 0x04e8cb9664000000 0x53c23c7ff8000003 0xd4f08f1ffe000000

def z421 : W := mkw 0x0408012028004230 0xc10200480a00108c 0x0000002038000030 0x000000080e00000c

def z422 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3df3e7ffbfcff3 0xfb0f7cf9ffeff3fc

def z423 : W := mkw 0x1bfbfbf765370dc3 0x06fefefdd94dc370 0xfffde3c7c73f0fc3 0x7fff78f1f1cfc3f0

def z424 : W := mkw 0x0901608740370943 0x02405821d00dc250 0xec01e387c63f0f03 0x3b0078e1f18fc3c0

def z425 : W := mkw 0x0377b80007c00000 0x00ddee0001f00000 0xfbfffc0007c00001 0xfeffff0001f00000

def z426 : W := mkw 0x108847fdb0000000 0x042211ff6c000000 0x40023ffff8000003 0xd0008ffffe000000

def z427 : W := mkw 0x06fe93702fc8c6b8 0xc1bfa4dc0bf231ae 0xfbfe13f83fc0cffe 0xfeff84fe0ff033ff

def z428 : W := mkw 0x123addbcb0000000 0x048eb76f2c000000 0xc03fdfbe38000003 0xb00ff7ef8e000000

def z429 : W := mkw 0x0004000002800000 0x0001000000a00000 0xe83c000006800000 0xba0f000001a00000

def z430 : W := mkw 0x0414d0862aaccb30 0xc10534218aab32cc 0x2c01d0063ebccf31 0x0b0074018faf33cc

def z431 : W := mkw 0x8141240add335856 0xa0504902b74cd615 0xffc3fc7ffffff8ff 0xfff0ff1ffffffe3f

def z432 : W := mkw 0x041490020aaccb30 0xc105240082ab32cc 0xec3dd00006bccf31 0xbb0f740001af33cc

def z433 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93fdff87f8000001 0x24ff7fe1fe000000

def z434 : W := mkw 0x80000408d0011046 0x2000010234004411 0x40023c7ff94330cf 0xd0008f1ffe50cc33

def z435 : W := mkw 0x041cd1a622ac8b20 0x4107346988ab22c8 0xec3dc386063c0f03 0x3b0f70e1818f03c0

def z436 : W := mkw 0x088042c500040581 0x022010b140010160 0x0000038000000700 0x000000e0000001c0

def z437 : W := mkw 0x13e32e5995522000 0x04f8cb9665548800 0x13c22c59c1433000 0x44f08b167050cc00

def z438 : W := mkw 0x89c166cfdd375dd7 0xa27059b3f74dd775 0xffc1ffc7ff3fffc3 0x7ff07ff1ffcffff0

def z439 : W := mkw 0x0bf7ba4147dba4c3 0x02fdee9051f6e930 0xfffffc41c7fff0c1 0xffffff1071fffc30

def z440 : W := mkw 0x02ea037005400488 0x00ba80dc01500122 0xd3fe03f8014000ce 0xf4ff80fe00500033

def z441 : W := mkw 0x877ffdaefffffb76 0xe1dfff6bbffffedd 0xffffffffffffffff 0xffffffffffffffff

def z442 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfc03f806000ffe 0x26ff00fe018003ff

def z443 : W := mkw 0x818166cfd8215856 0xa06059b3f6085615 0xf7c3fffff9e3f8ff 0xfdf0fffffe78fe3f

def z444 : W := mkw 0x0377b80247fba842 0x00ddee0091feea10 0xfffffc47c7fff8c3 0xffffff11f1fffe30

def z445 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffde000073f0001 0x7fff780001cfc000

def z446 : W := mkw 0x0000408400040100 0x0000102100010040 0x8801c380061c0700 0x220070e0018701c0

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000078000008fe 0x0000001e0000023f

def z448 : W := mkw 0x048843f628244fb8 0xc12210fd8a0913ee 0x000003fe38000ffe 0x000000ff8e0003ff

def z449 : W := mkw 0x06fed3f427cc87a8 0x41bfb4fd09f321ea 0x9bfdc380061c0700 0x26ff70e0018701c0

def z450 : W := mkw 0x0bf7fac747ffadc3 0x02fdfeb1d1ffeb70 0xfffde3c7c73f0fc3 0x7fff78f1f1cfc3f0

def z451 : W := mkw 0x0000408640250942 0x0000102190094250 0xec01e3c7c73f0fc3 0x7b0078f1f1cfc3f0

def z452 : W := mkw 0x908847fff8215856 0xa42211fffe085615 0x000003fff80008fe 0x000000fffe00023f

def z453 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x04003c7ff823f8ff 0x01000f1ffe08fe3f

def z454 : W := mkw 0x03ffbb7007daa6a8 0x00ffeedc01f6a9aa 0xfbffc3f807dc0ffe 0xfefff0fe01f703ff

def z455 : W := mkw 0x0000000000000000 0x0000000000000000 0x04003c000023f001 0x01000f000008fc00

def z456 : W := mkw 0x840400024aaddb76 0xe101000092ab76dd 0x2c00000007fffffc 0x0b00000001ffffff

def z457 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0xec3dd38006bcc701 0xbb0f74e001af31c0

def z458 : W := mkw 0x13b3feddb0000000 0x04ecffb76c000000 0x13c3fc5ff8000001 0x44f0ff17fe000000

def z459 : W := mkw 0x00880370000006a8 0x002200dc000001aa 0x600203f801c00ffe 0xd80080fe007003ff

def z460 : W := mkw 0x0000040890000000 0x0000010224000000 0x00022c59c0000000 0x40008b1670000000

def z461 : W := mkw 0x00000000001aa000 0x000000000006a800 0x04000000003ff000 0x01000000000ffc00

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x64023c7801e3f8ff 0xd9008f1e0078fe3f

def z463 : W := mkw 0x0323280000000000 0x00c8ca0000000000 0x13c22c0000000000 0x44f08b0000000000

def z464 : W := mkw 0x0941608745370943 0x02505821d14dc250 0xffc1e007c73f0001 0x7ff07801f1cfc000

def z465 : W := mkw 0x151dfdafbaaccb30 0xc5477f6beeab32cc 0xec3dffa7febccf33 0xbb0f7fe9ffaf33cc

def z466 : W := mkw 0x08c042c745370dc3 0x023010b1d14dc370 0x2c0003c7c73f0fc2 0x0b0000f1f1cfc3f0

def z467 : W := mkw 0x02ee03720fe04eb8 0x80bb80dc83f813ae 0xfffe13fe3fe0cfff 0xffff84ff8ff833ff

def z468 : W := mkw 0x0000040890000000 0x0000010224000000 0x60023c7ff9c008ff 0xd8008f1ffe70023f

def z469 : W := mkw 0x0141200005120000 0x0050480001448000 0x9bc1c000061c0000 0x26f0700001870000

def z470 : W := mkw 0x040841a628244b30 0xc10210698a0912cc 0x640013a638a0cf33 0x990004e98e2833cc

def z471 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9bffec00075f3000 0x66fffb0001d7cc00

def z472 : W := mkw 0x01c1224005120480 0x0070489001448120 0xffc1e3c0073f0fc3 0x7ff078f001cfc3f0

def z473 : W := mkw 0x13bbffffb0240900 0x04eeffffec090240 0xfffffffffe3c0f03 0xffffffffff8f03c0

def z474 : W := mkw 0x17bbffffb82cc910 0xc5eeffffee0b3244 0xd7fffffff83cc003 0xf5fffffffe0f3000

def z475 : W := mkw 0x17bbffffb8244b30 0xc5eeffffee0912cc 0xd3fffffff8000f33 0xf4fffffffe0003cc

def z476 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfc03a006800f32 0xbeff00e801a003cc

def z477 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9fc1e387c63f0701 0x27f078e1f18fc1c0

def z478 : W := mkw 0x0141200245330842 0x00504800914cc210 0xffc1e047c73f08c3 0x7ff07811f1cfc230

def z479 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xbfc1c380073f0fc0 0x2ff070e001cfc3f0

def z480 : W := mkw 0x09c166cfd5370dc3 0x027059b3f54dc370 0xffc3ffffff3f0fc3 0xfff0ffffffcfc3f0

def z481 : W := mkw 0x09d5f2c747bf8dc3 0x02757cb1d1efe370 0xfffdf3c7c7bfcfc3 0xffff7cf1f1eff3f0

def z482 : W := mkw 0x149cd7ffbaaccb30 0xc52735ffeeab32cc 0xec3dd3fffebccf33 0xbb0f74ffffaf33cc

def z483 : W := mkw 0x0373b800055aa000 0x00dcee000156a800 0x17c3fc00017ff001 0x45f0ff00005ffc00

def z484 : W := mkw 0x02fe937007c886a8 0x00bfa4dc01f221aa 0xffffd3f807fccfff 0xfffff4fe01ff33ff

def z485 : W := mkw 0x02e2025005400488 0x00b8809401500122 0xfbc203d807400fce 0x7ef080f601d003f3

def z486 : W := mkw 0x8404040adaaddb76 0xe1010102b6ab76dd 0x6c023c7fffffffff 0xdb008f1fffffffff

def z487 : W := mkw 0x0141200005120000 0x0050480001448000 0xffc3fc0007fff001 0xfff0ff0001fffc00

def z488 : W := mkw 0x13fffbf527c006a8 0x04fffefd49f001aa 0xfbffc3f807c00ffe 0xfefff0fe01f003ff

def z489 : W := mkw 0x0222080000402000 0x0088820000100800 0x00020c0000403000 0x0000830000100c00

def z490 : W := mkw 0x82ee0778d7c116ee 0x20bb81de35f045bb 0xfbfe2ff9c7c33ffe 0xfeff8bfe71f0cfff

def z491 : W := mkw 0x0400408628244910 0xc10010218a091244 0x0000000638000000 0x000000018e000000

def z492 : W := mkw 0x0800000240370943 0x02000000900dc250 0x04000000003f0000 0x01000000000fc000

def z493 : W := mkw 0x0000000200240900 0x0000000080090240 0x2c000000063c0f00 0x0b000000018f03c0

def z494 : W := mkw 0x03f7ba5007daa488 0x00fdee9401f6a922 0xfffffc5807fff0cd 0xffffff1601fffc33

def z495 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfc03c007000fc2 0x7eff00f001c003f0

def z496 : W := mkw 0x0010d08420000000 0x0004342108000000 0x0001d00638000001 0x000074018e000000

def z497 : W := mkw 0x077ff9a427dea320 0x41dffe6909f7a8c8 0x9bfdc380061c0700 0x26ff70e0018701c0

def z498 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfffe3ff807e3ffff 0xffff8ffe01f8ffff

def z499 : W := mkw 0x0155b000079a8000 0x00556c0001e6a000 0xfffdf00007bfc001 0xffff7c0001eff000

def z500 : W := mkw 0x1be32e59d51304c3 0x06f8cb967544c130 0x13c22c59c10300c0 0x44f08b167040c030

def z501 : W := mkw 0x0000408608244910 0x8000102182091244 0xec01d3a63ebccf33 0xbb0074e98faf33cc

def z502 : W := mkw 0x0236980002c8a000 0x008da60000b22800 0x003c000000000000 0x000f000000000000

def z503 : W := mkw 0x17bffbf72aaccb30 0xc5effefdcaab32cc 0xfffdd3a63ebccf33 0xbfff74e98faf33cc

def z504 : W := mkw 0x0ffffbe76fffeff3 0xc3fffef9dbfffbfc 0xffffffe7fffffff3 0xfffffff9fffffffc

def z505 : W := mkw 0x0054900007daa000 0x0015240001f6a800 0xec3dd00007fff001 0xbb0f740001fffc00

def z506 : W := mkw 0x8266040adfe15856 0xa0998102b7f85615 0xfffe3c7fffe3f8ff 0xffff8f1ffff8fe3f

def z507 : W := mkw 0x0236980002c8a000 0x008da60000b22800 0xec3fdc0006fcf001 0xbb0ff70001bf3c00

def z508 : W := mkw 0x09c162c5451304c3 0x027058b15144c130 0xd3c1e3c7c10300c3 0x74f078f1f040c030

def z509 : W := mkw 0x8088077ad8215efe 0xa02201deb60857bf 0x64023ffff9e3ffff 0xd9008ffffe78ffff

def z510 : W := mkw 0x0dd1f2c76d3fcdd3 0xc3747cb1db4ff374 0xffc1f3c7ff3fcfc3 0x7ff07cf1ffcff3f0

def z511 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x04023c3ff8e3f03d 0x81008f0ffe38fc0f

def z512 : W := mkw 0x1bbbfffff0370943 0x06eefffffc0dc250 0xd7fffffff83f0003 0xf5fffffffe0fc000

def z513 : W := mkw 0x17ffffffbffeeb30 0xc5ffffffefffbacc 0xffffffffffffff33 0xffffffffffffffcc

def z514 : W := mkw 0x13a36edd90000000 0x04e8dbb764000000 0xd3c3efdfc0000003 0x74f0fbf7f0000000

def z515 : W := mkw 0x0337b80002c8a000 0x00cdee0000b22800 0xd3fffc0000c0f001 0xf4ffff0000303c00

def z516 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffdfb838000000 0xa4fff7ee0e000000

def z517 : W := mkw 0x12220c1890000000 0x0488830624000000 0x00020c1800000000 0x0000830600000000

def z518 : W := mkw 0x0101280000122000 0x00404a0000048800 0x00002c0000033000 0x00000b000000cc00

def z519 : W := mkw 0x0367200007d20000 0x00d9c80001f48000 0xffffe00007ff0001 0xfffff80001ffc000

def z520 : W := mkw 0x0010900000000000 0x0004240000000000 0xc03dd00000000001 0xb00f740000000000

def z521 : W := mkw 0x841c9528ba88d234 0xe107254a2ea2348d 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z522 : W := mkw 0x0000040a98204810 0x80000102a6081204 0x64023c7ff8a0c833 0xd9008f1ffe28320c

def z523 : W := mkw 0x0236980002c8a000 0x008da60000b22800 0x643e3c0001e3f001 0xd90f8f000078fc00

def z524 : W := mkw 0x8377bc089fdaf014 0xa0ddef0227f6bc05 0xfffffc383ffff03d 0xffffff0e0ffffc0f

def z525 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x043dd02638bcc031 0x810f74098e2f300c

def z526 : W := mkw 0x1098d7fdb0000000 0x042635ff6c000000 0xc03dd3fff8000003 0xb00f74fffe000000

def z527 : W := mkw 0x0080025000000488 0x0020009400000122 0x00000058000000cc 0x0000001600000033

def z528 : W := mkw 0x0018912020000000 0x0006244808000000 0x003c102038000000 0x800f04080e000000

def z529 : W := mkw 0x840845aef8255b76 0xe102116bbe0956dd 0x000003fff8000ffe 0x000000fffe0003ff

def z530 : W := mkw 0x037fb92007daa220 0x00dfee4801f6a888 0xffffffa007ffff33 0xffffffe801ffffcc

def z531 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x00021c7ff8c0f8fe 0x8000871ffe303e3f

def z532 : W := mkw 0x001098000008a000 0x0004260000022800 0x00001c000000f000 0x0000070000003c00

def z533 : W := mkw 0x0901608740370943 0x02405821d00dc250 0x6401e047c13f08c3 0x59007811f04fc230

def z534 : W := mkw 0x0181224100000000 0x0060489040000000 0x13c02041c0000000 0x44f0081070000000

def z535 : W := mkw 0x13f7be5997daa000 0x04fdef9665f6a800 0xfffffc59c7fff001 0xffffff1671fffc00

def z536 : W := mkw 0x0008013000000228 0x0002004c0000008a 0x000000380000003c 0x0000000e0000000f

def z537 : W := mkw 0x041090002808c010 0xc10424000a023004 0x000010003800c000 0x000004000e003000

def z538 : W := mkw 0x1111fc8db0000000 0x04447f236c000000 0x4003fc7ff8000003 0xd000ff1ffe000000

def z539 : W := mkw 0x09c562c747ffadc3 0x027158b1d1ffeb70 0xffc1e3c7c7ffffc3 0x7ff078f1f1fffff0

def z540 : W := mkw 0x80000408d8015056 0xa000010236005415 0x00023c79f9c3f0fc 0xc0008f1e7e70fc3f

def z541 : W := mkw 0x040400020aaccb30 0xc101000082ab32cc 0x6c0010263ebccf33 0x9b0004098faf33cc

def z542 : W := mkw 0x0bfffbf747ffafeb 0x02fffefdd1ffebfa 0xffffffffc7ffffff 0xfffffffff1ffffff

def z543 : W := mkw 0x12ba9f78b0000000 0x04aea7de2c000000 0xd3fe1ff838000002 0xf4ff87fe0e000000

def z544 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3e3ffc7ff0fff 0xfff0f8fff1ffc3ff

def z545 : W := mkw 0x09c162c505160581 0x027058b141458160 0xfbc1c3c0071c0fc2 0x7ef070f001c703f0

def z546 : W := mkw 0x02e6025007c00488 0x00b9809401f00122 0xfbfe005807c000cc 0xfeff801601f00033

def z547 : W := mkw 0x188847fff0250dc3 0x062211fffc094370 0x000003fff8000fc2 0x000000fffe0003f0

def z548 : W := mkw 0x83ffbf7adffbfefe 0xa0ffefdeb7feffbf 0xffffffffffffffff 0xffffffffffffffff

def z549 : W := mkw 0x0044000007c006a8 0x0011000001f001aa 0x0800000006000700 0x02000000018001c0

def z550 : W := mkw 0x040841a628244b30 0xc10210698a0912cc 0xec01c3a63e3c0f33 0x3b0070e98f8f03cc

def z551 : W := mkw 0x0800000240250dc3 0x0200000090094370 0x0000000000000fc0 0x00000000000003f0

def z552 : W := mkw 0x13ab6ffdb0000000 0x04eadbff6c000000 0x13c22ffff8000002 0x44f08bfffe000000

def z553 : W := mkw 0x026e013007c00228 0x009b804c01f0008a 0xfbfe003807c0003c 0xfeff800e01f0000f

def z554 : W := mkw 0x073ff9a62aaccb30 0xc1cffe698aab32cc 0xffffffa63ebccf33 0xffffffe98faf33cc

def z555 : W := mkw 0x89c1264bdd335cd7 0xa2704992f74cd735 0x77c23c7ff9e3f8ff 0xddf08f1ffe78fe3f

def z556 : W := mkw 0x133bfdbdb0000000 0x04ceff6f6c000000 0x003ffc3ff8000001 0x800fff0ffe000000

def z557 : W := mkw 0x00c0024005000480 0x0030009001400120 0xfbc203f807c00ffe 0xfef080fe01f003ff

def z558 : W := mkw 0x018166cd90000000 0x006059b364000000 0xd3c3fffff8000003 0xf4f0fffffe000000

def z559 : W := mkw 0x063ed1b62aeccb38 0xc18fb46d8abb32ce 0xec3fd3be3efccf3f 0xbb0ff4ef8fbf33cf

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000001e3f000 0x090000000078fc00

def z561 : W := mkw 0x0044000007c006a8 0x0011000001f001aa 0x6802007807c00ffe 0xda00801e01f003ff

def z562 : W := mkw 0x02bad3f420000000 0x00aeb4fd08000000 0xd3ffd3fe38000003 0xf4fff4ff8e000000

def z563 : W := mkw 0x0004000002c8a000 0x0001000000b22800 0x0000000000c0f000 0x0000000000303c00

def z564 : W := mkw 0x8dddf7efffbfdff7 0xe3777dfbffeff7fd 0xffffffffffffffff 0xffffffffffffffff

def z565 : W := mkw 0x1bfbfffdf51304c3 0x06feffff7d44c130 0xd3fffffff90300c3 0xf4fffffffe40c030

def z566 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x00022c7ff94338fe 0x40008b1ffe50ce3f

def z567 : W := mkw 0x088042c740250dc3 0x022010b1d0094370 0xec01c3c7c63c0fc3 0x3b0070f1f18f03f0

def z568 : W := mkw 0x0aee43f747e50feb 0x02bb90fdd1f943fa 0xfbfe03ffc7c00ffe 0xfeff80fff1f003ff

def z569 : W := mkw 0x8377bc08d7dbb046 0x20ddef0235f6ec11 0xfffffc59c7fff0cd 0xffffff1671fffc33

def z570 : W := mkw 0x13fffffdb7c00000 0x04ffffff6df00000 0xfbffffffffc00003 0xfefffffffff00000

def z571 : W := mkw 0x8000000248215856 0xa000000092085615 0x040000000023f000 0x010000000008fc00

def z572 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x24021c3839e3f8fc 0x8900870e0e78fe3f

def z573 : W := mkw 0x0373b80005522000 0x00dcee0001548800 0xd3fffc0001433001 0xf4ffff000050cc00

def z574 : W := mkw 0x0410d086282cc910 0xc10434218a0b3244 0x6401d02638bcc833 0x990074098e2f320c

def z575 : W := mkw 0x00cc0360078006a0 0x003300d801e001a8 0xfbfc03e007800ff2 0xfeff00f801e003fc

def z576 : W := mkw 0x0004000002c00228 0x0001000000b0008a 0x0000000000c0003c 0x000000000030000f

def z577 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xbbfc038007c00ffc 0x2eff00e001f003ff

def z578 : W := mkw 0x13ab2f7990000000 0x04eacbde64000000 0xd3fe2ff9c0000002 0xf4ff8bfe70000000

def z579 : W := mkw 0x008c0370028006a8 0x002300dc00a001aa 0xe83c03f806800ffe 0xba0f00fe01a003ff

def z580 : W := mkw 0x008042c500000000 0x002010b140000000 0x000003c7c0000002 0x000000f1f0000000

def z581 : W := mkw 0x8377b8024ffbf856 0xa0ddee0093fefe15 0xfffffc0007fff8fd 0xffffff0001fffe3f

def z582 : W := mkw 0x02ee037247e10eea 0x00bb80dc91f843ba 0xfffe23ffc7e30fff 0xffff88fff1f8c3ff

def z583 : W := mkw 0x09c12241451304c3 0x027048905144c130 0xffc1e041c73f00c1 0x7ff0781071cfc030

def z584 : W := mkw 0x8333bc0ad8215856 0xa0ccef02b6085615 0xf7fffc7ff9e3f8ff 0xfdffff1ffe78fe3f

def z585 : W := mkw 0x123a9d38b0000000 0x048ea74e2c000000 0x403e3c7ff8000003 0xd00f8f1ffe000000

def z586 : W := mkw 0x02e2025005400488 0x00b8809401500122 0x13c0000000000000 0x04f0000000000000

def z587 : W := mkw 0x045cd1a62feccfb8 0xc11734698bfb33ee 0xec3dd3a63ffccfff 0xbb0f74e98fff33ff

def z588 : W := mkw 0x0dddf3e5279e87a1 0x43777cf949e7a1e8 0x9bfdc380061c0700 0x26ff70e0018701c0

def z589 : W := mkw 0x03f7ba4007daa480 0x00fdee9001f6a920 0xffffffc007ffffc3 0xfffffff001fffff0

def z590 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x64003c47f923f8c3 0x59000f11fe48fe30

def z591 : W := mkw 0x0844000247ffadc3 0x0211000091ffeb70 0x2c00000007ffffc0 0x0b00000001fffff0

def z592 : W := mkw 0x0418d1a628244b30 0xc10634698a0912cc 0xc03dd3a638000f33 0xb00f74e98e0003cc

def z593 : W := mkw 0x0000000240210842 0x0000000090084210 0x24000000012308c0 0x090000000048c230

def z594 : W := mkw 0x8840040add375dd7 0xa2100102b74dd775 0x6c023c7fffffffff 0xdb008f1fffffffff

def z595 : W := mkw 0x12ee47fdb7c006a8 0x04bb91ff6df001aa 0xfbfe03ffffc00ffe 0xfeff80fffff003ff

def z596 : W := mkw 0x0337b80002888000 0x00cdee0000a22000 0xfffffc0006bcc001 0xffffff0001af3000

def z597 : W := mkw 0x049cd3f62aaccfb8 0xc12734fd8aab33ee 0xec3dd3fe3ebccfff 0xbb0f74ff8faf33ff

def z598 : W := mkw 0x000c012002800220 0x0003004800a00088 0x883c038006000700 0x220f00e0018001c0

def z599 : W := mkw 0x0410d084200c8100 0x4104342108032040 0x0001c000001c0000 0x0000700000070000

def z600 : W := mkw 0x02ee43f607e40fa8 0x00bb90fd81f903ea 0xffffc3fe07fc0fff 0xfffff0ff81ff03ff

def z601 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x24022c59c1e3f8fc 0x49008b167078fe3f

def z602 : W := mkw 0x1bfbfbf525160581 0x06fefefd49458160 0x9bfdc380061c0700 0x26ff70e0018701c0

def z603 : W := mkw 0x93bbfffdf0011046 0x24eeffff7c004411 0xd3fffffff94330cf 0xf4fffffffe50cc33

def z604 : W := mkw 0x888046cfd8255dd7 0xa22011b3f6095775 0x64023ffff9e3ffff 0xd9008ffffe78ffff

def z605 : W := mkw 0x02e2025005400488 0x00b8809401500122 0x73c2007801c008fe 0xdcf0801e0070023f

def z606 : W := mkw 0x098162c740370dc3 0x026058b1d00dc370 0x0401e3c7c03f0fc3 0x010078f1f00fc3f0

def z607 : W := mkw 0x841cd5aebaacdb34 0xe107356baeab36cd 0xec3fdfbe3efcff3f 0xbb0ff7ef8fbf3fcf

def z608 : W := mkw 0x0101200000120000 0x0040480000048000 0x0401e000003f0001 0x01007800000fc000

def z609 : W := mkw 0x841cd5aefaaddb76 0xe107356bbeab76dd 0xec3dffa7febfff33 0xbb0f7fe9ffafffcc

def z610 : W := mkw 0x098162c740250dc3 0x026058b1d0094370 0xd3c1e3c7c0000fc3 0x74f078f1f00003f0

def z611 : W := mkw 0x83632c08d5533046 0x20d8cb023554cc11 0x13c22c59c14330cc 0x44f08b167050cc33

def z612 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffdd00006bcc001 0xbfff740001af3000

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002047c0000003 0x50000811f0000000

def z614 : W := mkw 0x051df9a62abeeb30 0xc1477e698aafbacc 0xec3dffa63ebfff33 0xbb0f7fe98fafffcc

def z615 : W := mkw 0x0777f8862ffee910 0xc1ddfe218bffba44 0xfffffc063ffff001 0xffffff018ffffc00

def z616 : W := mkw 0x037fb93007daa228 0x00dfee4c01f6a88a 0xfffffc3807fff03d 0xffffff0e01fffc0f

def z617 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xdbfe03f806000702 0xf6ff80fe018001c0

def z618 : W := mkw 0x0d11f087683fc953 0xc3447c21da0ff254 0x0401f007f83fc001 0x01007c01fe0ff000

def z619 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xac3dc38006bccf30 0x2b0f70e001af33cc

def z620 : W := mkw 0x0262000005400000 0x0098800001500000 0x13c2000001400000 0x44f0800000500000

def z621 : W := mkw 0x0000000208204810 0x8000000082081204 0x040010063820c001 0x010004018e083000

def z622 : W := mkw 0x0040000005120000 0x0010000001448000 0x2c000000073f0000 0x0b00000001cfc000

def z623 : W := mkw 0x0377f88607fea900 0x00ddfe2181ffaa40 0xffffff8607ffff03 0xffffffe181ffffc0

def z624 : W := mkw 0x80000408d0011046 0x2000010234004411 0x00002c01c0033000 0x00000b007000cc00

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x4002007800000002 0xd000801e00000000

def z626 : W := mkw 0x8377bc0adffbf856 0xa0ddef02b7fefe15 0xfffffc07fffff001 0xffffff01fffffc00

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000102638000003 0x900004098e000000

def z628 : W := mkw 0x041c91202a88c230 0xc10724480aa2308c 0xe83c13a03e80cf32 0xba0f04e80fa033cc

def z629 : W := mkw 0x80000408d0011046 0x2000010234004411 0x64023c59c1e3f0cd 0xd9008f167078fc33

def z630 : W := mkw 0x08400000451304c3 0x021000001144c130 0x00000000010300c0 0x000000000040c030

def z631 : W := mkw 0x8000000008005014 0xa000000002001405 0x0000000000c0f03c 0x0000000000303c0f

def z632 : W := mkw 0x0222001000400008 0x0088800400100002 0x000200180040000c 0x0000800600100003

def z633 : W := mkw 0x123e9d38b2c8a000 0x048fa74e2cb22800 0x003e1c3838c0f000 0x800f870e0e303c00

def z634 : W := mkw 0x0010900000088000 0x0004240000022000 0x0401d000003cc001 0x01007400000f3000

def z635 : W := mkw 0x044400020feccfb8 0xc111000083fb33ee 0x2c00000007fccffc 0x0b00000001ff33ff

def z636 : W := mkw 0x1080065990000000 0x0420019664000000 0x00000059c0000000 0x0000001670000000

def z637 : W := mkw 0x0400000208244b30 0xc1000000820912cc 0x0000000000000f30 0x00000000000003cc

def z638 : W := mkw 0x8044040adffbf856 0xa0110102b7fefe15 0x6c023c7ffffff8ff 0xdb008f1ffffffe3f

def z639 : W := mkw 0x82ee03724fe15efe 0xa0bb80dc93f857bf 0xfffe03f807e3fffe 0xffff80fe01f8ffff

def z640 : W := mkw 0x8bf7fecfdffffdd7 0xa2fdffb3f7ffff75 0xffffffffffffffff 0xffffffffffffffff

def z641 : W := mkw 0x8000448ed8255956 0xa0001123b6095655 0xec03ffffffffffff 0xfb00ffffffffffff

def z642 : W := mkw 0x13bbffffb8204810 0x84eeffffee081204 0xf7fffffff8a0c833 0xfdfffffffe28320c

def z643 : W := mkw 0x02aa037000000000 0x00aa80dc00000000 0x93fc038000000000 0x24ff00e000000000

def z644 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x13fe3c0001c3f000 0xc4ff8f000070fc00

def z645 : W := mkw 0x09cd63e747b70fe3 0x027358f9d1edc3f8 0xfffde3e7c7bf0ff3 0xffff78f9f1efc3fc

def z646 : W := mkw 0x0276900007c88000 0x009da40001f22000 0xffffd00007fcc001 0xfffff40001ff3000

def z647 : W := mkw 0x02ae037002c00228 0x00ab80dc00b0008a 0xd3fe03f800c0003e 0xf4ff80fe0030000f

def z648 : W := mkw 0x06fed3f427cc87a8 0x41bfb4fd09f321ea 0xfbffc3f807dc0ffe 0xfefff0fe01f703ff

def z649 : W := mkw 0x8000000248215856 0xa000000092085615 0x6402007801e3f8fe 0xd900801e0078fe3f

def z650 : W := mkw 0x0c9cd3e76aadcff3 0xc32734f9daab73fc 0xec3dd3e7febccff3 0xbb0f74f9ffaf33fc

def z651 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x40023c7ff80008ff 0xd0008f1ffe00023f

def z652 : W := mkw 0x0000000208204810 0x8000000082081204 0x2400000000a0c830 0x090000000028320c

def z653 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9bffdc0006dcf000 0xa6fff70001b73c00

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000002000800832 0x980000080020020c

def z655 : W := mkw 0x0141200005120000 0x0050480001448000 0x13c0200001030000 0x44f008000040c000

def z656 : W := mkw 0x8000040ad0211846 0x20000102b4084611 0x64022c5fc16338cf 0x59008b17f058ce33

def z657 : W := mkw 0x82e2065add615cde 0xa0b88196b7585737 0x77c23c7ff9e3f8ff 0xddf08f1ffe78fe3f

def z658 : W := mkw 0x13b3be5990000000 0x04ecef9664000000 0xd3fffc59c0000001 0xf4ffff1670000000

def z659 : W := mkw 0x02fed3f427c006a8 0x00bfb4fd09f001aa 0xfbffd3fe3fc00fff 0xfefff4ff8ff003ff

def z660 : W := mkw 0x0373b80005120000 0x00dcee0001448000 0xfffffc00073f0001 0xffffff0001cfc000

def z661 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x17c1e047c13f00c1 0x45f07811f04fc030

def z662 : W := mkw 0x0dc562c74fbfcff3 0xc37158b1d3eff3fc 0xffc1e3c7c7bfcff3 0x7ff078f1f1eff3fc

def z663 : W := mkw 0x0040000005522000 0x0010000001548800 0x0000000001433000 0x000000000050cc00

def z664 : W := mkw 0x86fed7feffeddffe 0xe1bfb5ffbffb77ff 0xffffffffffffffff 0xffffffffffffffff

def z665 : W := mkw 0x040841a420040320 0x41021069080100c8 0x0000038000000700 0x000000e0000001c0

def z666 : W := mkw 0x02e6024007c00480 0x00b9809001f00120 0xfbfe03c007c00fc2 0xfeff80f001f003f0

def z667 : W := mkw 0x841cd5aefaaddb76 0xe107356bbeab76dd 0xec3dd3fffebccfff 0xbb0f74ffffaf33ff

def z668 : W := mkw 0x93a32e5bd8215856 0xa4e8cb96f6085615 0x77c23c7ff9e3f8ff 0xddf08f1ffe78fe3f

def z669 : W := mkw 0x9111fc8ff8215856 0xa4447f23fe085615 0x0401fc07f823f001 0x01007f01fe08fc00

def z670 : W := mkw 0x1be36edfd5370dc3 0x06f8dbb7f54dc370 0xffc3efdfc73f0fc3 0x7ff0fbf7f1cfc3f0

def z671 : W := mkw 0x0aee037247f70feb 0x02bb80dc91fdc3fa 0xfffe03f807ff0ffe 0xffff80fe01ffc3ff

def z672 : W := mkw 0x000c01220aa04a30 0x8003004882a8128c 0xec3c13a63ea0cf33 0xbb0f04e98fa833cc

def z673 : W := mkw 0x026e012007c00220 0x009b804801f00088 0xfbfe03a007c00f32 0xfeff80e801f003cc

def z674 : W := mkw 0x97bffffffaaddb76 0xe5effffffeab76dd 0xffffffffffffffff 0xffffffffffffffff

def z675 : W := mkw 0x1191fecdb0000000 0x04647fb36c000000 0xd3c1ffc7f8000003 0x74f07ff1fe000000

def z676 : W := mkw 0x08c0024245370dc3 0x02300090914dc370 0xffc003c0073f0fc2 0x7ff000f001cfc3f0

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x60000040010008c2 0x5800001000400230

def z678 : W := mkw 0x0dc963e76d374ff3 0xc37258f9db4dd3fc 0xffc1e3e7ff3f0ff3 0x7ff078f9ffcfc3fc

def z679 : W := mkw 0x0911f887403fa943 0x02447e21d00fea50 0x0401fc07c03ff001 0x01007f01f00ffc00

def z680 : W := mkw 0x022e013002c00228 0x008b804c00b0008a 0xe83e03b806c00f3e 0xba0f80ee01b003cf

def z681 : W := mkw 0x001c912002888220 0x0007244800a22088 0xec3dd3a006bccf33 0xbb0f74e801af33cc

def z682 : W := mkw 0x0410d086282cc910 0xc10434218a0b3244 0xec01d3863e3ccf03 0x3b0074e18f8f33c0

def z683 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0xe83dc3a0069c0f32 0xba0f70e801a703cc

def z684 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0xd3ffc3f800000002 0xf4fff0fe00000000

def z685 : W := mkw 0x8111bc0ad83bf856 0xa0446f02b60efe15 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z686 : W := mkw 0x0155b80007daa000 0x00556e0001f6a800 0x2c01fc0007fff001 0x0b007f0001fffc00

def z687 : W := mkw 0x82aa077ad8215856 0xa0aa81deb6085615 0xf7fe3ffff9e3f8ff 0xfdff8ffffe78fe3f

def z688 : W := mkw 0x018162c500000000 0x006058b140000000 0x93c1c38000000000 0x24f070e000000000

def z689 : W := mkw 0x0941608745370dc3 0x02505821d14dc370 0x2c01e007c73f0fc1 0x0b007801f1cfc3f0

def z690 : W := mkw 0x108843f520000000 0x042210fd48000000 0x0000038000000000 0x000000e000000000

def z691 : W := mkw 0x13fbfffdb5000480 0x04feffff6d400120 0xfbffffffff000fc3 0xfeffffffffc003f0

def z692 : W := mkw 0x13bbbf79b0000000 0x04eeefde6c000000 0x13fe3c79f8000000 0xc4ff8f1e7e000000

def z693 : W := mkw 0x1377fc8db7daa000 0x04ddff236df6a800 0xfffffc07fffff001 0xffffff01fffffc00

def z694 : W := mkw 0x9111fc8ff8215856 0xa4447f23fe085615 0x6403fc7ff9e3f8ff 0xd900ff1ffe78fe3f

def z695 : W := mkw 0x17bffffdb28c8320 0x45efffff6ca320c8 0xdbfffffffe1c0703 0xf6ffffffff8701c0

def z696 : W := mkw 0x0777b8020ffeeb30 0xc1ddee0083ffbacc 0xfffffc0007ffff31 0xffffff0001ffffcc

def z697 : W := mkw 0x0111b80000000000 0x00446e0000000000 0x0001fc0000000001 0x00007f0000000000

def z698 : W := mkw 0x00c0024005000480 0x0030009001400120 0x13c00040010000c0 0x44f0001000400030

def z699 : W := mkw 0x13fbfffdb5400488 0x04feffff6d500122 0xd3fffffff94000cf 0xf4fffffffe500033

def z700 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfe03b806c0073c 0xa6ff80ee01b001cf

def z701 : W := mkw 0x80000408d0011046 0x2000010234004411 0x60022c79c1c338fe 0xd8008b1e7070ce3f

def z702 : W := mkw 0x0000000240210842 0x0000000090084210 0x04002007c0230001 0x01000801f008c000

def z703 : W := mkw 0x0004000002888000 0x0001000000a22000 0x2c00000006bcc000 0x0b00000001af3000

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002003800c0003c 0x8000800e0030000f

def z705 : W := mkw 0x0141608605360900 0x00505821814d8240 0xffc1e386073f0f03 0x7ff078e181cfc3c0

def z706 : W := mkw 0x055df1a62fbecb30 0xc1577c698befb2cc 0xfffdf3a63fbfcf33 0xffff7ce98feff3cc

def z707 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9bc1c387c61c0700 0x26f070e1f18701c0

def z708 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3fe3ebccfff 0xbb0f74ff8faf33ff

def z709 : W := mkw 0x13bbfffdb0400008 0x04eeffff6c100002 0xd3fffffff840000f 0xf4fffffffe100003

def z710 : W := mkw 0x06f2d2d62d6ccd98 0xc1bcb4b58b5b3366 0x17c3d05e397cc0cd 0x45f0f4178e5f3033

def z711 : W := mkw 0x13bbbf79b0000000 0x04eeefde6c000000 0x53fe3c7ff8000003 0xd4ff8f1ffe000000

def z712 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0x883dd3a03e1c0700 0xa20f74e80f8701c0

def z713 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc3807fff03d 0xffffff0e01fffc0f

def z714 : W := mkw 0x0333bc0890000000 0x00ccef0224000000 0xd3fffc07f8000001 0xf4ffff01fe000000

def z715 : W := mkw 0x89c166cd9d165595 0xa27059b367459565 0x9bc3dfb83edcf73c 0xa6f0f7ee0fb73dcf

def z716 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0xfbc1e3c1c71f0fc2 0x7ef078f071c7c3f0

def z717 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1f3c7c7bfcfc3 0xfff07cf1f1eff3f0

def z718 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x883dd3a63e9ccf32 0xa20f74e98fa733cc

def z719 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc7807fff003 0xffffff1e01fffc00

def z720 : W := mkw 0x0ab6dac742edadc3 0x02adb6b1d0bb6b70 0x003e1fc7c0c0ffc2 0x800f87f1f0303ff0

def z721 : W := mkw 0x0199bb70001aa6a8 0x00666edc0006a9aa 0x0401fff8003fffff 0x01007ffe000fffff

def z722 : W := mkw 0x09c162c745770dcb 0x027058b1d15dc372 0xffc1e3c7c77f0fcf 0x7ff078f1f1dfc3f3

def z723 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e3c7c7ff0fff 0x7ff078f1f1ffc3ff

def z724 : W := mkw 0x02ee0b7007c026a8 0x00bb82dc01f009aa 0xfbfe0ff807c03ffe 0xfeff83fe01f00fff

def z725 : W := mkw 0x10cc47fdb7daa000 0x043311ff6df6a800 0x2c0003fffffff002 0x0b0000fffffffc00

def z726 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0x883dc3a63e1c0702 0x220f70e98f8701c0

def z727 : W := mkw 0x02aa077890000000 0x00aa81de24000000 0xd3fe03fff8000002 0xf4ff80fffe000000

def z728 : W := mkw 0x93bbfbf768215856 0xa4eefefdda085615 0xb7fdc38001e3f8fc 0x2dff70e00078fe3f

def z729 : W := mkw 0x098162c740370943 0x026058b1d00dc250 0xffc1e3c7c63f0f03 0x7ff078f1f18fc3c0

def z730 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fdffa7f8000003 0xb4ff7fe9fe000000

def z731 : W := mkw 0x13bbfffdb00006a8 0x04eeffff6c0001aa 0xd3fffffff8000703 0xf4fffffffe0001c0

def z732 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9fc1e3c7c73f07c1 0x67f078f1f1cfc1f0

def z733 : W := mkw 0x884400024ffffdd7 0xa211000093ffff75 0x2c00000007fffffc 0x0b00000001ffffff

def z734 : W := mkw 0x13bbfffdb00006a8 0x04eeffff6c0001aa 0xf3fffffff9c00fff 0xfcfffffffe7003ff

def z735 : W := mkw 0x041cd1b62aaccb38 0xc107346d8aab32ce 0xec3dd3be3ebccf3f 0xbb0f74ef8faf33cf

def z736 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffffdff8000001 0x64fffff7fe000000

def z737 : W := mkw 0x076b69a62d766b30 0xc1dada698b5d9acc 0x13c22fa639433f32 0x44f08be98e50cfcc

def z738 : W := mkw 0x8511fc8ef83ff956 0xe1447f23be0ffe55 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z739 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffdffff8000002 0xa4fff7fffe000000

def z740 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xbfffec0007fff000 0x6ffffb0001fffc00

def z741 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xfbc1c3c7c71c0fc2 0x7ef070f1f1c703f0

def z742 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1c3c7c63c0fc3 0x3ff070f1f18f03f0

def z743 : W := mkw 0x02aa0370000006a8 0x00aa80dc000001aa 0xf3fe03f801c00ffe 0xfcff80fe007003ff

def z744 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xbfffdc0007fff000 0xaffff70001fffc00

def z745 : W := mkw 0x0c4400024fffeff3 0xc311000093fffbfc 0x2c00000007fffff0 0x0b00000001fffffc

def z746 : W := mkw 0x8d11f48ff83fd957 0xe3447d23fe0ff655 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z747 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3df3e7ffffffff 0xfb0f7cf9ffffffff

def z748 : W := mkw 0x0941608745370943 0x02505821d14dc250 0xffc1e387c73f0f03 0x7ff078e1f1cfc3c0

def z749 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc3e3ffc7ffffff 0xfff0f8fff1ffffff

def z750 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfffe23f807e30fff 0xffff88fe01f8c3ff

def z751 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe13fe3fc00fff 0xfeff84ff8ff003ff

def z752 : W := mkw 0x0337b80002daa000 0x00cdee0000b6a800 0xd7fffc0000fff001 0xf5ffff00003ffc00

def z753 : W := mkw 0x098162c740250dc3 0x026058b1d0094370 0xffc1e3c7c63c0fc3 0x7ff078f1f18f03f0

def z754 : W := mkw 0x09c162c505160581 0x027058b141458160 0xffc1e3c7c73f0703 0x7ff078f1f1cfc1c0

def z755 : W := mkw 0x841cd5acf28d9366 0x6107356b3ca364d9 0x883fefd9c75f37cc 0x620ffbf671d7cdf3

def z756 : W := mkw 0x0b2f61b742f70b6b 0x02cbd86dd0bdc2da 0x043fe03fc0ff003d 0x810ff80ff03fc00f

def z757 : W := mkw 0x8911fc8fd83ff957 0xa2447f23f60ffe55 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z758 : W := mkw 0x841cd1a62aacdb34 0xe10734698aab36cd 0xec3dd3a63efcff3f 0xbb0f74e98fbf3fcf

def z759 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xac3dd3863ebccf31 0x2b0f74e18faf33cc

def z760 : W := mkw 0x8c8847eff8255ff7 0xe32211fbfe0957fd 0x000003fff8000ffe 0x000000fffe0003ff

def z761 : W := mkw 0x0018d1a420040100 0x0006346908010040 0xc83dd3a63e1c0703 0xb20f74e98f8701c0

def z762 : W := mkw 0x040c41a62aa44b30 0xc10310698aa912cc 0xec3dc3a63ebc0f33 0xbb0f70e98faf03cc

def z763 : W := mkw 0x1155fc8db7c006a8 0x04557f236df001aa 0x2801fc07ffc00ffd 0x0a007f01fff003ff

def z764 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xdfc1e3c7c63f0703 0x77f078f1f18fc1c0

def z765 : W := mkw 0x82ee077adfe15efe 0xa0bb81deb7f857bf 0x9ffc3f87fe23f701 0x27ff0fe1ff88fdc0

def z766 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc1e3e7ff3f0ff3 0x7ff078f9ffcfc3fc

def z767 : W := mkw 0x0dddb3616f9bc6f3 0xc3776cd85be6f1bc 0x13fc3061f983c0f0 0xc4ff0c187e60f03c

def z768 : W := mkw 0x123e9d38b2c8a228 0x048fa74e2cb2288a 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z769 : W := mkw 0x13bbfffdb0000228 0x04eeffff6c00008a 0xd3fffffff800003f 0xf4fffffffe00000f

def z770 : W := mkw 0x02ae037002c006a8 0x00ab80dc00b001aa 0xd3fe03f800c00ffe 0xf4ff80fe003003ff

def z771 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1ffc7c73fffc3 0x7ff07ff1f1cffff0

def z772 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0xec023fffffe3ffff 0xfb008ffffff8ffff

def z773 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0xec3dd3a63ebcc703 0xbb0f74e98faf31c0

def z774 : W := mkw 0x09c162c505160581 0x027058b141458160 0x9bc1c3c7c61c0702 0x26f070f1f18701c0

def z775 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x17fffc0001fff001 0xc5ffff00007ffc00

def z776 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x13fe03f801c00ffe 0xc4ff80fe007003ff

def z777 : W := mkw 0x8377bc0adffbf856 0xa0ddef02b7fefe15 0x9bfdc07ffe1c08fe 0x26ff701fff87023f

def z778 : W := mkw 0x03bbbf7890000000 0x00eeefde24000000 0xd3fffffff8000003 0xf4fffffffe000000

def z779 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3863e3ccf03 0x3b0f74e18f8f33c0

def z780 : W := mkw 0x02ea0370054006a8 0x00ba80dc015001aa 0xd3fe03f801400ffe 0xf4ff80fe005003ff

def z781 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fde3fff8000003 0x74ff78fffe000000

def z782 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xac3dd3a03ebccf30 0xab0f74e80faf33cc

def z783 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3fd3fe3fffffff 0xfb0ff4ff8fffffff

def z784 : W := mkw 0x1be32e5995120481 0x06f8cb9665448120 0x13c22c59c0000000 0x44f08b1670000000

def z785 : W := mkw 0x10cc47fdb7c006a8 0x043311ff6df001aa 0x280003ffffc00ffe 0x0a0000fffff003ff

def z786 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dc3a63e3c0f33 0x3b0f70e98f8f03cc

def z787 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc1e3c7c73f0fff 0x7ff078f1f1cfc3ff

def z788 : W := mkw 0x0044040897c006a8 0x0011010225f001aa 0x68023c7fffc00fff 0xda008f1ffff003ff

def z789 : W := mkw 0x0377b80007daa6a8 0x00ddee0001f6a9aa 0xfffffc0007fff701 0xffffff0001fffdc0

def z790 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fd3a63ffccf33 0xfb0ff4e98fff33cc

def z791 : W := mkw 0x13bbfffdb0040100 0x04eeffff6c010040 0xdbfffffffe1c0703 0xf6ffffffff8701c0

def z792 : W := mkw 0x01c162c505120480 0x007058b141448120 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z793 : W := mkw 0x13bbfffdb0000488 0x04eeffff6c000122 0xd3fffffff80000cf 0xf4fffffffe000033

def z794 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3dd3a63ebfff33 0xbb0f74e98fafffcc

def z795 : W := mkw 0x09c162c505160581 0x027058b141458160 0x9bc1e387c61c0701 0x26f078e1f18701c0

def z796 : W := mkw 0x02ee037007c886a8 0x00bb80dc01f221aa 0xfffe03f807fccffe 0xffff80fe01ff33ff

def z797 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xac3dc3a63ebccf32 0x2b0f70e98faf33cc

def z798 : W := mkw 0x0155b000079a8000 0x00556c0001e6a000 0xfffffc0007fff001 0xffffff0001fffc00

def z799 : W := mkw 0x0018d1a628244910 0x800634698a091244 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z800 : W := mkw 0x12aa47fdb0000000 0x04aa91ff6c000000 0x93fc03fff8000002 0x24ff00fffe000000

def z801 : W := mkw 0x1a7a9d3af5370dc3 0x069ea74ebd4dc370 0x2c3e1c383f3f0fc0 0x8b0f870e0fcfc3f0

def z802 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff9433003 0xf4fffffffe50cc00

def z803 : W := mkw 0x12ba9f78b0000000 0x04aea7de2c000000 0xd3fe3ffff8000003 0xf4ff8ffffe000000

def z804 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe1ff807c0fffe 0xfeff87fe01f03fff

def z805 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fd3be3efccf3f 0xbb0ff4ef8fbf33cf

def z806 : W := mkw 0x9be32e59d51314c7 0x26f8cb967544c531 0x13c22c59c14330cc 0x44f08b167050cc33

def z807 : W := mkw 0x884400024ff75fff 0xa211000093fdd7ff 0x2c00000007fffffc 0x0b00000001ffffff

def z808 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3ffc3fff8000002 0xf4fff0fffe000000

def z809 : W := mkw 0x844400024feddffe 0xe111000093fb77ff 0x2c00000007fffffc 0x0b00000001ffffff

def z810 : W := mkw 0x863e9d28bac8f234 0xe18fa74a2eb23c8d 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z811 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0xffc1e3c1c73f07c1 0x7ff078f071cfc1f0

def z812 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfe03f806c00ffe 0xa6ff80fe01b003ff

def z813 : W := mkw 0x13e32e5995522488 0x04f8cb9665548922 0x13c22c59c14330cc 0x44f08b167050cc33

def z814 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3ffffc7ffffff 0xfff0fffff1ffffff

def z815 : W := mkw 0x0337b800029aa000 0x00cdee0000a6a800 0xfffffc0006bff001 0xffffff0001affc00

def z816 : W := mkw 0x0377b80007daa480 0x00ddee0001f6a920 0xfffffc0007ffffc1 0xffffff0001fffff0

def z817 : W := mkw 0x0199f7edb0000000 0x00667dfb6c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z818 : W := mkw 0x0dc162c76d374dd3 0xc37058b1db4dd374 0xffc1e3c7ff3f0fc3 0x7ff078f1ffcfc3f0

def z819 : W := mkw 0x13ab6ffdb0000000 0x04eadbff6c000000 0xd3fe2ffff8000002 0xf4ff8bfffe000000

def z820 : W := mkw 0x13bbfffdb008a000 0x04eeffff6c022800 0xd3fffffff800f003 0xf4fffffffe003c00

def z821 : W := mkw 0x1be32e59d55324c3 0x06f8cb967554c930 0x13c22c59c14330c0 0x44f08b167050cc30

def z822 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0x9bfe03f807400ffe 0x66ff80fe01d003ff

def z823 : W := mkw 0x0141608645370942 0x00505821914dc250 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z824 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xbbfe03d807c00ffc 0x6eff80f601f003ff

def z825 : W := mkw 0x163e9d38bac8e230 0xc58fa74e2eb2388c 0x003e1c3838c0f030 0x800f870e0e303c0c

def z826 : W := mkw 0x09c162c705360d81 0x027058b1c14d8360 0xffc1e3c7c63c0f03 0x7ff078f1f18f03c0

def z827 : W := mkw 0x83e32e58d55334ce 0x20f8cb963554cd33 0x13c22c59c14330cc 0x44f08b167050cc33

def z828 : W := mkw 0x02ee037007d206a8 0x00bb80dc01f481aa 0xfffe03f807ff0ffe 0xffff80fe01ffc3ff

def z829 : W := mkw 0x17a72e5b9aaccb30 0xc5e9cb96e6ab32cc 0x3fc22c59c6bccf30 0x4ff08b1671af33cc

def z830 : W := mkw 0x804400024fe15856 0xa011000093f85615 0x2c00000007e3f8fc 0x0b00000001f8fe3f

def z831 : W := mkw 0x001cd1a422888220 0x0007346908a22088 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z832 : W := mkw 0x001c91220aa8ca30 0x8007244882aa328c 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z833 : W := mkw 0x08c042c745250dc3 0x023010b1d1494370 0xffc1c3c7c73c0fc3 0x7ff070f1f1cf03f0

def z834 : W := mkw 0x0155b800079aa000 0x00556e0001e6a800 0xfffdfc0007bff001 0xffff7f0001effc00

def z835 : W := mkw 0x13bbfffdb0120000 0x04eeffff6c048000 0xd7fffffff83f0003 0xf5fffffffe0fc000

def z836 : W := mkw 0x8be32659d55314cf 0x22f8c9967554c533 0x13c22c59c14330cc 0x44f08b167050cc33

def z837 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff8c0003f 0xf4fffffffe30000f

def z838 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fdffc7f8000003 0x74ff7ff1fe000000

def z839 : W := mkw 0x00cc0360078006a0 0x003300d801e001a8 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z840 : W := mkw 0x17bbfffdb00c8100 0x45eeffff6c032040 0xd3fffffff81c0003 0xf4fffffffe070000

def z841 : W := mkw 0x1155fc8db7daa000 0x04557f236df6a800 0x2c01fc07fffff001 0x0b007f01fffffc00

def z842 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x8c3dd3a63ebcc731 0xa30f74e98faf31cc

def z843 : W := mkw 0x03b3fecd90000000 0x00ecffb364000000 0xd3fffffff8000003 0xf4fffffffe000000

def z844 : W := mkw 0x844400024ffffb76 0xe111000093fffedd 0x2c00000007fffffc 0x0b00000001ffffff

def z845 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x8c3dd3a63e3ccf33 0x230f74e98f8f33cc

def z846 : W := mkw 0x09c162d745370dcb 0x027058b5d14dc372 0xffc1e3dfc73f0fcf 0x7ff078f7f1cfc3f3

def z847 : W := mkw 0x1199ffedb0000000 0x04667ffb6c000000 0xd3fdffe7f8000003 0xf4ff7ff9fe000000

def z848 : W := mkw 0x13bbfffdb0402000 0x04eeffff6c100800 0xd3fffffff8403003 0xf4fffffffe100c00

def z849 : W := mkw 0x02ee037007daa6a8 0x00bb80dc01f6a9aa 0xfffe3ff807ffffff 0xffff8ffe01ffffff

def z850 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0x9bc1e381c61f0700 0x26f078e07187c1c0

def z851 : W := mkw 0x17bbfffdb0040320 0x45eeffff6c0100c8 0xd3fffffff8000703 0xf4fffffffe0001c0

def z852 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff8c0f003 0xf4fffffffe303c00

def z853 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe3ff807c00fff 0xfeff8ffe01f003ff

def z854 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0xe83dd3a03e9ccf32 0xba0f74e80fa733cc

def z855 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fffa63ebccf33 0xfb0fffe98faf33cc

def z856 : W := mkw 0x80000408d8015056 0xa000010236005415 0x40023c7ff9c3f0ff 0xd0008f1ffe70fc3f

def z857 : W := mkw 0x0414d0862aacc910 0xc10534218aab3244 0xec3dd3863ebccf03 0xbb0f74e18faf33c0

def z858 : W := mkw 0x13bbfbf520000000 0x04eefefd48000000 0xd3fdf3e7f8000003 0xf4ff7cf9fe000000

def z859 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc3ffe7fffffff3 0xfff0fff9fffffffc

def z860 : W := mkw 0x026e012007c00220 0x009b804801f00088 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z861 : W := mkw 0x8000040ad8255956 0xa0000102b6095655 0x6c023c7fffffffff 0xdb008f1fffffffff

def z862 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xfbfffffffe000f03 0xfeffffffff8003c0

def z863 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff94000cf 0xf4fffffffe500033

def z864 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc0007fff8fd 0xffffff0001fffe3f

def z865 : W := mkw 0x001cd1a622ac8900 0x0007346988ab2240 0xec3dd3a63ebccf03 0xbb0f74e98faf33c0

def z866 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc3ffc7c7ffffff 0xfff0fff1f1ffffff

def z867 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1f3e7ff3f0fc3 0xfff07cf9ffcfc3f0

def z868 : W := mkw 0x0222040890000000 0x0088810224000000 0xd3fe3c7ff8000003 0xf4ff8f1ffe000000

def z869 : W := mkw 0x82aa037248215856 0xa0aa80dc92085615 0xf7fe03f801e3f8fe 0xfdff80fe0078fe3f

def z870 : W := mkw 0x000c41a60aa44b30 0x8003106982a912cc 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z871 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xcc3dd3a63e3cc703 0xb30f74e98f8f31c0

def z872 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf3fffffff9c00003 0xfcfffffffe700000

def z873 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xffffc3f807fc0fff 0xfffff0fe01ff03ff

def z874 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93fdfffff8000003 0x24ff7ffffe000000

def z875 : W := mkw 0x0377b81007daa008 0x00ddee0401f6a802 0xfffffc1807fff00d 0xffffff0601fffc03

def z876 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3e3c7c7ff0fc3 0xfff0f8f1f1ffc3f0

def z877 : W := mkw 0x02ee037007c8a6a8 0x00bb80dc01f229aa 0xfbfe03f807c0fffe 0xfeff80fe01f03fff

def z878 : W := mkw 0x02bad7fcb0000000 0x00aeb5ff2c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z879 : W := mkw 0x041cd1a622ac8b20 0x4107346988ab22c8 0xec3dd3a63e3c0f03 0xbb0f74e98f8f03c0

def z880 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93fdc387f8000000 0x24ff70e1fe000000

def z881 : W := mkw 0x12badffdb0000000 0x04aeb7ff6c000000 0xd3fe1ffff8000002 0xf4ff87fffe000000

def z882 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc3f3ffffffcfff 0xfff0fcfffffff3ff

def z883 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xc83dd3a63e1c0f33 0xb20f74e98f8703cc

def z884 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0x883dc3863e1c0700 0x220f70e18f8701c0

def z885 : W := mkw 0x0276900007c88000 0x009da40001f22000 0xfffffc0007fff001 0xffffff0001fffc00

def z886 : W := mkw 0x041cd1a62aeccb38 0xc10734698abb32ce 0xec3dd3a63efccf3f 0xbb0f74e98fbf33cf

def z887 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xbfc1c3c7c73f0fc2 0x2ff070f1f1cfc3f0

def z888 : W := mkw 0x163e9d38b2888220 0x458fa74e2ca22088 0x003e1c3838000000 0x800f870e0e000000

def z889 : W := mkw 0x13fffbf527daa6a8 0x04fffefd49f6a9aa 0x9bfdc380061c0700 0x26ff70e0018701c0

def z890 : W := mkw 0x0000040890000000 0x0000010224000000 0x64023c7ff9e3f8ff 0xd9008f1ffe78fe3f

def z891 : W := mkw 0x09c162c505160581 0x027058b141458160 0x9bc1e3c1c61c0700 0x66f078f0718701c0

def z892 : W := mkw 0x13ab67fdb0000000 0x04ead9ff6c000000 0xd3ffe3fff8000003 0xf4fff8fffe000000

def z893 : W := mkw 0x848847fef8255ffe 0xe12211ffbe0957ff 0x000003fff8000ffe 0x000000fffe0003ff

def z894 : W := mkw 0x00c042c645250dc2 0x003010b191494370 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z895 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fd3fe3ebccf33 0xfb0ff4ff8faf33cc

def z896 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc1e3c7c73fffc3 0x7ff078f1f1cffff0

def z897 : W := mkw 0x0044040897daa000 0x0011010225f6a800 0x6c023c7ffffff003 0xdb008f1ffffffc00

def z898 : W := mkw 0x948847fff8255b76 0xe52211fffe0956dd 0x000003fff8000ffe 0x000000fffe0003ff

def z899 : W := mkw 0x041cd9a62aaceb30 0xc10736698aab3acc 0xec3ddfa63ebcff33 0xbb0f77e98faf3fcc

def z900 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x13fe3ffff8000002 0xc4ff8ffffe000000

def z901 : W := mkw 0x0337b80002888000 0x00cdee0000a22000 0xfffffc0007fff001 0xffffff0001fffc00

def z902 : W := mkw 0x033bfdacb0000000 0x00ceff6b2c000000 0xd3fffffff8000003 0xf4fffffffe000000

def z903 : W := mkw 0x0014d0860aacc910 0x8005342182ab3244 0xec3dd3a63ebccf33 0xbb0f74e98faf33cc

def z904 : W := mkw 0x041cd1a62aeceb30 0xc10734698abb3acc 0xec3dd3a63efcff33 0xbb0f74e98fbf3fcc

def z905 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xdffffc00063ff001 0xf7ffff00018ffc00

def z906 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffdfc00073ff001 0x7fff7f0001cffc00

def z907 : W := mkw 0x888847ffd8255fff 0xa22211fff60957ff 0x000003fff8000ffe 0x000000fffe0003ff

def z908 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xbfc1e387c73f0fc1 0x2ff078e1f1cfc3f0

def z909 : W := mkw 0x1199f7fdb0000000 0x04667dff6c000000 0xd3fdf3fff8000003 0xf4ff7cfffe000000

def z910 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3ffff87f8000001 0xf4ffffe1fe000000

def z911 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3dd3e7febccff3 0xbb0f74f9ffaf33fc

def z912 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3fffa63fffffff 0xfb0fffe98fffffff

def z913 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0xdbc1e3c7c71f07c3 0x76f078f1f1c7c1f0

def z914 : W := mkw 0x018162c740250942 0x006058b1d0094250 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z915 : W := mkw 0x89c162c74d375dd7 0xa27058b1d34dd775 0xffc1f3e7ffffffff 0xfff07cf9ffffffff

def z916 : W := mkw 0x02ee037007d226a8 0x00bb80dc01f489aa 0xfbfe03f807c33ffe 0xfeff80fe01f0cfff

def z917 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3efc7c77f3fc3 0x7ff0fbf1f1dfcff0

def z918 : W := mkw 0x02ea037005000480 0x00ba80dc01400120 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z919 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3a63fffff33 0xbb0f74e98fffffcc

def z920 : W := mkw 0x93bbfffdb0001004 0x24eeffff6c000401 0xd3fffffff840300f 0xf4fffffffe100c03

def z921 : W := mkw 0x963e9d38ba88d234 0xe58fa74e2ea2348d 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z922 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0xc83dd3a63e9cc733 0xb20f74e98fa731cc

def z923 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3863ebcc701 0xbb0f74e18faf31c0

def z924 : W := mkw 0x0373b800055aa000 0x00dcee000156a800 0xd7fffc00017ff001 0xf5ffff00005ffc00

def z925 : W := mkw 0x13ab2f7990000000 0x04eacbde64000000 0xd3fe3ffff8000003 0xf4ff8ffffe000000

def z926 : W := mkw 0x001cd1a622a40b20 0x0007346988a902c8 0xec3dd3a63ebc0f33 0xbb0f74e98faf03cc

def z927 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3a63ffccfff 0xbb0f74e98fff33ff

def z928 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe2ff807c33ffe 0xfeff8bfe01f0cfff

def z929 : W := mkw 0x1333fc8db0000000 0x04ccff236c000000 0x93fdfc07f8000001 0x24ff7f01fe000000

def z930 : W := mkw 0x02ae037002800220 0x00ab80dc00a00088 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z931 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x13fffc7ff8000001 0xc4ffff1ffe000000

def z932 : W := mkw 0x02ae0370028006a8 0x00ab80dc00a001aa 0xfbfe03f806800ffe 0xfeff80fe01a003ff

def z933 : W := mkw 0x018162c500040100 0x006058b140010040 0xdbc1e3c7c61c0703 0x76f078f1f18701c0

def z934 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xbbfe03b807c00ffc 0xaeff80ee01f003ff

def z935 : W := mkw 0x0c4400024fffcffb 0xc311000093fff3fe 0x2c00000007ffcffc 0x0b00000001fff3ff

def z936 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0x883dd3803e1cc700 0x220f74e00f8731c0

def z937 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc2007fff833 0xffffff0801fffe0c

def z938 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e387c63f0f03 0x3ff078e1f18fc3c0

def z939 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0xe83dd3a63e9c0f33 0xba0f74e98fa703cc

def z940 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0x883dc3a03e1c0730 0x220f70e80f8701cc

def z941 : W := mkw 0x13bbfffdb0000220 0x04eeffff6c000088 0xd3fffffff8000f33 0xf4fffffffe0003cc

def z942 : W := mkw 0x13bbfffdb0088000 0x04eeffff6c022000 0xd7fffffff83cc003 0xf5fffffffe0f3000

def z943 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xfffffffffe3c0003 0xffffffffff8f0000

def z944 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfffe13f807e0cfff 0xffff84fe01f833ff

def z945 : W := mkw 0x01c162c705360900 0x007058b1c14d8240 0xffc1e3c7c73f0f03 0x7ff078f1f1cfc3c0

def z946 : W := mkw 0x988847fff8255dd7 0xa62211fffe095775 0x000003fff8000ffe 0x000000fffe0003ff

def z947 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf7fffffff9e3f8ff 0xfdfffffffe78fe3f

def z948 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd7fffffff823f003 0xf5fffffffe08fc00

def z949 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc1e3c7c7bfcff3 0x7ff078f1f1eff3fc

def z950 : W := mkw 0x133bfdadb0000000 0x04ceff6b6c000000 0xd3ffffa7f8000003 0xf4ffffe9fe000000

def z951 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3e3dfc77f0fcf 0x7ff0f8f7f1dfc3f3

def z952 : W := mkw 0x02ea0370050006a8 0x00ba80dc014001aa 0xfbfe03f807000ffe 0xfeff80fe01c003ff

def z953 : W := mkw 0x0377b80007daa488 0x00ddee0001f6a922 0xfffffc0007fff0cd 0xffffff0001fffc33

def z954 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3ffffe3fffffff 0xfb0fffff8fffffff

def z955 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e3c7c7ffffc3 0x7ff078f1f1fffff0

def z956 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffffbff8000001 0xa4ffffeffe000000

def z957 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfc03f806800ffe 0xbeff00fe01a003ff

def z958 : W := mkw 0x133bfdbdb0000000 0x04ceff6f6c000000 0xd3fffc3ff8000001 0xf4ffff0ffe000000

def z959 : W := mkw 0x863e9538bac8d23c 0xe18fa54e2eb2348f 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z960 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9ffffc0006fff001 0xa7ffff0001bffc00

def z961 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xbffdfc0007fff001 0x2fff7f0001fffc00

def z962 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf7fffffff9230003 0xfdfffffffe48c000

def z963 : W := mkw 0x0418d1a628244b30 0xc10634698a0912cc 0xec3dd3a63e3c0f33 0xbb0f74e98f8f03cc

def z964 : W := mkw 0x13b3fecdb0000000 0x04ecffb36c000000 0xd3ffffc7f8000003 0xf4fffff1fe000000

def z965 : W := mkw 0x09c16ac745372dc3 0x02705ab1d14dcb70 0xffc1efc7c73f3fc3 0x7ff07bf1f1cfcff0

def z966 : W := mkw 0x1bbbfffdb0160101 0x06eeffff6c058040 0xd3fffffff81c0003 0xf4fffffffe070000

def z967 : W := mkw 0x823e9d389ac8f23c 0xa08fa74e26b23c8f 0x003e1c3838c0f03c 0x800f870e0e303c0f

def z968 : W := mkw 0x12bad7fdb0000000 0x04aeb5ff6c000000 0xd3ffd3fff8000003 0xf4fff4fffe000000

def z969 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e3e7c7bf0ff3 0xfff078f9f1efc3fc

def z970 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xdbfe03f806000ffe 0xf6ff80fe018003ff

def z971 : W := mkw 0x13bbfffdb0000480 0x04eeffff6c000120 0xd3fffffff8000fc3 0xf4fffffffe0003f0

def z972 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xffffff8007ffff03 0xffffffe001ffffc0

def z973 : W := mkw 0x0367200007d20000 0x00d9c80001f48000 0xfffffc0007fff001 0xffffff0001fffc00

def z974 : W := mkw 0x0418d1a6282cc910 0xc10634698a0b3244 0xec3dd3a63e3ccf03 0xbb0f74e98f8f33c0

def z975 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfc03f807000ffe 0x7eff00fe01c003ff

def z976 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9fc1e3c7c63f0fc3 0x27f078f1f18fc3f0

def z977 : W := mkw 0x13b3feddb0000000 0x04ecffb76c000000 0xd3fffc5ff8000001 0xf4ffff17fe000000

def z978 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc5807fff0cd 0xffffff1601fffc33

def z979 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0x9bc1e3c7c71f0fc2 0x66f078f1f1c7c3f0

def z980 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3df3a63fbfcf33 0xfb0f7ce98feff3cc

def z981 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3fdfa63efcff33 0xbb0ff7e98fbf3fcc

def z982 : W := mkw 0x02aa0370000006a8 0x00aa80dc000001aa 0x93fc03f800000ffe 0x24ff00fe000003ff

def z983 : W := mkw 0x12aa47fdb0000000 0x04aa91ff6c000000 0xd3fe3ffff8000003 0xf4ff8ffffe000000

def z984 : W := mkw 0x041cd1a42a8cc330 0xc10734690aa330cc 0xec3dd3a03ebcc731 0xbb0f74e80faf31cc

def z985 : W := mkw 0x133bbd38b0000000 0x04ceef4e2c000000 0xd3fffc7ff8000003 0xf4ffff1ffe000000

def z986 : W := mkw 0x841cd1a66aaddb76 0xe10734699aab76dd 0xec3dd3a63ebccfff 0xbb0f74e98faf33ff

def z987 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xe83dc3a63e9c0f32 0xba0f70e98fa703cc

def z988 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x04023c7ff9e3f0fd 0xc1008f1ffe78fc3f

def z989 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3ff3ffffffcfff 0xfb0ffcfffffff3ff

def z990 : W := mkw 0x09c162c5451705c3 0x027058b15145c170 0x9bc1c3c1c61c07c0 0x26f070f0718701f0

def z991 : W := mkw 0x02e6024007c00480 0x00b9809001f00120 0xfbfe03f807c00ffe 0xfeff80fe01f003ff

def z992 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xbbfc03f807c00ffe 0x2eff00fe01f003ff

def z993 : W := mkw 0x0333b800001aa000 0x00ccee000006a800 0xf7fffc0001fff001 0xfdffff00007ffc00

def z994 : W := mkw 0x13bbfffdb01aa000 0x04eeffff6c06a800 0xf7fffffff9fff003 0xfdfffffffe7ffc00

def z995 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3fffe7fffffff3 0xfb0ffff9fffffffc

def z996 : W := mkw 0x09c162c505160581 0x027058b141458160 0xfbc1e3c7c71c0fc3 0x7ef078f1f1c703f0

def z997 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfbfe23ffc7c00fff 0xfeff88fff1f003ff

def z998 : W := mkw 0x0333b800001aa000 0x00ccee000006a800 0x97fdfc00003ff001 0x25ff7f00000ffc00

def z999 : W := mkw 0x0c1cd1a76aadcb73 0xc3073469daab72dc 0xec3dd3a7febccf33 0xbb0f74e9ffaf33cc

def z1000 : W := mkw 0x0373b800051aa000 0x00dcee000146a800 0xfffffc00073ff001 0xffffff0001cffc00

def z1001 : W := mkw 0x8c4400024fbfdff7 0xe311000093eff7fd 0x2c00000007fffffc 0x0b00000001ffffff

def z1002 : W := mkw 0x09c12241451304c3 0x027048905144c130 0xffc1e3c1c73f0fc3 0x7ff078f071cfc3f0

def z1003 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dffa63ebfff33 0xbb0f7fe98fafffcc

def z1004 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0xec03fc7ffffff8ff 0xfb00ff1ffffffe3f

def z1005 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0x93ffeffff8000002 0x64fffbfffe000000

def z1006 : W := mkw 0x804400024fe15efe 0xa011000093f857bf 0x2800000007c00ffc 0x0a00000001f003ff

def z1007 : W := mkw 0x041c91202a88c230 0xc10724480aa2308c 0xec3dd3a03ebccf33 0xbb0f74e80faf33cc

def z1008 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xdbc1e3c7c61c0fc3 0x76f078f1f18703f0

def z1009 : W := mkw 0x89c162c745371dc7 0x227058b1d14dc771 0xffc1e3c7c77f3fcf 0x7ff078f1f1dfcff3

def z1010 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fffffff80008ff 0xf4fffffffe00023f

def z1011 : W := mkw 0x09c162c745772dc3 0x027058b1d15dcb70 0xffc1e3c7c77f3fc3 0x7ff078f1f1dfcff0

def z1012 : W := mkw 0x0377b80007daa6a8 0x00ddee0001f6a9aa 0xfffffc7807ffffff 0xffffff1e01ffffff

def z1013 : W := mkw 0x804400024ffbfefe 0xa011000093feffbf 0x2c00000007fffffc 0x0b00000001ffffff

def z1014 : W := mkw 0x1333fc8db0000000 0x04ccff236c000000 0xd3fffc7ff8000003 0xf4ffff1ffe000000

def z1015 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf3fffffff8800833 0xfcfffffffe20020c

def z1016 : W := mkw 0x0377b80007daa228 0x00ddee0001f6a88a 0xfffffc0007fff03d 0xffffff0001fffc0f

def z1017 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc263ffff003 0xffffff098ffffc00

def z1018 : W := mkw 0x1be32e59d55304cb 0x06f8cb967554c132 0x13c22c59c14300cc 0x44f08b167050c033

def z1019 : W := mkw 0x09c162c74d374dd3 0x827058b1d34dd374 0xffc1f3c7ff3fcfc3 0x7ff07cf1ffcff3f0

def z1020 : W := mkw 0x8be32e49d55334c7 0x22f8cb927554cd31 0x13c22c59c14330cc 0x44f08b167050cc33

def z1021 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3df3e7febccf33 0xfb0f7cf9ffaf33cc

def z1022 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0x9ffffc00077ff001 0x67ffff0001dffc00

def z1023 : W := mkw 0x01c162c705240d80 0x007058b1c1490360 0xffc1e3c7c73c0fc3 0x7ff078f1f1cf03f0

def z1024 : W := mkw 0x8000040ad8215856 0xa0000102b6085615 0x00023c7ff9c3f8fe 0xc0008f1ffe70fe3f

def z1025 : W := mkw 0x8333b80248215856 0xa0ccee0092085615 0xf7fffc0001e3f8fd 0xfdffff000078fe3f

def z1026 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3e3ffc73f0fc3 0xfff0f8fff1cfc3f0

def z1027 : W := mkw 0x03bbfbe520000000 0x00eefef948000000 0xd3ffffe7f8000003 0xf4fffff9fe000000

def z1028 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xd3fdd3fff8000003 0xb4ff74fffe000000

def z1029 : W := mkw 0x13b3be5990000000 0x04ecef9664000000 0xd3fffc7ff8000003 0xf4ffff1ffe000000

def z1030 : W := mkw 0x163e9d38bac8c238 0xc58fa74e2eb2308e 0x003e1c3838c0c03c 0x800f870e0e30300f

def z1031 : W := mkw 0x041cd1a4228c8320 0x4107346908a320c8 0x883dd3863e1c0701 0x220f74e18f8701c0

def z1032 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf7fffffff8a0c003 0xfdfffffffe283000

def z1033 : W := mkw 0x00cc0370078006a8 0x003300dc01e001aa 0xfbfc03f807800ffe 0xfeff00fe01e003ff

def z1034 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc3ffc7c73f0fc3 0xfff0fff1f1cfc3f0

def z1035 : W := mkw 0x02ee037007c006a8 0x00bb80dc01f001aa 0xfffe03f807e3fffe 0xffff80fe01f8ffff

def z1036 : W := mkw 0x02ee037007daa6a8 0x00bb80dc01f6a9aa 0xfbfe03f807dc0ffe 0xfeff80fe01f703ff

def z1037 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc47c7fff003 0xffffff11f1fffc00

def z1038 : W := mkw 0x03bbf3f520000000 0x00eefcfd48000000 0xd3fff3fff8000003 0xf4fffcfffe000000

def z1039 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3df3a7febfcf33 0xbb0f7ce9ffaff3cc

def z1040 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xbfc1e3c1c73f0fc0 0x6ff078f071cfc3f0

def z1041 : W := mkw 0x9911fc8ff8375957 0xa6447f23fe0dd655 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z1042 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e387c73f0701 0x7ff078e1f1cfc1c0

def z1043 : W := mkw 0x0377b80007daa220 0x00ddee0001f6a888 0xfffffc0007ffff31 0xffffff0001ffffcc

def z1044 : W := mkw 0x03ab67fd90000000 0x00ead9ff64000000 0xd3fffffff8000003 0xf4fffffffe000000

def z1045 : W := mkw 0x9511fc8ff82dd956 0xe5447f23fe0b7655 0x0401fc07f83ff001 0x01007f01fe0ffc00

def z1046 : W := mkw 0x0373b80005120000 0x00dcee0001448000 0xfffffc0007fff001 0xffffff0001fffc00

def z1047 : W := mkw 0x01c1224245330cc2 0x00704890914cc330 0xffc1e3c7c73f0fc3 0x7ff078f1f1cfc3f0

def z1048 : W := mkw 0x041cd1a62aaccb30 0xc10734698aab32cc 0xec3dd3e63fbccff3 0xfb0f74f98fef33fc

def z1049 : W := mkw 0x804400024ffbf856 0xa011000093fefe15 0x2c00000007fff000 0x0b00000001fffc00

def z1050 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffdfc0006bff001 0xbfff7f0001affc00

def z1051 : W := mkw 0x1bbbfffdb0040581 0x06eeffff6c010160 0xd3fffffff8000703 0xf4fffffffe0001c0

def z1052 : W := mkw 0x13bbfffdb0000000 0x04eeffff6c000000 0xf3fffffff90008c3 0xfcfffffffe400230

def z1053 : W := mkw 0x09c162c745370dc3 0x027058b1d14dc370 0xffc1e3ffc73f0fff 0x7ff078fff1cfc3ff

def z1054 : W := mkw 0x13bbfffdb01aa000 0x04eeffff6c06a800 0xd3fffffff81c0003 0xf4fffffffe070000

def z1055 : W := mkw 0x041cd1a66aadcb72 0xc10734699aab72dc 0xec3dd3a63fbfcff3 0xbb0f74e98feff3fc

def z1056 : W := mkw 0x13bbfffdb0122000 0x04eeffff6c048800 0xd3fffffff8033003 0xf4fffffffe00cc00

def z1057 : W := mkw 0x0377b80007daa000 0x00ddee0001f6a800 0xfffffc4007fff8c3 0xffffff1001fffe30

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z5,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z11,z6])],[(0,[z1,z2,z12,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z14]),(0,[z15,z1,z2,z4,z5,z6,z16])],[(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z4,z18,z5,z6]),(0,[z19,z1,z2,z3,z4,z20,z6]),(0,[z21,z1,z2,z3,z4,z5,z6]),(1,[z22,z1,z2,z3,z23,z6]),(0,[z1,z2,z3,z5,z24,z6,z25]),(0,[z1,z26,z2,z3,z4,z5,z6])],[],[(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z5,z23,z6])],[(0,[z1,z2,z3,z4,z29,z5,z6]),(0,[z30,z1,z2,z3,z31,z5,z6]),(0,[z1,z2,z32,z3,z33,z5,z6])],[(0,[z34,z1,z2,z35,z4,z5,z6]),(0,[z36,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z35,z4,z5,z37]),(0,[z22,z1,z2,z3,z5,z23,z6])]],
   [[(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z35,z39,z4,z5,z6]),(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z1,z2,z3,z4,z42,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z43])],[(0,[z44,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z46,z6]),(1,[z1,z47,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z48])],[(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z51,z4,z5,z6])],[(0,[z45,z1,z52,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z53,z6])],[(0,[z1,z2,z3,z54,z5,z6,z25]),(0,[z1,z2,z3,z4,z5,z55,z6]),(0,[z22,z1,z2,z32,z3,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z6])],[(0,[z1,z2,z3,z57,z4,z5,z6]),(1,[z1,z2,z3,z58,z5,z6]),(0,[z15,z1,z2,z3,z58,z5,z6])],[(0,[z1,z2,z3,z59,z4,z5,z6]),(0,[z1,z2,z3,z60,z4,z5,z6]),(0,[z61,z1,z2,z62,z4,z5,z6]),(0,[z1,z2,z35,z63,z4,z5,z6]),(0,[z64,z34,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z2,z66,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z68])],[(0,[z69,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z70,z6]),(0,[z1,z2,z32,z3,z4,z5,z6])],[(0,[z1,z2,z3,z71,z4,z5,z6]),(0,[z1,z2,z72,z3,z4,z5,z6])],[(0,[z73,z2,z3,z4,z46,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z74]),(0,[z75,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z76,z6]),(0,[z34,z1,z2,z3,z4,z77,z6]),(0,[z78,z1,z2,z3,z4,z5,z6])],[(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z80,z6]),(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z20,z6,z82])],[(0,[z1,z2,z35,z4,z83,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z1,z2,z3,z4,z5,z85,z6]),(0,[z1,z2,z3,z4,z5,z6,z86]),(0,[z87,z1,z2,z3,z4,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z91,z4,z5,z6]),(0,[z92,z1,z2,z3,z4,z5,z11])]],
   [[(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z19,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z95]),(0,[z96,z1,z2,z3,z4,z97,z6]),(0,[z1,z2,z98,z3,z4,z5,z6])],[(0,[z1,z2,z3,z99,z5,z6,z25]),(0,[z1,z100,z2,z101,z4,z5,z6]),(0,[z1,z2,z102,z3,z103,z4,z6]),(0,[z90,z1,z2,z3,z4,z5,z25])],[(1,[z61,z2,z3,z4,z5,z104]),(0,[z1,z2,z3,z4,z105,z5,z6]),(0,[z1,z2,z3,z106,z4,z5,z6]),(0,[z1,z2,z3,z107,z4,z5,z6])],[(0,[z108,z1,z2,z3,z4,z46,z6]),(0,[z1,z2,z3,z4,z97,z5,z6]),(0,[z1,z2,z3,z109,z28,z5,z6])],[(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z1,z2,z3,z113,z4,z5,z6]),(0,[z1,z2,z3,z4,z114,z5,z6])],[(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z61,z1,z2,z3,z4,z5,z104]),(0,[z1,z116,z2,z3,z4,z5,z6]),(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z118]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z5,z6,z82])],[(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z121,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z122,z3,z4,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z124,z3,z4,z5,z6]),(1,[z78,z1,z2,z4,z5,z6])],[(0,[z19,z1,z2,z3,z4,z125,z6]),(0,[z2,z3,z4,z46,z5,z125,z6]),(0,[z61,z1,z126,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z127])]],
   [[(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z129,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z130,z6]),(0,[z1,z2,z3,z4,z131,z5,z6])],[(0,[z1,z2,z132,z3,z4,z5,z6]),(1,[z64,z1,z2,z97,z5,z6]),(0,[z1,z2,z133,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z134,z6]),(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z136,z5,z6]),(0,[z92,z1,z137,z2,z3,z4,z6]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z140,z5,z6])],[(0,[z141,z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z3,z4,z142,z5,z6]),(0,[z1,z2,z3,z4,z143,z5,z6]),(0,[z1,z2,z3,z4,z144,z5,z6]),(0,[z1,z2,z3,z4,z145,z97,z6]),(0,[z1,z2,z3,z4,z146,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z6,z148]),(0,[z1,z149,z2,z3,z4,z5,z130]),(0,[z96,z1,z2,z3,z4,z5,z6])],[(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z151,z3,z4,z5,z6]),(0,[z152,z1,z2,z3,z4,z5,z6]),(1,[z1,z149,z3,z4,z5,z130])],[(0,[z1,z2,z153,z3,z4,z5,z6]),(0,[z1,z2,z3,z97,z5,z6,z25]),(1,[z88,z1,z2,z3,z5,z6])]],
   [[(0,[z108,z1,z2,z3,z4,z20,z6])],[(0,[z2,z151,z3,z4,z46,z5,z6])],[(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z155,z6]),(0,[z1,z2,z101,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z31,z5,z6]),(1,[z34,z1,z2,z4,z77,z6]),(0,[z156,z1,z2,z3,z4,z5,z6])],[(0,[z73,z157,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z158,z5,z6])],[(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z160,z6]),(0,[z1,z2,z3,z4,z5,z6,z161]),(1,[z92,z1,z2,z3,z4,z82]),(0,[z92,z1,z2,z3,z4,z5,z82])],[(0,[z1,z126,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z162,z6])],[(0,[z61,z163,z2,z3,z4,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z165,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z167,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z102,z4,z83,z6]),(0,[z168,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z3,z171,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z172,z6]),(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z174]),(0,[z1,z2,z3,z4,z145,z5,z6]),(1,[z1,z2,z91,z4,z5,z6])],[(0,[z1,z2,z3,z4,z175,z5,z6]),(0,[z1,z2,z3,z176,z4,z5,z6]),(0,[z177,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z178,z4,z5,z6])],[(0,[z1,z2,z3,z4,z179,z5,z6]),(0,[z1,z2,z32,z3,z28,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z180])],[(0,[z73,z93,z2,z3,z4,z5,z6]),(0,[z1,z181,z2,z3,z4,z5,z6]),(0,[z182,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z183,z6]),(1,[z96,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z186,z5,z6])],[(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z34,z1,z2,z33,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z188])],[(0,[z1,z2,z3,z4,z189,z5,z6]),(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z191,z6]),(0,[z192,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z193,z6]),(1,[z1,z2,z3,z194,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z196,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z197]),(0,[z1,z2,z3,z4,z5,z198,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z199,z6]),(0,[z1,z2,z3,z4,z200,z5,z6])],[(0,[z19,z1,z2,z3,z4,z46,z6]),(0,[z201,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z202])],[(0,[z1,z2,z203,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z204,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z1,z2,z3,z4,z207,z5,z6]),(0,[z1,z2,z3,z4,z5,z208,z6])],[(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z2,z3,z211,z4,z5,z6]),(0,[z90,z1,z2,z3,z109,z5,z6])],[(0,[z212,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z4,z5,z77,z6]),(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z214,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z215,z6]),(0,[z1,z2,z3,z4,z6,z216,z217])],[(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6]),(0,[z1,z2,z219,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z4,z97,z5,z6]),(0,[z1,z2,z3,z4,z220,z5,z6])]],
   [[(0,[z1,z151,z3,z4,z20,z5,z6]),(0,[z1,z2,z3,z4,z221,z5,z6]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z1,z2,z3,z58,z4,z5,z6]),(0,[z223,z1,z2,z3,z4,z5,z6]),(0,[z1,z224,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z225,z5,z6])],[(0,[z73,z19,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z226,z4,z5,z6]),(1,[z108,z1,z3,z4,z20,z6])],[(1,[z1,z100,z101,z4,z5,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z228,z2,z3,z4,z5,z6])],[(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z1,z151,z3,z4,z5,z6,z217]),(0,[z1,z2,z3,z4,z5,z6,z229]),(0,[z108,z1,z2,z3,z4,z125,z6]),(0,[z230,z1,z2,z3,z4,z5,z6])],[(0,[z120,z1,z2,z3,z231,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z233,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z234]),(0,[z1,z2,z3,z4,z5,z6,z235]),(0,[z1,z2,z3,z4,z11,z6,z82])],[(0,[z1,z2,z3,z4,z236,z5,z6]),(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z238])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z92,z19,z1,z2,z3,z4,z6]),(0,[z239,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z130,z6,z217]),(0,[z64,z1,z2,z3,z97,z5,z6]),(1,[z15,z1,z2,z4,z5,z16])]],
   [[(0,[z240,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z241,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z242])],[(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z244,z1,z2,z3,z4,z5,z6]),(1,[z45,z2,z3,z4,z46,z6]),(0,[z245,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z246,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z2,z91,z3,z4,z5,z6])],[(0,[z1,z2,z3,z248,z4,z5,z6]),(0,[z1,z2,z3,z109,z99,z5,z6]),(0,[z1,z2,z3,z249,z4,z5,z6])],[(0,[z1,z2,z3,z250,z4,z5,z6]),(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z11,z6])],[(0,[z1,z2,z3,z252,z4,z5,z6]),(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z4,z5,z6,z16])],[(0,[z157,z1,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z231,z5,z6,z25]),(0,[z254,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z255,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z256]),(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z259,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z5,z6])],[(0,[z30,z1,z2,z219,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z261]),(0,[z262,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z263])]],
   [[(0,[z157,z1,z3,z4,z20,z5,z6]),(0,[z1,z2,z264,z3,z4,z5,z6]),(0,[z61,z1,z2,z3,z4,z5,z242]),(0,[z1,z265,z2,z3,z4,z5,z6]),(0,[z110,z1,z3,z63,z4,z5,z6]),(0,[z1,z2,z266,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z267,z6])],[(0,[z1,z2,z3,z4,z268,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z269]),(0,[z45,z1,z2,z3,z4,z270,z6]),(0,[z108,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z271]),(0,[z1,z2,z4,z83,z5,z77,z6]),(0,[z1,z2,z3,z4,z5,z6,z272])],[(0,[z1,z2,z3,z4,z5,z125,z6]),(0,[z1,z2,z3,z273,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z274]),(0,[z163,z1,z2,z3,z4,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6])],[(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z157,z1,z3,z4,z5,z6,z217]),(0,[z1,z2,z3,z4,z5,z277,z6]),(0,[z1,z2,z3,z4,z5,z278,z6]),(0,[z1,z2,z3,z4,z20,z260,z6]),(0,[z1,z2,z3,z4,z5,z279,z6])],[(0,[z280,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z120,z2,z3,z4,z99,z5,z6]),(0,[z282,z1,z2,z3,z4,z5,z6])],[(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z284,z2,z153,z3,z4,z5,z6]),(0,[z1,z2,z102,z3,z4,z5,z6])],[(0,[z1,z2,z285,z3,z4,z5,z6]),(0,[z286,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z287,z3,z4,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z100,z2,z3,z4,z5,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(0,[z289,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z290,z3,z4,z5,z6]),(0,[z291,z1,z2,z3,z4,z5,z6]),(0,[z292,z1,z2,z3,z4,z5,z6]),(0,[z108,z1,z137,z3,z4,z5,z6]),(1,[z1,z2,z3,z293,z5,z6]),(0,[z15,z1,z2,z3,z293,z5,z6]),(0,[z92,z1,z2,z3,z4,z260,z6]),(1,[z1,z2,z10,z4,z5,z6])],[(1,[z1,z2,z3,z4,z294,z6]),(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z296,z1,z2,z3,z4,z5,z6])],[(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z298,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z32,z35,z4,z5,z6])],[(0,[z299,z1,z2,z3,z4,z5,z6]),(0,[z300,z1,z2,z3,z4,z5,z6]),(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z302,z5,z6]),(0,[z108,z1,z3,z4,z20,z5,z6]),(1,[z1,z2,z3,z4,z246,z6]),(0,[z1,z303,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z102,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z304])],[(0,[z305,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z92,z1,z2,z3,z4,z6,z82])],[(0,[z1,z2,z3,z308,z4,z5,z6]),(0,[z1,z2,z3,z33,z109,z5,z6]),(0,[z22,z1,z2,z3,z109,z5,z6]),(0,[z1,z2,z3,z4,z5,z309,z6])]],
   [[(0,[z310,z1,z2,z3,z4,z5,z6]),(0,[z73,z1,z2,z3,z4,z311,z6]),(0,[z157,z1,z2,z3,z4,z189,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z1,z2,z3,z4,z260,z270,z6]),(0,[z1,z2,z3,z4,z5,z315,z6]),(0,[z1,z2,z3,z316,z4,z5,z6]),(0,[z1,z2,z3,z4,z317,z5,z6])],[(0,[z318,z1,z2,z3,z4,z5,z6])],[(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z320,z5,z6]),(0,[z1,z321,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z322,z6])],[(0,[z157,z93,z1,z3,z4,z5,z6]),(0,[z323,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z219,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z324])],[(0,[z1,z2,z3,z4,z5,z6,z325]),(0,[z1,z100,z101,z3,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z5,z326,z6]),(0,[z1,z2,z3,z4,z5,z6,z327]),(0,[z1,z328,z2,z3,z4,z5,z6])],[(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z194,z5,z6]),(0,[z1,z2,z3,z330,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z332,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z333,z6])],[(0,[z334,z1,z2,z3,z4,z6,z104]),(0,[z1,z2,z3,z4,z5,z6,z335]),(0,[z212,z336,z1,z3,z4,z5,z6]),(0,[z1,z2,z35,z4,z97,z5,z6])]],
   [[(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z338,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z339,z5,z6]),(0,[z73,z163,z2,z3,z4,z5,z6]),(0,[z19,z2,z3,z4,z5,z125,z6]),(1,[z1,z2,z3,z5,z340,z6]),(0,[z1,z2,z3,z341,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z342,z6])],[(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z344,z6]),(0,[z345,z1,z2,z3,z4,z5,z6]),(1,[z120,z2,z3,z99,z5,z6]),(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z1,z2,z3,z103,z4,z5,z6])],[(0,[z346,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z217]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z3,z5,z6,z25])],[(0,[z1,z2,z3,z4,z5,z311,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z5,z348,z6]),(0,[z1,z2,z349,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z350,z5,z6])],[(0,[z120,z1,z2,z3,z99,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z351]),(0,[z1,z2,z3,z4,z352,z5,z6]),(0,[z1,z2,z3,z4,z5,z353,z6])],[(0,[z1,z2,z3,z4,z5,z6,z354]),(0,[z19,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z100,z3,z4,z5,z6]),(0,[z1,z2,z3,z355,z4,z5,z6]),(0,[z356,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z4,z5,z77,z6])]],
   [[(0,[z1,z2,z3,z357,z4,z5,z6]),(0,[z157,z1,z2,z3,z4,z294,z6]),(1,[z358,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z359,z5,z6]),(0,[z1,z2,z3,z4,z360,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6]),(1,[z362,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z363,z6]),(0,[z1,z2,z3,z4,z364,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z153,z35,z4,z5,z6]),(0,[z120,z141,z2,z3,z4,z5,z6]),(0,[z15,z1,z2,z3,z4,z5,z6])],[(0,[z141,z2,z3,z231,z4,z5,z6]),(0,[z1,z2,z365,z3,z4,z5,z6]),(0,[z366,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z367,z6])],[(0,[z15,z1,z2,z3,z4,z5,z16])],[],[(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z369,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z370,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z371]),(0,[z1,z137,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z372,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z340,z6]),(0,[z1,z2,z3,z5,z11,z6,z373])],[(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z375,z4,z5,z6]),(0,[z61,z1,z2,z255,z4,z5,z6])],[(0,[z1,z2,z3,z4,z376,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z324])],[(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z378,z1,z2,z3,z4,z5,z6]),(1,[z336,z1,z3,z54,z5,z6])],[(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z380,z5,z6])],[(0,[z1,z2,z3,z4,z5,z381,z6]),(0,[z382,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z383,z3,z4,z5,z6]),(0,[z1,z47,z2,z3,z4,z6,z217]),(0,[z1,z2,z3,z4,z384,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z385]),(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z212,z1,z3,z4,z222,z5,z6]),(0,[z1,z2,z3,z4,z5,z387,z6]),(0,[z34,z1,z2,z3,z103,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z388,z6]),(1,[z343,z2,z39,z4,z5,z6]),(0,[z1,z389,z2,z3,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z125,z6]),(0,[z1,z2,z3,z4,z5,z390,z6])],[(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z19,z1,z2,z3,z4,z270,z6]),(0,[z392,z1,z2,z3,z4,z5,z6]),(1,[z334,z1,z2,z3,z4,z6]),(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z394,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z395,z4,z5,z6]),(0,[z396,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z397,z6]),(0,[z1,z398,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z5,z11])],[(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z400,z1,z2,z3,z4,z5,z6])],[(1,[z1,z401,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z402,z5,z6])],[(0,[z403,z1,z2,z3,z4,z5,z6]),(0,[z284,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z405]),(0,[z1,z406,z2,z3,z4,z5,z6])]],
   [[(0,[z157,z2,z151,z3,z4,z5,z6]),(0,[z407,z1,z2,z3,z4,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z409,z5,z6]),(0,[z1,z2,z410,z3,z4,z5,z6]),(0,[z34,z1,z2,z102,z4,z5,z6])],[(0,[z1,z2,z32,z33,z4,z5,z6]),(0,[z1,z2,z33,z4,z83,z5,z6]),(0,[z1,z2,z3,z411,z4,z5,z6])],[(0,[z1,z2,z412,z3,z4,z5,z6]),(0,[z343,z284,z2,z3,z4,z5,z6]),(0,[z1,z2,z413,z3,z4,z5,z6]),(0,[z1,z2,z3,z414,z4,z5,z6]),(0,[z1,z2,z415,z3,z4,z5,z6]),(0,[z1,z2,z102,z3,z4,z83,z6])],[(0,[z343,z2,z3,z39,z4,z5,z6])],[(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z101,z3,z63,z4,z5,z6]),(1,[z1,z2,z418,z4,z5,z6]),(0,[z1,z2,z3,z419,z4,z5,z6]),(0,[z1,z2,z3,z4,z420,z5,z6])],[(0,[z1,z2,z421,z3,z4,z5,z6]),(1,[z1,z137,z3,z4,z270,z6]),(0,[z1,z2,z3,z4,z5,z246,z6]),(0,[z1,z2,z3,z422,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z423,z6])],[(1,[z1,z2,z3,z4,z189,z6]),(0,[z1,z2,z3,z424,z4,z5,z6])],[(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z46,z260,z6]),(0,[z336,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(0,[z1,z2,z3,z427,z4,z5,z6]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z88,z1,z2,z3,z5,z77,z6])]],
   [[(0,[z429,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z430,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z431]),(0,[z336,z1,z2,z3,z222,z5,z6]),(0,[z1,z2,z432,z3,z4,z5,z6])],[(0,[z73,z2,z3,z4,z5,z6,z104]),(1,[z1,z2,z3,z4,z433,z6]),(0,[z1,z2,z3,z4,z5,z434,z6]),(0,[z1,z2,z4,z5,z37,z6,z16]),(0,[z1,z2,z435,z3,z4,z5,z6])],[(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z437,z6]),(0,[z108,z358,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z4,z23,z6])],[(0,[z1,z2,z3,z4,z46,z6,z82]),(0,[z1,z2,z3,z4,z5,z6,z438]),(0,[z108,z362,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z97,z5,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z37,z6])],[(0,[z1,z2,z3,z4,z5,z6,z441]),(0,[z442,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z443]),(0,[z1,z2,z444,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z25]),(0,[z1,z445,z2,z3,z4,z5,z6])],[(0,[z30,z1,z2,z3,z4,z333,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z5,z24,z6])],[(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z104]),(0,[z1,z2,z35,z3,z4,z5,z16])],[(0,[z163,z2,z151,z3,z4,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z448,z4,z5,z6]),(0,[z1,z2,z3,z449,z4,z5,z6]),(0,[z110,z1,z2,z63,z4,z5,z6]),(0,[z78,z1,z2,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z260,z5,z82])]],
   [[(0,[z1,z2,z63,z4,z5,z6,z16]),(0,[z92,z108,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z450,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z452])],[(0,[z1,z2,z3,z4,z5,z453,z6]),(0,[z61,z2,z3,z4,z5,z6,z104]),(0,[z1,z2,z454,z3,z4,z5,z6])],[(0,[z455,z1,z2,z3,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z46,z6]),(0,[z1,z2,z101,z3,z4,z5,z6]),(0,[z1,z2,z3,z54,z109,z5,z6]),(0,[z1,z2,z3,z4,z20,z5,z6]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z456])],[(1,[z1,z338,z3,z4,z5,z6]),(0,[z1,z2,z457,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z458,z5,z6]),(0,[z343,z1,z2,z39,z4,z5,z6])],[(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z460,z1,z2,z3,z4,z5,z6])],[(0,[z461,z1,z2,z3,z4,z5,z6]),(0,[z61,z1,z2,z3,z4,z5,z6])],[(0,[z93,z2,z151,z3,z4,z5,z6]),(0,[z462,z1,z2,z3,z4,z5,z6]),(0,[z1,z463,z2,z3,z4,z5,z6]),(0,[z90,z1,z2,z422,z4,z5,z6]),(0,[z1,z2,z3,z225,z5,z11,z6])]],
   [[(0,[z1,z2,z3,z464,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z465,z6])],[(1,[z110,z1,z63,z4,z5,z6]),(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z1,z2,z32,z4,z5,z6,z16]),(0,[z1,z467,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z468,z1,z2,z3,z4,z5,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z470,z3,z4,z5,z6]),(0,[z1,z2,z4,z97,z5,z6,z16]),(0,[z1,z471,z2,z3,z4,z5,z6])],[(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z1,z2,z3,z4,z28,z5,z6])],[(0,[z73,z1,z151,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z474,z6]),(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z1,z2,z3,z418,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z216]),(1,[z1,z2,z32,z33,z5,z6]),(0,[z476,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z477,z5,z6]),(0,[z358,z1,z2,z3,z4,z5,z6]),(0,[z478,z1,z2,z3,z4,z5,z6])],[(0,[z108,z1,z2,z3,z4,z270,z6]),(0,[z1,z2,z3,z4,z270,z6,z82]),(0,[z1,z2,z3,z479,z4,z5,z6])],[(0,[z2,z151,z3,z4,z5,z6,z104]),(0,[z1,z2,z39,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z480,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z481,z5,z6]),(0,[z1,z2,z3,z4,z5,z482,z6])],[(0,[z1,z483,z2,z3,z4,z5,z6]),(0,[z1,z484,z2,z3,z4,z5,z6]),(0,[z485,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z2,z3,z109,z4,z5,z24])],[(0,[z1,z2,z32,z3,z97,z5,z6]),(0,[z487,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z488,z6])],[],[(1,[z73,z157,z3,z4,z5,z6]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z1,z149,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490])],[(0,[z1,z2,z491,z3,z4,z5,z6]),(0,[z1,z2,z3,z492,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z83,z6])],[(0,[z493,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z494,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z134,z6]),(0,[z495,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z496,z1,z2,z3,z4,z5,z6]),(0,[z61,z1,z401,z3,z4,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6]),(1,[z498,z2,z3,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z500,z23,z6]),(1,[z1,z2,z3,z103,z28,z6])],[(0,[z163,z2,z3,z4,z5,z242,z6]),(0,[z1,z3,z54,z4,z222,z5,z6]),(0,[z30,z1,z3,z4,z5,z6,z217]),(0,[z501,z1,z2,z3,z4,z5,z6])],[(0,[z502,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z503,z6])],[(0,[z19,z2,z151,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z505,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z506])],[(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z508,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z509]),(0,[z1,z2,z3,z4,z510,z5,z6]),(0,[z1,z2,z3,z4,z5,z511,z6]),(0,[z1,z2,z3,z4,z5,z512,z6]),(0,[z1,z2,z3,z4,z5,z242,z6]),(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z513,z6]),(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z1,z515,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z516,z5,z6])],[(0,[z1,z2,z153,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z517,z5,z6])]],
   [[(0,[z518,z1,z2,z3,z4,z5,z6]),(0,[z1,z519,z2,z3,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z222,z5,z6]),(0,[z336,z1,z3,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z521]),(1,[z1,z2,z422,z4,z5,z6])],[(0,[z284,z1,z2,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z325,z104]),(0,[z1,z149,z2,z3,z4,z5,z217]),(0,[z522,z1,z2,z3,z4,z5,z6])],[(0,[z1,z149,z151,z3,z4,z5,z6]),(0,[z30,z442,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z4,z5,z25]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z524])],[(0,[z1,z2,z525,z3,z4,z5,z6]),(0,[z1,z2,z3,z477,z4,z5,z6]),(0,[z1,z2,z3,z4,z526,z5,z6]),(0,[z30,z1,z2,z418,z4,z5,z6])],[(0,[z527,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z125,z6,z82]),(0,[z528,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z15,z1,z2,z3,z4,z5,z37])],[(0,[z61,z1,z2,z3,z4,z433,z6]),(0,[z15,z1,z2,z35,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z529])],[(0,[z1,z2,z530,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z531,z6])],[(0,[z532,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z533,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z5,z6]),(0,[z534,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z535,z6]),(0,[z22,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z538,z5,z6]),(0,[z1,z2,z3,z4,z539,z5,z6]),(0,[z1,z2,z3,z4,z5,z540,z6]),(0,[z22,z1,z2,z3,z103,z5,z6]),(0,[z1,z2,z541,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z542,z5,z6]),(0,[z1,z2,z3,z4,z543,z5,z6]),(1,[z1,z2,z3,z544,z5,z6]),(0,[z1,z2,z3,z545,z4,z5,z6]),(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z547,z6]),(1,[z1,z2,z3,z109,z5,z24])],[(0,[z157,z1,z149,z3,z4,z5,z6]),(0,[z1,z2,z3,z63,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z548]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z550,z3,z4,z5,z6]),(0,[z1,z2,z3,z551,z4,z5,z6])],[(1,[z1,z2,z3,z4,z359,z6]),(0,[z1,z2,z3,z4,z552,z5,z6])],[(0,[z553,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z222,z5,z6,z25]),(0,[z1,z2,z3,z554,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z555])],[(0,[z1,z2,z3,z4,z556,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z558,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z559,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z145,z6]),(0,[z561,z1,z2,z3,z4,z5,z6])],[(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z563,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z564]),(0,[z1,z2,z3,z4,z5,z565,z6])],[(0,[z1,z2,z3,z4,z5,z566,z6]),(0,[z1,z2,z3,z567,z4,z5,z6]),(0,[z1,z2,z3,z4,z568,z5,z6]),(0,[z1,z2,z3,z4,z83,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z569]),(0,[z1,z2,z3,z4,z5,z23,z6])],[(0,[z1,z2,z3,z4,z5,z570,z6]),(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z3,z4,z5,z572,z6])],[(1,[z212,z1,z3,z222,z5,z6]),(0,[z1,z573,z2,z3,z4,z5,z6])],[(0,[z2,z153,z3,z39,z4,z5,z6]),(0,[z1,z2,z574,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z294,z6]),(0,[z576,z1,z2,z3,z4,z5,z6]),(1,[z19,z2,z3,z4,z125,z6]),(0,[z212,z1,z2,z3,z222,z5,z6]),(1,[z442,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z103,z28,z5,z6])],[(0,[z1,z52,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z3,z28,z5,z6]),(0,[z1,z2,z3,z28,z5,z6,z25]),(0,[z577,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z343,z1,z2,z153,z4,z5,z6]),(0,[z1,z2,z3,z4,z578,z5,z6]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z581])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z544,z5,z6]),(0,[z61,z1,z2,z3,z477,z5,z6]),(0,[z1,z2,z3,z33,z5,z6,z25]),(0,[z22,z1,z2,z3,z5,z6,z25]),(0,[z1,z582,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z99,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z104]),(0,[z1,z2,z3,z583,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584]),(0,[z1,z2,z3,z4,z585,z5,z6])],[(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z587,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z20,z6]),(0,[z1,z100,z2,z63,z4,z5,z6]),(0,[z1,z2,z3,z4,z588,z5,z6])],[(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z590,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z3,z591,z4,z5,z6]),(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z216]),(0,[z64,z22,z1,z2,z3,z5,z6]),(0,[z593,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z594])],[(0,[z1,z2,z3,z4,z595,z5,z6]),(0,[z1,z596,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z598,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z1,z600,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6]),(0,[z1,z2,z3,z4,z5,z602,z6]),(0,[z1,z2,z3,z225,z4,z5,z6])],[(1,[z1,z2,z3,z31,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z130]),(0,[z1,z2,z3,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z5,z6,z603])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z604]),(0,[z605,z1,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z20,z5,z270,z6]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z1,z2,z102,z4,z83,z5,z6])],[(0,[z1,z2,z3,z606,z4,z5,z6]),(1,[z93,z151,z3,z4,z5,z6]),(0,[z1,z2,z33,z4,z97,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z607]),(1,[z1,z2,z3,z4,z260,z11])],[(0,[z608,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z231,z109,z5,z6]),(0,[z61,z1,z2,z3,z4,z134,z6]),(0,[z1,z2,z3,z4,z5,z6,z609]),(0,[z1,z2,z3,z610,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z611]),(0,[z1,z612,z2,z3,z4,z5,z6]),(0,[z613,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z2,z3,z615,z4,z5,z6]),(0,[z1,z2,z616,z3,z4,z5,z6]),(0,[z30,z1,z149,z3,z4,z5,z6]),(0,[z617,z1,z2,z3,z4,z5,z6])],[(0,[z110,z1,z2,z101,z4,z5,z6]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z1,z2,z35,z3,z4,z5,z37]),(0,[z1,z2,z619,z3,z4,z5,z6])],[(0,[z620,z1,z2,z3,z4,z5,z6]),(0,[z1,z137,z151,z3,z4,z5,z6]),(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z623,z3,z4,z5,z6])],[(0,[z1,z2,z151,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z624,z6]),(0,[z625,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z626]),(0,[z30,z498,z2,z3,z4,z5,z6]),(1,[z30,z1,z3,z4,z5,z217]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z35,z4,z5,z37,z6])]],
   [[(0,[z1,z2,z628,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z629,z6]),(0,[z1,z2,z3,z630,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z631,z6])],[(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z633,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z217])],[(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z635,z4,z5,z6]),(1,[z1,z2,z62,z4,z5,z6]),(0,[z1,z137,z2,z3,z4,z270,z6])],[(0,[z1,z2,z401,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z636,z5,z6]),(0,[z1,z2,z637,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z638]),(0,[z92,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z639])],[(0,[z1,z2,z255,z3,z4,z5,z6])],[(0,[z1,z2,z101,z35,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z640]),(0,[z1,z2,z3,z4,z5,z6,z641]),(0,[z1,z2,z3,z4,z5,z642,z6]),(1,[z1,z2,z4,z5,z500,z6])],[(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z644,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z645,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z34,z22,z1,z2,z3,z4,z6]),(0,[z22,z1,z2,z3,z4,z23,z6]),(0,[z647,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z73,z1,z2,z3,z4,z359,z6]),(0,[z45,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z648,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z649,z6]),(0,[z1,z2,z3,z4,z650,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z653,z2,z3,z4,z5,z6])],[(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z656,z6]),(0,[z1,z2,z3,z103,z4,z28,z6])],[(0,[z1,z2,z3,z4,z5,z6,z657]),(0,[z45,z19,z2,z3,z4,z5,z6]),(0,[z92,z45,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z658,z5,z6]),(0,[z64,z1,z2,z32,z4,z5,z6]),(0,[z1,z659,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z83,z5,z6,z16]),(0,[z1,z660,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z11,z6,z324])],[(0,[z1,z2,z3,z661,z4,z5,z6]),(0,[z2,z3,z4,z5,z242,z6,z104]),(0,[z1,z2,z3,z4,z662,z5,z6])],[(0,[z284,z1,z2,z153,z4,z5,z6]),(1,[z141,z2,z3,z231,z5,z6]),(0,[z61,z1,z2,z3,z544,z5,z6]),(0,[z663,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z664]),(0,[z1,z2,z665,z3,z4,z5,z6]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z4,z83,z5,z6]),(1,[z1,z2,z3,z5,z6,z373])],[(0,[z45,z1,z2,z3,z4,z125,z6]),(0,[z1,z2,z3,z4,z5,z6,z667]),(0,[z1,z2,z3,z4,z5,z6,z668]),(0,[z1,z2,z3,z4,z5,z6,z669])]],
   [[(0,[z73,z157,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z333,z5,z6]),(0,[z1,z2,z3,z4,z5,z670,z6])],[(1,[z1,z2,z3,z4,z6,z325]),(0,[z1,z2,z102,z3,z4,z77,z6]),(0,[z1,z2,z3,z4,z671,z5,z6]),(1,[z90,z1,z2,z3,z5,z25])],[(0,[z672,z1,z2,z3,z4,z5,z6]),(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z674])],[(0,[z1,z2,z3,z4,z675,z5,z6]),(1,[z1,z126,z3,z4,z5,z6])],[(0,[z1,z2,z3,z676,z4,z5,z6])],[(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z678,z5,z6]),(0,[z1,z2,z3,z679,z4,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6])],[(0,[z681,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z682,z3,z4,z5,z6]),(0,[z1,z2,z683,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z684,z5,z6]),(0,[z1,z137,z3,z4,z5,z270,z6]),(0,[z1,z2,z3,z4,z5,z6,z685])],[(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z687]),(1,[z163,z2,z3,z4,z5,z242]),(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z11,z6])]],
   [[(1,[z284,z2,z153,z4,z5,z6]),(0,[z1,z2,z3,z231,z4,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z1,z2,z3,z4,z690,z5,z6])],[(1,[z1,z2,z3,z4,z311,z6]),(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z2,z3,z4,z692,z5,z6])],[(0,[z141,z1,z2,z3,z231,z5,z6]),(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z694]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z433,z5,z6]),(0,[z1,z2,z3,z54,z4,z5,z6]),(0,[z108,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z695,z6]),(0,[z1,z2,z3,z109,z4,z5,z6])],[(0,[z2,z3,z231,z4,z99,z5,z6]),(1,[z1,z52,z3,z4,z5,z6]),(0,[z1,z149,z3,z4,z5,z130,z6]),(0,[z1,z2,z3,z5,z340,z77,z6]),(0,[z1,z2,z3,z696,z4,z5,z6])],[(0,[z697,z1,z2,z3,z4,z5,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z699,z6]),(0,[z22,z1,z2,z3,z4,z28,z6]),(0,[z700,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z701,z6]),(0,[z702,z1,z2,z3,z4,z5,z6]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z10,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z260,z125,z6]),(0,[z1,z2,z3,z4,z5,z6,z373])],[(0,[z704,z1,z2,z3,z4,z5,z6]),(0,[z45,z2,z3,z4,z46,z5,z6]),(0,[z705,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z336,z1,z2,z3,z54,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z312,z151,z3,z4,z5,z6]),(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z2,z708,z4,z5,z6]),(0,[z1,z2,z3,z4,z709,z6]),(0,[z2,z153,z710,z4,z5,z6]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z4,z83,z565,z6]),(0,[z1,z2,z712,z4,z5,z6])],[(0,[z93,z151,z3,z4,z5,z6]),(1,[z78,z22,z1,z2,z6]),(0,[z1,z2,z3,z4,z260,z11])],[(0,[z1,z2,z3,z4,z294,z6]),(0,[z297,z151,z3,z4,z5,z6]),(0,[z157,z1,z3,z4,z359,z6]),(0,[z1,z713,z3,z4,z5,z6]),(0,[z19,z26,z2,z3,z4,z6]),(0,[z561,z2,z3,z4,z46,z6]),(0,[z1,z714,z2,z3,z4,z6]),(1,[z1,z2,z3,z5,z715])],[(0,[z1,z2,z3,z716,z5,z6]),(0,[z686,z1,z3,z4,z20,z6]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z1,z2,z718,z4,z5,z6]),(0,[z108,z1,z3,z4,z6,z581])]],
   [[(0,[z1,z719,z3,z4,z5,z6]),(0,[z1,z2,z3,z720,z5,z6])],[(0,[z721,z93,z3,z4,z5,z6]),(0,[z1,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z723,z5,z6]),(0,[z110,z1,z63,z4,z5,z6]),(0,[z724,z2,z3,z4,z5,z6]),(0,[z1,z137,z3,z4,z725,z6]),(0,[z1,z2,z726,z4,z5,z6]),(0,[z1,z2,z3,z194,z246,z6]),(0,[z727,z1,z2,z3,z4,z6]),(0,[z64,z1,z2,z97,z5,z6]),(0,[z1,z2,z3,z4,z6,z728])],[(1,[z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z729,z5,z6]),(0,[z1,z2,z3,z4,z730,z6]),(0,[z22,z1,z2,z133,z3,z6]),(0,[z88,z1,z2,z83,z5,z6])],[(0,[z1,z2,z3,z4,z731,z6]),(0,[z1,z2,z3,z732,z5,z6]),(0,[z1,z401,z255,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z733]),(0,[z1,z2,z3,z4,z734,z6]),(0,[z1,z2,z97,z5,z6,z641]),(0,[z1,z2,z102,z4,z42,z6])]],
   [[(0,[z1,z2,z735,z4,z5,z6]),(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z52,z3,z4,z11,z6]),(0,[z1,z3,z737,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z738]),(0,[z1,z2,z3,z4,z739,z6]),(0,[z92,z1,z2,z3,z4,z584]),(0,[z1,z2,z3,z4,z6,z216]),(0,[z1,z3,z4,z20,z725,z6]),(0,[z1,z740,z3,z4,z5,z6])],[(0,[z1,z2,z3,z477,z5,z6]),(0,[z1,z2,z3,z477,z134,z6]),(0,[z30,z498,z3,z4,z5,z217]),(0,[z298,z1,z2,z3,z5,z25]),(0,[z1,z2,z35,z293,z5,z6]),(0,[z15,z1,z2,z58,z5,z16])],[(0,[z288,z151,z3,z4,z5,z6]),(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z126,z3,z477,z5,z6]),(0,[z1,z2,z3,z742,z5,z6]),(0,[z1,z2,z35,z4,z5,z629]),(0,[z743,z2,z3,z4,z5,z6]),(0,[z1,z149,z3,z4,z5,z130]),(0,[z1,z2,z4,z5,z6,z324]),(0,[z1,z744,z3,z4,z5,z6])],[(0,[z1,z52,z3,z4,z294,z6]),(0,[z1,z137,z3,z4,z294,z6]),(0,[z1,z2,z3,z4,z745,z6]),(0,[z2,z3,z4,z5,z6,z746]),(0,[z1,z2,z4,z5,z6,z747])]],
   [[(0,[z1,z2,z3,z748,z5,z6]),(0,[z1,z2,z3,z5,z6,z749]),(0,[z750,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z500,z6]),(0,[z751,z2,z3,z4,z5,z6])],[(0,[z343,z2,z710,z4,z5,z6]),(0,[z1,z752,z3,z4,z5,z6]),(0,[z1,z2,z3,z753,z5,z6]),(0,[z1,z2,z3,z4,z333,z6]),(0,[z1,z2,z3,z754,z5,z6]),(0,[z64,z1,z2,z145,z97,z6]),(0,[z96,z1,z2,z35,z4,z6]),(0,[z1,z2,z66,z33,z5,z6]),(1,[z1,z2,z4,z5,z755]),(0,[z1,z2,z10,z225,z5,z6])],[(0,[z1,z3,z4,z20,z294,z6]),(0,[z2,z3,z756,z99,z5,z6]),(0,[z2,z3,z4,z5,z6,z757]),(0,[z34,z1,z2,z4,z695,z6]),(0,[z1,z2,z4,z5,z6,z758])],[(0,[z462,z1,z3,z4,z5,z217]),(0,[z1,z2,z759,z4,z5,z6]),(0,[z442,z2,z418,z4,z5,z6]),(0,[z64,z1,z2,z341,z5,z6]),(0,[z1,z3,z4,z5,z6,z760]),(0,[z761,z1,z2,z4,z5,z6]),(1,[z1,z2,z3,z4,z728])]],
   [[(0,[z1,z2,z762,z4,z5,z6]),(0,[z2,z3,z4,z46,z763,z6]),(0,[z61,z2,z3,z544,z5,z104]),(0,[z92,z1,z2,z3,z4,z82])],[(0,[z19,z2,z3,z4,z595,z6]),(0,[z1,z2,z3,z764,z5,z6]),(1,[z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z766,z5,z6]),(1,[z1,z2,z767,z5,z6]),(0,[z1,z2,z3,z28,z210,z6])],[(0,[z1,z2,z3,z768,z5,z6]),(0,[z1,z2,z3,z4,z769,z6]),(0,[z245,z157,z3,z4,z5,z6]),(0,[z1,z2,z737,z4,z5,z6]),(0,[z770,z2,z3,z4,z5,z6]),(0,[z192,z1,z2,z3,z5,z25]),(0,[z1,z2,z3,z109,z5,z183]),(0,[z498,z149,z3,z4,z5,z6])],[(0,[z721,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z771,z5,z6]),(0,[z1,z2,z3,z4,z5,z772]),(0,[z92,z358,z2,z3,z4,z6]),(0,[z15,z1,z2,z293,z5,z16]),(0,[z90,z1,z2,z422,z5,z25])]],
   [[(0,[z73,z2,z3,z4,z189,z6]),(1,[z2,z3,z756,z5,z6]),(0,[z1,z2,z773,z4,z5,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z91,z4,z5,z6])],[(0,[z334,z2,z151,z3,z4,z6]),(0,[z1,z775,z3,z4,z5,z6]),(0,[z776,z2,z3,z4,z5,z6]),(0,[z22,z1,z2,z500,z23,z6]),(0,[z78,z22,z1,z2,z4,z6]),(0,[z1,z2,z3,z5,z6,z373])],[(0,[z258,z151,z3,z4,z5,z6]),(0,[z451,z1,z2,z97,z5,z6]),(0,[z78,z22,z1,z2,z5,z6])],[(0,[z358,z2,z3,z4,z5,z6]),(0,[z157,z721,z3,z4,z5,z6]),(0,[z1,z149,z3,z4,z5,z777]),(0,[z96,z1,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z778,z3,z4,z6]),(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z325]),(0,[z780,z2,z3,z4,z5,z6]),(1,[z1,z737,z4,z5,z6]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z1,z2,z782,z4,z5,z6]),(0,[z90,z1,z2,z3,z5,z25])],[(0,[z45,z338,z3,z4,z46,z6]),(0,[z1,z2,z4,z5,z6,z783]),(1,[z34,z88,z1,z2,z6]),(0,[z1,z2,z4,z5,z784,z6])],[(0,[z1,z2,z3,z4,z785,z6]),(0,[z61,z2,z3,z4,z325,z104]),(0,[z1,z2,z3,z194,z5,z6]),(0,[z1,z2,z786,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z787])],[(0,[z788,z1,z2,z3,z4,z6]),(0,[z1,z789,z3,z4,z5,z6]),(0,[z1,z401,z62,z4,z5,z6]),(0,[z1,z401,z3,z477,z5,z6]),(0,[z498,z2,z3,z194,z5,z6]),(0,[z34,z1,z2,z341,z4,z6])]],
   [[(0,[z1,z2,z790,z4,z5,z6]),(0,[z45,z2,z3,z4,z314,z6]),(0,[z1,z2,z3,z4,z791,z6]),(0,[z1,z2,z422,z4,z5,z6])],[(0,[z792,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z793,z6]),(0,[z2,z3,z4,z46,z311,z6]),(0,[z73,z157,z3,z4,z311,z6]),(0,[z1,z2,z4,z5,z6,z794]),(0,[z1,z2,z3,z795,z5,z6]),(0,[z401,z3,z4,z5,z6,z104]),(0,[z61,z2,z255,z4,z5,z104]),(0,[z163,z2,z3,z4,z5,z765]),(0,[z796,z2,z3,z4,z5,z6]),(0,[z1,z2,z797,z4,z5,z6]),(0,[z442,z2,z3,z4,z246,z6]),(0,[z798,z1,z3,z4,z5,z6]),(0,[z799,z1,z2,z4,z5,z6])],[(0,[z163,z2,z3,z4,z5,z242]),(0,[z1,z2,z3,z4,z800,z6]),(0,[z1,z2,z418,z4,z246,z6]),(0,[z1,z2,z3,z5,z801,z6])],[(0,[z1,z2,z4,z767,z5,z6]),(0,[z34,z1,z2,z340,z77,z6]),(0,[z1,z2,z3,z28,z801,z6])]],
   [[(0,[z1,z2,z3,z4,z311,z6]),(0,[z2,z3,z710,z4,z5,z6]),(0,[z45,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z4,z802,z6]),(0,[z30,z1,z418,z4,z5,z217]),(0,[z64,z96,z1,z2,z97,z6])],[(0,[z141,z2,z3,z756,z5,z6]),(0,[z1,z2,z3,z4,z803,z6]),(0,[z61,z334,z2,z3,z4,z104]),(0,[z366,z1,z2,z4,z5,z16]),(0,[z804,z2,z3,z4,z5,z6]),(0,[z64,z1,z2,z517,z5,z6])],[(0,[z1,z52,z3,z4,z5,z6]),(0,[z1,z2,z805,z4,z5,z6]),(0,[z2,z3,z4,z763,z125,z6]),(0,[z1,z100,z737,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z806])],[(0,[z1,z2,z3,z4,z6,z807]),(0,[z61,z2,z3,z4,z433,z104]),(0,[z1,z328,z3,z4,z270,z6]),(0,[z442,z2,z219,z4,z5,z6]),(0,[z96,z1,z2,z3,z109,z6]),(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z3,z5,z24,z715])]],
   [[(0,[z19,z151,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z808,z6]),(0,[z1,z2,z3,z4,z6,z809]),(0,[z1,z2,z3,z5,z6,z810]),(0,[z1,z2,z3,z811,z5,z6]),(0,[z812,z2,z3,z4,z5,z6]),(0,[z282,z1,z2,z3,z4,z82]),(0,[z22,z1,z2,z3,z801,z6])],[(0,[z1,z2,z4,z5,z813,z6]),(0,[z1,z2,z3,z814,z5,z6]),(0,[z73,z157,z3,z4,z359,z6]),(0,[z1,z815,z3,z4,z5,z6]),(0,[z1,z2,z3,z225,z5,z6])],[(0,[z137,z151,z3,z4,z46,z6]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z817,z1,z2,z3,z4,z6])],[(0,[z1,z2,z3,z818,z5,z6]),(0,[z163,z2,z3,z4,z5,z187]),(0,[z343,z2,z39,z4,z5,z6]),(0,[z557,z2,z3,z99,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z359,z6]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z2,z62,z4,z433,z6]),(0,[z1,z2,z255,z477,z5,z6]),(0,[z2,z3,z4,z5,z242,z765]),(0,[z1,z2,z4,z5,z821,z6])],[(0,[z1,z52,z3,z4,z46,z6]),(0,[z358,z2,z3,z4,z270,z6])],[(0,[z151,z3,z4,z243,z5,z6]),(0,[z92,z1,z52,z3,z4,z6]),(0,[z822,z2,z3,z4,z5,z6]),(0,[z823,z1,z2,z3,z5,z6]),(0,[z824,z2,z3,z4,z5,z6])],[(0,[z19,z338,z3,z4,z5,z6]),(0,[z468,z1,z2,z3,z4,z82]),(0,[z358,z2,z3,z4,z20,z6]),(0,[z1,z3,z4,z5,z130,z777]),(0,[z15,z1,z2,z4,z5,z16]),(0,[z1,z2,z3,z5,z279,z25])]],
   [[(0,[z1,z2,z3,z5,z825,z6]),(0,[z108,z362,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z145,z6]),(0,[z1,z2,z3,z826,z5,z6])],[(0,[z1,z2,z4,z5,z6,z827]),(0,[z92,z1,z2,z3,z4,z687]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z1,z3,z54,z720,z5,z6]),(0,[z64,z96,z1,z2,z5,z6])],[(0,[z13,z1,z2,z3,z5,z25]),(0,[z30,z1,z3,z4,z246,z217]),(0,[z1,z2,z102,z4,z829,z6]),(0,[z1,z2,z422,z5,z6,z25])],[(0,[z1,z2,z3,z4,z6,z830]),(0,[z831,z1,z2,z4,z5,z6]),(0,[z832,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z833,z5,z6]),(0,[z834,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z5,z206])]],
   [[(0,[z1,z2,z3,z4,z835,z6]),(0,[z1,z2,z4,z5,z6,z836]),(0,[z1,z2,z3,z4,z837,z6]),(0,[z1,z2,z3,z4,z838,z6]),(0,[z487,z1,z3,z222,z5,z6]),(0,[z1,z47,z2,z3,z4,z6]),(0,[z839,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z755])],[(0,[z1,z2,z710,z4,z5,z6]),(0,[z152,z1,z2,z4,z5,z16]),(0,[z1,z2,z3,z4,z840,z6]),(0,[z61,z2,z62,z4,z5,z104]),(0,[z1,z2,z35,z4,z5,z601])],[(0,[z442,z2,z3,z4,z5,z6]),(0,[z19,z2,z3,z4,z125,z6]),(0,[z1,z2,z3,z4,z841,z6]),(0,[z1,z2,z219,z4,z246,z6])],[(0,[z1,z2,z842,z4,z5,z6]),(0,[z108,z1,z3,z4,z207,z6]),(0,[z1,z2,z418,z4,z5,z6]),(0,[z1,z2,z843,z3,z4,z6]),(0,[z90,z1,z2,z91,z5,z25])]],
   [[(0,[z1,z52,z3,z4,z270,z6]),(0,[z1,z2,z3,z4,z6,z844]),(0,[z498,z2,z418,z4,z5,z6]),(0,[z1,z2,z3,z58,z5,z6]),(0,[z1,z2,z3,z801,z23,z6])],[(0,[z1,z2,z3,z4,z189,z6]),(0,[z1,z2,z845,z4,z5,z6]),(0,[z1,z2,z3,z846,z5,z6]),(1,[z2,z710,z4,z5,z6]),(0,[z1,z2,z3,z4,z847,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z1,z3,z4,z720,z5,z6]),(0,[z1,z2,z3,z31,z333,z6]),(0,[z849,z2,z3,z4,z5,z6])],[(0,[z1,z151,z3,z4,z359,z6]),(0,[z1,z2,z3,z850,z5,z6]),(0,[z1,z52,z3,z4,z20,z6]),(0,[z61,z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z3,z4,z852,z6]),(0,[z853,z2,z3,z4,z5,z6])],[(0,[z1,z2,z854,z4,z5,z6]),(0,[z1,z2,z855,z4,z5,z6]),(0,[z156,z1,z3,z4,z20,z6]),(0,[z34,z1,z2,z4,z473,z6]),(0,[z1,z2,z3,z4,z5,z856])]],
   [[(0,[z1,z2,z857,z4,z5,z6]),(0,[z1,z2,z3,z4,z433,z6]),(0,[z1,z2,z3,z4,z858,z6])],[(0,[z1,z126,z3,z4,z433,z6]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z860,z2,z3,z4,z5,z6]),(0,[z442,z2,z3,z194,z5,z6]),(0,[z1,z2,z3,z4,z5,z861]),(0,[z501,z1,z2,z97,z5,z6]),(0,[z22,z1,z2,z3,z309,z6])],[(0,[z1,z2,z3,z4,z862,z6]),(0,[z1,z2,z3,z4,z863,z6]),(0,[z1,z864,z3,z4,z5,z6]),(0,[z865,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z866]),(0,[z1,z2,z3,z867,z5,z6])],[(0,[z868,z1,z2,z3,z4,z6]),(0,[z1,z137,z3,z4,z381,z6]),(0,[z1,z2,z3,z4,z6,z869]),(0,[z163,z401,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z801,z6])]],
   [[(0,[z870,z1,z2,z4,z5,z6]),(0,[z1,z2,z871,z4,z5,z6]),(0,[z1,z2,z62,z477,z5,z6]),(0,[z1,z2,z3,z4,z260,z76]),(0,[z30,z1,z3,z4,z5,z777]),(0,[z298,z1,z2,z4,z5,z16]),(0,[z1,z2,z33,z5,z670,z6]),(0,[z1,z2,z3,z103,z801,z6]),(0,[z1,z2,z422,z109,z5,z6])],[(0,[z1,z2,z3,z4,z872,z6]),(0,[z873,z2,z3,z4,z5,z6]),(0,[z34,z88,z1,z2,z3,z6]),(0,[z1,z2,z4,z5,z829,z6])],[(0,[z245,z2,z3,z4,z46,z6]),(0,[z2,z3,z4,z5,z765,z104]),(0,[z1,z2,z3,z293,z5,z6]),(0,[z1,z2,z10,z4,z5,z6]),(0,[z78,z22,z1,z2,z23,z6])],[(0,[z1,z2,z3,z4,z874,z6]),(0,[z1,z875,z3,z4,z5,z6]),(0,[z1,z137,z349,z3,z4,z6]),(0,[z1,z2,z35,z4,z5,z656])]],
   [[(0,[z358,z2,z3,z4,z11,z6]),(0,[z22,z1,z2,z3,z473,z6]),(0,[z1,z2,z32,z5,z348,z6]),(0,[z1,z2,z3,z109,z5,z572])],[(0,[z1,z2,z3,z876,z5,z6]),(0,[z61,z2,z3,z4,z5,z104]),(0,[z61,z2,z3,z4,z134,z104]),(0,[z877,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z246,z6])],[(0,[z329,z151,z3,z4,z5,z6]),(0,[z878,z1,z2,z3,z4,z6]),(0,[z61,z126,z3,z4,z5,z104]),(0,[z498,z2,z3,z4,z246,z6]),(0,[z34,z1,z2,z4,z829,z6]),(0,[z1,z2,z879,z4,z5,z6])],[(0,[z1,z2,z3,z4,z880,z6]),(0,[z1,z2,z3,z4,z881,z6]),(0,[z1,z2,z3,z882,z5,z6]),(0,[z1,z137,z3,z4,z693,z6]),(0,[z1,z2,z883,z4,z5,z6]),(0,[z30,z1,z3,z4,z5,z217])]],
   [[(0,[z1,z2,z884,z4,z5,z6]),(0,[z885,z1,z3,z4,z5,z6]),(0,[z1,z2,z886,z4,z5,z6]),(0,[z1,z2,z255,z544,z5,z6]),(0,[z30,z442,z3,z4,z5,z217]),(0,[z92,z1,z2,z3,z4,z728])],[(0,[z1,z2,z3,z887,z5,z6]),(1,[z1,z3,z4,z725,z6]),(0,[z78,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z5,z888,z6]),(0,[z78,z1,z2,z103,z4,z6]),(0,[z1,z2,z3,z4,z5,z715])],[(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z2,z62,z4,z5,z6]),(0,[z605,z2,z153,z4,z5,z6]),(0,[z1,z2,z62,z4,z134,z6]),(0,[z2,z3,z4,z5,z6,z765]),(0,[z110,z1,z737,z4,z5,z6])],[(0,[z890,z1,z2,z3,z4,z5]),(0,[z358,z2,z3,z4,z125,z6]),(0,[z1,z126,z62,z4,z5,z6]),(0,[z1,z2,z219,z4,z5,z6]),(0,[z96,z1,z2,z3,z6,z25]),(0,[z1,z2,z3,z891,z5,z6]),(0,[z90,z1,z2,z3,z5,z715])]],
   [[(0,[z1,z2,z3,z4,z892,z6]),(0,[z1,z3,z4,z5,z6,z893]),(0,[z894,z1,z2,z3,z5,z6]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z896]),(0,[z523,z1,z3,z54,z5,z6]),(0,[z897,z1,z2,z3,z4,z6]),(0,[z498,z2,z219,z4,z5,z6])],[(0,[z446,z1,z2,z97,z5,z6]),(0,[z1,z3,z4,z5,z6,z898])],[(0,[z73,z686,z3,z4,z5,z6]),(0,[z1,z2,z899,z4,z5,z6]),(0,[z1,z401,z3,z4,z433,z6]),(0,[z1,z2,z3,z544,z433,z6]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z30,z1,z3,z194,z5,z217]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z728])],[(0,[z1,z902,z2,z3,z4,z6]),(0,[z903,z1,z2,z4,z5,z6]),(0,[z1,z2,z904,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z638]),(0,[z498,z2,z3,z4,z333,z6]),(0,[z1,z2,z32,z33,z5,z6]),(0,[z96,z1,z2,z32,z3,z6]),(0,[z1,z2,z4,z5,z755,z16])]],
   [[(0,[z19,z2,z3,z4,z311,z6]),(0,[z1,z905,z3,z4,z5,z6]),(1,[z1,z2,z4,z829,z6])],[(0,[z1,z2,z3,z756,z5,z6]),(0,[z1,z906,z3,z4,z5,z6]),(0,[z165,z2,z3,z4,z125,z6]),(1,[z1,z3,z720,z5,z6]),(0,[z1,z2,z3,z5,z340,z6])],[(0,[z721,z2,z3,z4,z5,z6]),(0,[z120,z2,z3,z99,z5,z6]),(0,[z1,z3,z4,z5,z6,z907]),(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z2,z3,z4,z909,z6]),(0,[z1,z2,z219,z194,z5,z6]),(0,[z88,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z2,z911,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z912]),(1,[z64,z96,z1,z2,z6]),(0,[z1,z2,z3,z913,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z763,z6]),(0,[z914,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z915]),(0,[z1,z2,z3,z225,z260,z11])],[(0,[z284,z2,z710,z4,z5,z6]),(0,[z141,z2,z3,z231,z5,z6]),(0,[z916,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z917,z5,z6]),(0,[z1,z2,z3,z194,z333,z6]),(0,[z34,z1,z2,z4,z77,z6]),(0,[z1,z2,z4,z83,z6,z456]),(0,[z918,z2,z3,z4,z5,z6])],[(0,[z151,z3,z4,z5,z6,z506]),(0,[z73,z40,z3,z4,z5,z6]),(0,[z1,z52,z3,z4,z125,z6]),(0,[z1,z2,z919,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z920]),(0,[z1,z2,z3,z5,z6,z921]),(0,[z1,z2,z922,z4,z5,z6])],[(0,[z73,z157,z3,z4,z5,z6]),(0,[z1,z2,z923,z4,z5,z6]),(0,[z1,z924,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z925,z6]),(0,[z61,z401,z3,z4,z5,z104]),(0,[z1,z2,z3,z4,z5,z728])]],
   [[(0,[z926,z1,z2,z4,z5,z6]),(1,[z2,z3,z4,z763,z6]),(0,[z1,z2,z927,z4,z5,z6]),(0,[z928,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z929,z6]),(0,[z930,z2,z3,z4,z5,z6]),(0,[z78,z22,z1,z2,z3,z6])],[(0,[z362,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z932,z2,z3,z4,z5,z6]),(0,[z1,z137,z3,z4,z314,z6]),(0,[z30,z1,z47,z3,z4,z217]),(0,[z933,z1,z2,z3,z5,z6]),(0,[z934,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z149,z3,z4,z5,z295]),(0,[z1,z2,z3,z4,z935,z6]),(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z2,z3,z4,z134,z6]),(0,[z30,z1,z3,z4,z216,z217]),(0,[z1,z2,z102,z4,z83,z6])],[(0,[z1,z126,z3,z4,z5,z6]),(0,[z498,z2,z3,z4,z5,z6]),(0,[z1,z126,z3,z4,z134,z6]),(0,[z1,z2,z255,z4,z433,z6]),(0,[z34,z88,z1,z2,z77,z6]),(0,[z1,z2,z3,z103,z28,z6])]],
   [[(0,[z73,z334,z2,z3,z4,z6]),(0,[z1,z937,z3,z4,z5,z6]),(0,[z1,z2,z3,z938,z5,z6]),(0,[z1,z2,z939,z4,z5,z6]),(0,[z1,z2,z62,z544,z5,z6]),(0,[z1,z2,z940,z4,z5,z6]),(0,[z64,z1,z2,z352,z5,z6])],[(0,[z1,z2,z3,z4,z941,z6]),(0,[z1,z2,z3,z4,z942,z6]),(0,[z1,z2,z3,z4,z943,z6]),(0,[z944,z2,z3,z4,z5,z6]),(0,[z945,z1,z2,z3,z5,z6]),(0,[z1,z2,z293,z5,z6,z16]),(0,[z1,z3,z4,z5,z6,z946])],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z442,z2,z3,z31,z5,z6]),(0,[z34,z1,z2,z630,z4,z6]),(0,[z1,z2,z3,z949,z5,z6]),(0,[z1,z2,z3,z5,z6,z715])],[(0,[z1,z2,z3,z4,z950,z6]),(0,[z1,z2,z3,z951,z5,z6]),(0,[z1,z2,z3,z4,z11,z174]),(0,[z1,z737,z63,z4,z5,z6]),(0,[z1,z101,z737,z4,z5,z6]),(0,[z952,z2,z3,z4,z5,z6]),(0,[z1,z2,z418,z31,z5,z6]),(0,[z22,z1,z2,z3,z352,z6]),(0,[z1,z2,z4,z5,z247,z16])]],
   [[(0,[z721,z151,z3,z4,z5,z6]),(0,[z284,z2,z153,z4,z5,z6]),(0,[z1,z953,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z777]),(0,[z1,z2,z33,z767,z5,z6])],[(0,[z276,z151,z3,z4,z5,z6]),(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z649]),(0,[z1,z2,z3,z955,z5,z6]),(0,[z1,z2,z3,z28,z6,z43])],[(0,[z19,z2,z3,z4,z381,z6]),(0,[z1,z2,z3,z4,z956,z6]),(0,[z957,z2,z3,z4,z5,z6]),(0,[z362,z137,z3,z4,z5,z6]),(0,[z1,z2,z225,z5,z6,z324])],[(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z3,z4,z5,z6,z777])]],
   [[(0,[z1,z2,z3,z5,z6,z959]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z19,z2,z3,z4,z207,z6]),(0,[z336,z1,z3,z54,z5,z6])],[(0,[z358,z2,z3,z4,z311,z6]),(0,[z73,z721,z3,z4,z5,z6]),(0,[z1,z961,z3,z4,z5,z6]),(0,[z358,z2,z3,z4,z46,z6]),(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z2,z963,z4,z5,z6]),(0,[z336,z1,z3,z720,z5,z6]),(0,[z362,z3,z4,z20,z5,z6])],[(0,[z1,z47,z151,z3,z4,z6]),(0,[z1,z2,z3,z4,z964,z6]),(0,[z1,z2,z3,z965,z5,z6]),(0,[z1,z2,z3,z4,z966,z6]),(1,[z1,z3,z4,z5,z777]),(0,[z1,z2,z3,z4,z829,z6])],[(0,[z1,z2,z3,z5,z6,z967]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z212,z1,z3,z720,z5,z6]),(0,[z970,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z971,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z973,z3,z4,z5,z6]),(0,[z1,z2,z974,z4,z5,z6]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z767,z5,z6]),(0,[z1,z2,z32,z767,z5,z6])],[(0,[z334,z1,z2,z3,z4,z6]),(0,[z1,z2,z4,z83,z829,z6]),(0,[z1,z2,z3,z5,z715,z25]),(0,[z1,z2,z3,z109,z5,z715])],[(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z978,z3,z4,z5,z6]),(0,[z1,z2,z3,z979,z5,z6]),(0,[z1,z2,z980,z4,z5,z6]),(0,[z1,z2,z981,z4,z5,z6]),(0,[z78,z1,z2,z28,z5,z6]),(0,[z982,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z983,z6]),(0,[z45,z2,z3,z4,z6,z639]),(0,[z1,z2,z984,z4,z5,z6]),(0,[z1,z2,z3,z4,z985,z6]),(0,[z1,z2,z4,z5,z6,z986]),(0,[z498,z3,z4,z5,z6,z217]),(0,[z22,z1,z2,z3,z23,z6])]],
   [[(0,[z1,z401,z3,z4,z5,z6]),(0,[z1,z2,z987,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z2,z3,z544,z5,z6]),(0,[z1,z2,z989,z4,z5,z6]),(0,[z168,z2,z3,z231,z5,z6]),(0,[z338,z3,z4,z46,z5,z6]),(0,[z1,z401,z3,z4,z134,z6]),(0,[z1,z2,z3,z544,z134,z6]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z991,z2,z3,z4,z5,z6]),(0,[z992,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z109,z5,z24]),(0,[z1,z2,z3,z4,z728,z82])],[(0,[z1,z993,z3,z4,z5,z6]),(0,[z1,z126,z3,z544,z5,z6]),(0,[z1,z2,z3,z4,z994,z6]),(0,[z1,z2,z995,z4,z5,z6]),(0,[z108,z1,z3,z4,z20,z6]),(0,[z442,z2,z3,z4,z333,z6]),(0,[z1,z2,z3,z31,z246,z6]),(0,[z1,z2,z10,z4,z260,z11])],[(0,[z2,z710,z39,z4,z5,z6]),(0,[z123,z2,z39,z4,z5,z6]),(0,[z1,z2,z3,z996,z5,z6]),(0,[z1,z100,z101,z4,z5,z6]),(0,[z1,z2,z418,z4,z333,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z1,z998,z3,z4,z5,z6]),(0,[z1,z2,z4,z260,z11,z324])],[(0,[z1,z2,z4,z999,z5,z6]),(0,[z1,z1000,z3,z4,z5,z6]),(0,[z1,z2,z3,z477,z433,z6]),(0,[z1,z3,z4,z725,z5,z6]),(0,[z30,z1,z3,z31,z5,z217]),(0,[z64,z96,z1,z2,z3,z6]),(0,[z1,z2,z3,z4,z6,z1001]),(0,[z1,z2,z35,z4,z5,z37])]],
   [[],[(0,[z1,z2,z3,z1002,z5,z6]),(0,[z1,z2,z1003,z4,z5,z6]),(0,[z2,z3,z231,z756,z5,z6]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z1,z2,z3,z4,z6,z1006]),(0,[z1,z2,z32,z8,z5,z6])],[(0,[z1,z2,z1007,z4,z5,z6]),(0,[z1,z2,z3,z1008,z5,z6]),(0,[z1,z2,z3,z5,z6,z1009]),(0,[z1,z2,z35,z4,z5,z755])],[(0,[z403,z2,z3,z4,z46,z6]),(0,[z1,z2,z3,z4,z1010,z6]),(0,[z73,z157,z3,z4,z189,z6]),(0,[z1,z3,z720,z222,z5,z6]),(0,[z1,z2,z219,z31,z5,z6]),(0,[z64,z96,z1,z2,z4,z6]),(0,[z1,z2,z4,z5,z37,z755])]],
   [[(0,[z45,z2,z3,z4,z46,z6]),(0,[z1,z2,z3,z1011,z5,z6]),(0,[z1,z2,z3,z103,z662,z6]),(0,[z1,z1012,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z1013]),(0,[z1,z137,z3,z4,z270,z6]),(0,[z88,z1,z2,z102,z3,z6])],[(0,[z1,z2,z3,z4,z1014,z6]),(0,[z1,z2,z3,z4,z1015,z6]),(0,[z1,z1016,z3,z4,z5,z6]),(0,[z2,z3,z4,z763,z5,z6]),(0,[z1,z406,z101,z4,z5,z6]),(0,[z108,z358,z3,z4,z20,z6]),(0,[z1,z1017,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z1018,z6]),(0,[z212,z1,z3,z222,z5,z6])]],
   [[(0,[z1,z2,z3,z1019,z5,z6]),(0,[z61,z2,z3,z477,z5,z104]),(0,[z1,z2,z4,z5,z6,z1020]),(0,[z1,z2,z1021,z4,z5,z6])],[(0,[z1,z1022,z3,z4,z5,z6]),(0,[z1,z2,z255,z4,z5,z6]),(0,[z1023,z1,z2,z3,z5,z6]),(0,[z120,z2,z3,z756,z5,z6]),(0,[z1,z2,z255,z4,z134,z6]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1,z2,z3,z4,z6,z1025]),(0,[z15,z1,z2,z4,z5,z755]),(0,[z1,z2,z3,z260,z11,z373])],[(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z126,z255,z4,z5,z6]),(0,[z1,z2,z1027,z3,z4,z6]),(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z4,z1029,z6])],[(0,[z459,z157,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1030,z6]),(0,[z2,z3,z4,z756,z5,z6]),(0,[z1,z2,z1031,z4,z5,z6]),(0,[z1,z2,z3,z4,z1032,z6]),(0,[z1033,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1034,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z1036,z2,z3,z4,z5,z6]),(0,[z1,z2,z418,z194,z5,z6]),(0,[z30,z1,z219,z4,z5,z217]),(0,[z1,z1037,z3,z4,z5,z6]),(0,[z1,z2,z5,z6,z324,z373])]],
   [[(0,[z1,z2,z1038,z3,z4,z6]),(0,[z1,z2,z1039,z4,z5,z6]),(0,[z64,z34,z22,z1,z2,z6]),(0,[z1,z2,z3,z1040,z5,z6]),(1,[z1,z2,z3,z801,z6]),(0,[z2,z3,z4,z5,z6,z1041])],[(0,[z2,z151,z3,z4,z189,z6]),(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z1043,z3,z4,z5,z6]),(0,[z1,z2,z1044,z3,z4,z6]),(0,[z45,z52,z3,z4,z46,z6]),(0,[z1,z2,z3,z109,z5,z367]),(0,[z2,z3,z4,z5,z6,z1045]),(0,[z1,z1046,z3,z4,z5,z6])],[(0,[z1047,z1,z2,z3,z5,z6]),(0,[z1,z2,z35,z4,z5,z701]),(0,[z1,z2,z1048,z4,z5,z6]),(0,[z1,z401,z3,z544,z5,z6]),(0,[z1,z2,z3,z4,z6,z1049]),(0,[z30,z1,z3,z4,z333,z217]),(0,[z64,z1,z2,z767,z5,z6]),(0,[z1,z2,z767,z97,z5,z6]),(0,[z96,z1,z2,z4,z6,z16])],[(0,[z1,z1050,z3,z4,z5,z6]),(0,[z117,z1,z63,z4,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z108,z1,z3,z4,z725,z6])]],
   [[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z19,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z4,z725,z6]),(0,[z1,z3,z4,z5,z777,z217]),(0,[z96,z1,z2,z33,z4,z6]),(0,[z1,z2,z3,z4,z11,z728])],[(0,[z1,z2,z3,z1053,z5,z6]),(0,[z1,z3,z4,z725,z270,z6]),(0,[z1,z2,z4,z829,z77,z6]),(0,[z1,z2,z10,z5,z6,z373])],[(0,[z403,z1,z3,z4,z20,z6]),(0,[z1,z2,z3,z4,z1054,z6]),(0,[z1,z2,z3,z31,z5,z6]),(0,[z1,z2,z219,z4,z333,z6]),(0,[z34,z88,z1,z2,z4,z6]),(0,[z1,z2,z1055,z4,z5,z6])],[(0,[z462,z2,z3,z4,z5,z104]),(0,[z1,z338,z3,z4,z5,z6]),(0,[z73,z157,z3,z4,z294,z6]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z157,z1,z47,z3,z4,z6]),(0,[z1,z1057,z3,z4,z5,z6]),(0,[z498,z2,z3,z31,z5,z6]),(0,[z34,z88,z1,z2,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 557) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 557).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1026)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [557, 469] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 89).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 89).take 39).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [89, 39] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_43138

theorem PEqualNP.Outside.L_meta_43138 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808360 * 2 ^ 32 + 3941263872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808360 * 2 ^ 32 + 3941263872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_43138.solve