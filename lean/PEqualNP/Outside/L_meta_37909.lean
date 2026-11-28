import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37909

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
  Nat.testBit (4277074666 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x110002002042812a#64 ++ 0x0220004004085025#64 ++ 0xfec14631e0c787ff#64 ++ 0xbfd828c63c18f0ff#64 : BitVec 256),
   (0x0e02192683196494#64 ++ 0x21c04324d0632c92#64 ++ 0xbda6b92e8739e49f#64 ++ 0x77b4d725d0e73c93#64 : BitVec 256),
   (0xa408c04b082c28c0#64 ++ 0x9481180961058518#64 ++ 0xebd8c1cf183e78e6#64 ++ 0xfd7b1839e307cf1c#64 : BitVec 256),
   (0x081701b015805600#64 ++ 0x2102e03602b00ac0#64 ++ 0x67ff01f01fc07f05#64 ++ 0xecffe03e03f80fe0#64 : BitVec 256),
   (0x303dee001ef78000#64 ++ 0xc607bdc003def000#64 ++ 0x1fbffe001fff8003#64 ++ 0xe3f7ffc003fff000#64 : BitVec 256),
   (0xc01ff5fdc0000000#64 ++ 0xf803febfb8000000#64 ++ 0xff9fffffe0000000#64 ++ 0x1ff3fffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1 : W := mkw 0x0a02192483114414 0x2140432490622882 0x35a639208701e41d 0x66b4c72410e03c83

def z2 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6b92e8739e49f 0x77b4d725d0e73c93

def z3 : W := mkw 0x110002002042812a 0x0220004004085025 0xfec14631e0c787ff 0xbfd828c63c18f0ff

def z4 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z5 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1cf183e78e6 0xfd7b1839e307cf1c

def z6 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z7 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8840c00f183e78e6 0xf1081801e307cf1c

def z8 : W := mkw 0x0c1701b215887680 0x2182e03642b10ed0 0xefff81fe1ff87f87 0xfdfff03fc3ff0ff0

def z9 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0xe04001fe80007f9c 0x1c08003fd0000ff3

def z10 : W := mkw 0x0015009014801200 0x0002a01202900240 0x001800c018001800 0x0003001803000300

def z11 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe001849f 0x3ff3fffffc003093

def z12 : W := mkw 0x110002002042812a 0x0220004004085025 0x4241461160c60360 0x884828c22c18c06c

def z13 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffe31ffff87ff 0xffffffc63ffff0ff

def z14 : W := mkw 0x313de6003ce6812a 0xc627bcc0079cd025 0x4259461178c60360 0x884b28c22f18c06c

def z15 : W := mkw 0x0400000200082080 0x0080000040010410 0x0100810e00386000 0x40201021c0070c00

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x14010630e0000000 0x028020c61c000000

def z17 : W := mkw 0x8e0ad96f83196494 0xb1c15b2df0632c92 0xffbef9ef8739e49f 0x7ff7df3df0e73c93

def z18 : W := mkw 0xd11ff7fde042812a 0xfa23feffbc085025 0xff9fffffe00780fa 0x1ff3fffffc00f01f

def z19 : W := mkw 0xa008c04908240840 0x9401180921048108 0x425840c118061860 0x884b08182300c30c

def z20 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x011881ce18387800 0x40231039c3070f00

def z21 : W := mkw 0x393fefb03ff7d72a 0xe727fdf607fefae5 0xfffffff1ffffffff 0xfffffffe3fffffff

def z22 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa000012e8000649c 0x14000025d0000c93

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0xeec1403100c607e7 0xbdd828062018c0fc

def z24 : W := mkw 0x10000a0002538000 0x02000140004a7000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z25 : W := mkw 0x1f021b26a35be5be 0x23e04364d46b7cb7 0xffe7ff3fe7ffe7ff 0xfffcffe7fcfffcff

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814631e0000000 0x1fd028c63c000000

def z27 : W := mkw 0xd11ff7fde042812a 0xfa23feffbc085025 0xffdfffffe0c787ff 0xbffbfffffc18f0ff

def z28 : W := mkw 0x110002002042812a 0x0220004004085025 0x98004601e00780fa 0x130008c03c00f01f

def z29 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x66c1003000c00705 0xacd82006001800e0

def z31 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000031e0000000 0x1c0000063c000000

def z32 : W := mkw 0x400211b4c0000000 0x2800423698000000 0x00000030e0000000 0x000000061c000000

def z33 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x1f9ffe0000000000 0x03f3ffc000000000

def z34 : W := mkw 0x11000a002253812a 0x02200140044a7025 0xffe7fe31e7ff87ff 0xfffcffc63cfff0ff

def z35 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x013eb8001f380000 0x4027d70003e70000

def z36 : W := mkw 0x8008c04900000000 0x9001180920000000 0x011881ce00000000 0x00231039c0000000

def z37 : W := mkw 0x2e0219268b3d6cd4 0x25c04324d167ad9a 0xbde6b92e9f3ffcff 0xf7bcd725d3e7ff9f

def z38 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffbfffffe7006405 0x7ff7fffffce00c80

def z39 : W := mkw 0x0015000014800000 0x0002a00002900000 0x07bf00001fc00001 0xe0f7e00003f80000

def z40 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x604001f000007f04 0x0c08003e00000fe0

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x0398000018000000 0xe073000003000000

def z42 : W := mkw 0x110002002042812a 0x0220004004085025 0x5ec1461160c78363 0xabd828c22c18f06c

def z43 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x0126b90e0739e49f 0x6024d721c0e73c93

def z44 : W := mkw 0xc81711fdd5805600 0x3902e23fbab00ac0 0xe7ff01ffffc07f05 0xfcffe03ffff80fe0

def z45 : W := mkw 0x1900020035c2d72a 0x0320004006b85ae5 0x006000001fc7ffff 0xe00c000003f8ffff

def z46 : W := mkw 0x110002002042812a 0x0220004004085025 0xfe814631e00780fa 0x1fd028c63c00f01f

def z47 : W := mkw 0x0400000200082080 0x0080000040010410 0xa980810e00386086 0x75301021c0070c10

def z48 : W := mkw 0xae0ad96f8b3d6cd4 0xb5c15b2df167ad9a 0xfffef9ef9f3ffcff 0xffffdf3df3e7ff9f

def z49 : W := mkw 0xb428ee4b0a7fa8c0 0xd6851dc9614ff518 0x9800fe0f003f80e2 0x13001fc1e007f01c

def z50 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x002000001fff8003 0xe004000003fff000

def z51 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0x001800c000000000 0x0003001800000000

def z52 : W := mkw 0x110002002042812a 0x0220004004085025 0x0040000000c787ff 0xa00800000018f0ff

def z53 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x011eb9ce00000000 0x0023d739c0000000

def z54 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x14273e0007c18001 0x0284e7c000f83000

def z55 : W := mkw 0x8400004b000828c0 0x1080000960010518 0xe04001cf000078e4 0x1c080039e0000f1c

def z56 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffffc07f05 0xfffffffffff80fe0

def z57 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x0126b90e07386000 0x4024d721c0e70c00

def z58 : W := mkw 0xf03deed95ef78000 0xde07bddb2bdef000 0x5fbffed17fff8003 0xebf7ffda2ffff000

def z59 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x1da6b8001fff8003 0xe3b4d70003fff000

def z60 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0x421946d160000000 0x084328da2c000000

def z61 : W := mkw 0x8008c04900000000 0x9001180920000000 0xeb98c1cf00000000 0x1d731839e0000000

def z62 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0xffbfffcf1fff8003 0xfff7fff9e3fff000

def z63 : W := mkw 0xac1fc1fb1dac7ec0 0xb583f83f63b58fd8 0xefffc1ff1ffe7fe7 0xfdfff83fe3ffcffc

def z64 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0xffff47f1ffc7ffff 0xffffe8fe3ff8ffff

def z65 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c80000000018003 0x2390000000003000

def z66 : W := mkw 0x0000080002110000 0x0000010000422000 0x1da6b80007398003 0x63b4d70000e73000

def z67 : W := mkw 0x24000002082c28c0 0x0480000041058518 0x00400000183e78e6 0xe00800000307cf1c

def z68 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe011fff80e7 0xffffffc023fff01c

def z69 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x63f801c01fc07f05 0xec7f003803f80fe0

def z70 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x14073e30e0000000 0x0280e7c61c000000

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc8000208001849f 0x3790000410003093

def z72 : W := mkw 0x110002002042812a 0x0220004004085025 0x14010630e0c18719 0x028020c61c1830e3

def z73 : W := mkw 0xf03ffffdca778000 0xfe07ffffb94ef000 0xff9fffffe03f8002 0x1ff3fffffc07f000

def z74 : W := mkw 0x2408c002082c2080 0x8481180041058410 0xab98c10e183e6086 0xf5731821c307cc10

def z75 : W := mkw 0x001701b000000000 0x2002e03600000000 0x679f01f000000000 0x0cf3e03e00000000

def z76 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1da7be0007f98003 0x63b4f7c000ff3000

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z78 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe00600e6 0xbffbfffffc00c01c

def z79 : W := mkw 0x04000002000828c0 0x0080000040010518 0x00400000000078e4 0x0008000000000f1c

def z80 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6b92e87386000 0x57b4d725d0e70c00

def z81 : W := mkw 0x9108c2492042812a 0x9221184924085025 0xffd9c7ffe0c787ff 0xbffb38fffc18f0ff

def z82 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1c27fe0007ff8003 0x0384ffc000fff000

def z83 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0x0020000007386000 0x4004000000e70c00

def z84 : W := mkw 0x303de6001ce68000 0xc607bcc0039cd000 0x0219460018c60000 0x804328c00318c000

def z85 : W := mkw 0x0a02192483114414 0x2140432490622882 0x1426382087018419 0x0284c70410e03083

def z86 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff41f11fc67fe7 0xfdffe83e23f8cffc

def z87 : W := mkw 0xce1ffdffc3196494 0xf9c3ffbff8632c92 0xbdbeb9ee8739e49f 0x77b7d73dd0e73c93

def z88 : W := mkw 0x0015240000000000 0x4002a48000000000 0x14073e0000000000 0x0280e7c000000000

def z89 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0x1fbffe0007398003 0x63f7ffc000e73000

def z90 : W := mkw 0xce1ffdffc3196494 0xf9c3ffbff8632c92 0xffbfffffe739e49f 0x7ff7fffffce73c93

def z91 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x0bbef8001f3e0002 0xe177df0003e7c000

def z92 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0xffffffcf1ffff8e7 0xfffffff9e3ffff1c

def z93 : W := mkw 0xf03ffffddef78000 0xfe07ffffbbdef000 0xffbfffffffff8003 0xfff7fffffffff000

def z94 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xffdffffff8c01b00 0x9ffbffffff180360

def z95 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86b92e80000000 0x17b0d725d0000000

def z96 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x193efe001f3f8002 0x4327dfc003e7f000

def z97 : W := mkw 0x40003404c0000000 0x4800068098000000 0x10003e00e0000000 0x020007c01c000000

def z98 : W := mkw 0x2008c00008240000 0x8401180001048000 0x0b98c000183e0002 0xe17318000307c000

def z99 : W := mkw 0x0a1719b497915614 0x2142e33692f22ac2 0x1427383087c18719 0x0284e70610f830e3

def z100 : W := mkw 0xe41ff5ffc82c28c0 0xfc83febff9058518 0xffdffffff83e78e6 0xfffbffffff07cf1c

def z101 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1800fe00003f8002 0x03001fc00007f000

def z102 : W := mkw 0x8008c04900000000 0x9001180920000000 0xebd8c1cf18007804 0xfd7b1839e3000f00

def z103 : W := mkw 0x0000080002110000 0x0000010000422000 0x1800b80000398002 0x0300170000073000

def z104 : W := mkw 0x110002002042812a 0x0220004004085025 0x56414631e0c78779 0x8ac828c63c18f0ef

def z105 : W := mkw 0x24000002082c28c0 0x0480000041058518 0x63d801c0183e78e6 0xec7b00380307cf1c

def z106 : W := mkw 0x11352e0036d3812a 0x4226a5c006da7025 0x14273e30e7c18719 0x0284e7c61cf830e3

def z107 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbffe001f380000 0x43f7ffc003e70000

def z108 : W := mkw 0x0402112680082080 0x20804224d0010410 0xbd86b92e80386086 0x77b0d725d0070c10

def z109 : W := mkw 0x0600180682192094 0x00c00300d0432412 0x9800b80e8039809a 0x13001701d0073013

def z110 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff00301fc00705 0xecffe00603f800e0

def z111 : W := mkw 0x0e1719b697997694 0x21c2e336d2f32ed2 0xffffb9fe9ff9ff9f 0xfffff73fd3ff3ff3

def z112 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0x14270630e7c18719 0x0284e0c61cf830e3

def z113 : W := mkw 0x1000020000428000 0x0200004000085000 0x1e81460000c78003 0xa3d028c00018f000

def z114 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x006000001fc07f05 0xe00c000003f80fe0

def z115 : W := mkw 0x0802012001004400 0x2100402400200880 0x25a6012007006405 0x64b4c02400e00c80

def z116 : W := mkw 0x010000002000012a 0x0020000004000025 0xfcc00031e00187ff 0x3f9800063c0030ff

def z117 : W := mkw 0xa408c84b0a3d28c0 0x948119096147a518 0xfffef9cf1f3ff8e7 0xffffdf39e3e7ff1c

def z118 : W := mkw 0x1f021b26a35be5be 0x23e04364d46b7cb7 0xbda7bf3ee7f9e79f 0x77b4f7e7dcff3cf3

def z119 : W := mkw 0x3e3fff269fffe494 0xe7c7ffe4d3fffc92 0xbfbfff2e9fffe49f 0xf7f7ffe5d3fffc93

def z120 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0x002000000739e49f 0x6004000000e73c93

def z121 : W := mkw 0x010000002000012a 0x0020000004000025 0xe0400031e00007fc 0x1c0800063c0000ff

def z122 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0xffd9c7fff8ffffff 0xfffb38ffff1fffff

def z123 : W := mkw 0xac08c04b1dac7ec0 0x9581180963b58fd8 0xebf8c1cf1ffe7fe7 0xfd7f1839e3ffcffc

def z124 : W := mkw 0xc00211fdc0000000 0x3800423fb8000000 0xe00001ffe0000000 0x1c00003ffc000000

def z125 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x14273e001fff8003 0xe284e7c003fff000

def z126 : W := mkw 0x383fefb01ff7d600 0xe707fdf603fefac0 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z127 : W := mkw 0xce1ffdffd7997694 0xf9c3ffbffaf32ed2 0xfffffffffff9ff9f 0xffffffffffff3ff3

def z128 : W := mkw 0xc80211fdc1005600 0x3900423fb8200ac0 0xe04001ffe0007f04 0x1c08003ffc000fe0

def z129 : W := mkw 0x001de40014800000 0xc003bc8002900000 0x1fbffe001fc00001 0xe3f7ffc003f80000

def z130 : W := mkw 0x0e02192697997694 0x21c04324d2f32ed2 0xbde6b92e9ff9ff9f 0xf7bcd725d3ff3ff3

def z131 : W := mkw 0x0015009014801200 0x0002a01202900240 0x425900d018c01b00 0x884b201a03180360

def z132 : W := mkw 0x303de6901ce69200 0xc607bcd2039cd240 0x425946d018c61b00 0x884b28da0318c360

def z133 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x013e01c01f007800 0x4027c03803e00f00

def z134 : W := mkw 0x303dee000a778000 0xc607bdc0014ef000 0x1f9ffe00003f8002 0x03f3ffc00007f000

def z135 : W := mkw 0x081701b001005600 0x2102e03600200ac0 0x67df01f000007f04 0x0cfbe03e00000fe0

def z136 : W := mkw 0x110002002042812a 0x0220004004085025 0xda414611e0c783fa 0x9b4828c23c18f07f

def z137 : W := mkw 0x4a173db4c3114414 0x6942e7b698622882 0x14273e30e7018419 0x0284e7c61ce03083

def z138 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x646701f007c07f05 0x0c8ce03e00f80fe0

def z139 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z140 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8918c1cf183e78e2 0x51231839e307cf1c

def z141 : W := mkw 0x110002002042812a 0x0220004004085025 0x9e814601e0c780fb 0xb3d028c03c18f01f

def z142 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x5ffffe117fff8363 0xebffffc22ffff06c

def z143 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x0b98c1ce183e7802 0xe1731839c307cf00

def z144 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x4358c1cf183e7860 0xc86b1839e307cf0c

def z145 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xbd9eb9ee80000000 0x17b3d73dd0000000

def z146 : W := mkw 0x010000002000012a 0x0020000004000025 0x4040001160000360 0x080800022c00006c

def z147 : W := mkw 0x081709b017915600 0x2102e13602f22ac0 0x7fffb9f01ff9ff07 0xeffff73e03ff3fe0

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x63d801c018007804 0xec7b003803000f00

def z149 : W := mkw 0x110002002042812a 0x0220004004085025 0x9c014631e0c787fb 0x138028c63c18f0ff

def z150 : W := mkw 0xd01ff7fdc0428000 0xfa03feffb8085000 0xff9fffffe0c78003 0xbff3fffffc18f000

def z151 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x0427003007c00701 0x0084e00600f800e0

def z152 : W := mkw 0xc81fe5f955805600 0xf903fcbf2ab00ac0 0x67ff47f17fc07f05 0xecffe8fe2ff80fe0

def z153 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1da6b90e0739e003 0x63b4d721c0e73c00

def z154 : W := mkw 0x1e373f2697dbe494 0x63c6e7e4d2fb7c92 0xbda7bf2e87f9e49f 0x77b4f7e5d0ff3c93

def z155 : W := mkw 0x24000002082c28c0 0x0480000041058518 0x00000000003e00e2 0x000000000007c01c

def z156 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xa980c10f003e60e6 0x75301821e007cc1c

def z157 : W := mkw 0x313de6003ce6812a 0xc627bcc0079cd025 0xfed94631f8c787ff 0xbfdb28c63f18f0ff

def z158 : W := mkw 0xd108f64de042812a 0xda211ec9bc085025 0xfec1fe3fe0c787ff 0xbfd83fc7fc18f0ff

def z159 : W := mkw 0x303dee901ef79200 0xc607bdd203def240 0x5ffffed01fff9b03 0xebffffda03fff360

def z160 : W := mkw 0x8400004b000828c0 0x1080000960010518 0x000001ce00007800 0x00000039c0000f00

def z161 : W := mkw 0x0802012001004400 0x2100402400200880 0x67e7013007c06705 0xecfce02600f80ce0

def z162 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0xe04001ef80007cfc 0x1c08003df0000f9f

def z163 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xefd9c1ff18fe7fe7 0xfdfb383fe31fcffc

def z164 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8800c00f003e00e2 0x11001801e007c01c

def z165 : W := mkw 0x3028ee001ef78000 0xc6051dc003def000 0x1820fe001fff8003 0xe3041fc003fff000

def z166 : W := mkw 0x0000080002110000 0x0000010000422000 0x0126b80007380000 0x4024d70000e70000

def z167 : W := mkw 0x090201b02100572a 0x2120403604200ae5 0xe04001f1e0007ffc 0x1c08003e3c000fff

def z168 : W := mkw 0x2008c00008240000 0x8401180001048000 0x6bd8c1c0183e7806 0xed7b18380307cf00

def z169 : W := mkw 0x8c0201fb01087ec0 0x3180403f60210fd8 0xe04001ff00007fe4 0x1c08003fe0000ffc

def z170 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0x5ffffec11fff9863 0xebffffd823fff30c

def z171 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x033ffe001ffe0000 0xc067ffc003ffc000

def z172 : W := mkw 0x0200180482110014 0x0040030090422002 0x1000380080018018 0x0200070010003003

def z173 : W := mkw 0x8008c04900000000 0x9001180920000000 0x421840c100000000 0x0843081820000000

def z174 : W := mkw 0xe03ffdfddeb50000 0xfc07ffbfbbd6a000 0xffbfffffff380000 0x5ff7ffffffe70000

def z175 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd8c1ef983ffcff 0xfffb183df307ff9f

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x1400002080018419 0x0280000410003083

def z177 : W := mkw 0x0e1711b695887694 0x21c2e236d2b10ed2 0xe7ff01fe9fc07f9d 0xfcffe03fd3f80ff3

def z178 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7ffffe301fff8707 0xefffffc603fff0e0

def z179 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xff9ffffff83e0002 0xfff3ffffff07c000

def z180 : W := mkw 0x8c1701fb15887ec0 0x3182e03f62b10fd8 0xe7ff01ff1fc07fe5 0xfcffe03fe3f80ffc

def z181 : W := mkw 0x0400000200082080 0x0080000040010410 0xebc0c10f003e60e6 0xfd781821e007cc1c

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x4201461160000000 0x084028c22c000000

def z183 : W := mkw 0x0f021926a31965be 0x21e04324d4632cb7 0xfde6b93fe739e7ff 0x7fbcd727fce73cff

def z184 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x14273e30e7c00701 0x0284e7c61cf800e0

def z185 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x66e100301fc07f05 0xecdc200603f80fe0

def z186 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x9fbffe01ffff80fb 0xf3f7ffc03ffff01f

def z187 : W := mkw 0x0600180682192094 0x00c00300d0432412 0x9da6b80e8739809b 0x73b4d701d0e73013

def z188 : W := mkw 0x8400004b000828c0 0x1080000960010518 0xe3d801cf180078e4 0xfc7b0039e3000f1c

def z189 : W := mkw 0x31200a003ef7812a 0x0624014007def025 0x006000001fff87ff 0xe00c000003fff0ff

def z190 : W := mkw 0x9500024b204aa9ea 0x12a000496409553d 0xfec147ffe0c7ffff 0xbfd828fffc18ffff

def z191 : W := mkw 0xae1fd9ff9fbd7ed4 0xb5c3fb3ff3f7afda 0xfffff9ff9fffffff 0xffffff3ff3ffffff

def z192 : W := mkw 0xc008e44940000000 0xd8011c8928000000 0x0000460160000000 0x000008c02c000000

def z193 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0xfe9946f1e0000000 0x1fd328de3c000000

def z194 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x427900d01fc07f05 0xe84f201a03f80fe0

def z195 : W := mkw 0x110002002042812a 0x0220004004085025 0xffd947f1f8c7ffff 0xfffb28fe3f18ffff

def z196 : W := mkw 0x3f3fff26bfffe5be 0xe7e7ffe4d7fffcb7 0xffffff3fffffe7ff 0xffffffe7fffffcff

def z197 : W := mkw 0x38370bb01ff7d600 0x2706e17603fefac0 0x67ff01f01fffff07 0xecffe03e03ffffe0

def z198 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xeb98c1cf18387800 0x5d731839e3070f00

def z199 : W := mkw 0xe41ff5ffc82c28c0 0xfc83febff9058518 0xff9fffffe03e00e2 0x1ff3fffffc07c01c

def z200 : W := mkw 0x11352e0036d3812a 0x4226a5c006da7025 0xfee77e31e7c787ff 0xbfdcefc63cf8f0ff

def z201 : W := mkw 0x401ff5b4c0000000 0xe803feb698000000 0x1f9ffe30e0000000 0x03f3ffc61c000000

def z202 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0xfee74631e7c787ff 0xbfdce8c63cf8f0ff

def z203 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xbd87bf3ee0000000 0x17b0f7e7dc000000

def z204 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9c26b82e8739849b 0x1384d705d0e73093

def z205 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x0000010e00006000 0x00000021c0000c00

def z206 : W := mkw 0xce1ff5ffc1086494 0xf9c3febff8210c92 0xff9fffffe000649c 0x1ff3fffffc000c93

def z207 : W := mkw 0x881fc1f915805600 0xb103f83f22b00ac0 0xefffc1ff1fc07f05 0xfdfff83fe3f80fe0

def z208 : W := mkw 0x703fffb4def78000 0xee07fff69bdef000 0x1fbffe30ffff8003 0xe3f7ffc61ffff000

def z209 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1b98fe00183f8002 0xe3731fc00307f000

def z210 : W := mkw 0x081701b001004400 0x2102e03600200880 0x67bf01f007006405 0x6cf7e03e00e00c80

def z211 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x011eb80000000000 0x0023d70000000000

def z212 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67bf01f01f007800 0x4cf7e03e03e00f00

def z213 : W := mkw 0xe41ff5ffc82c28c0 0xfc83febff9058518 0xebdef9cf183e78e6 0xfd7bdf39e307cf1c

def z214 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01c01fc07805 0xecffe03803f80f00

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x6681003000000000 0x0cd0200600000000

def z216 : W := mkw 0x0e1709b217997694 0x21c2e13642f32ed2 0x67ff01f01ff9ff9f 0xecffe03e03ff3ff3

def z217 : W := mkw 0xd11de6d96042812a 0xda23bcdb2c085025 0xfed946f1e0c787ff 0xbfdb28de3c18f0ff

def z218 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1ffffe001fff87ff 0xe3ffffc003fff0ff

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x0980800000380002 0x6130100000070000

def z220 : W := mkw 0xd108f64de042812a 0xda211ec9bc085025 0x9800fe0fe00780fa 0x13001fc1fc00f01f

def z221 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdffffff8007804 0xfffbffffff000f00

def z222 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xa99881ce18387886 0x75331039c3070f10

def z223 : W := mkw 0x0000000000000000 0x0000000000000000 0xeac04001000600e6 0xbd5808002000c01c

def z224 : W := mkw 0x3108c2002866812a 0x86211840050cd025 0xffd9c631f8ff87ff 0xfffb38c63f1ff0ff

def z225 : W := mkw 0x1f021326a14ae5be 0x23e04264d4295cb7 0xfec1473fe0c7e7ff 0xbfd828e7fc18fcff

def z226 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x65e601f007007f05 0x6cbcc03e00e00fe0

def z227 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe7b93e87f9e79f 0xfffcf727d0ff3cf3

def z228 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1dbeb8001f398003 0x63b7d70003e73000

def z229 : W := mkw 0x8e02196f83196cd4 0x31c0432df0632d9a 0xfde6b9ef8739fcff 0x7fbcd73df0e73f9f

def z230 : W := mkw 0x50373fb4d6d38000 0x6a06e7f69ada7000 0x14273e30e7c18001 0x0284e7c61cf83000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x1d86b80000000000 0x03b0d70000000000

def z232 : W := mkw 0xc00211fdc0000000 0x3800423fb8000000 0x000001ce00000000 0x00000039c0000000

def z233 : W := mkw 0x0400080202192080 0x0080010040432410 0xbda6b90e0739e087 0x77b4d721c0e73c10

def z234 : W := mkw 0x0002112480000000 0x2000422490000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z235 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x000001c000007800 0x0000003800000f00

def z236 : W := mkw 0x1000020000428000 0x0200004000085000 0x1800460000078002 0x030008c00000f000

def z237 : W := mkw 0xbf0adb6fab7fedfe 0xb7e15b6df56ffdbf 0xffffffffffffffff 0xffffffffffffffff

def z238 : W := mkw 0x1115020034c2812a 0x0222a04006985025 0xffff4631ffc787ff 0xffffe8c63ff8f0ff

def z239 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0x5f9ffed160000000 0x0bf3ffda2c000000

def z240 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffff007800 0x5ff7ffffffe00f00

def z241 : W := mkw 0x2008c8000a350000 0x840119000146a000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x980000008001809a 0x1300000010003013

def z243 : W := mkw 0x0000000000000000 0x0000000000000000 0x98004601e0000000 0x130008c03c000000

def z244 : W := mkw 0xa508c04b282c29ea 0x94a118096505853d 0xebd8c1fff83e7ffe 0xfd7b183fff07cfff

def z245 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000018007804 0xe008000003000f00

def z246 : W := mkw 0x302002001ce68000 0x06040040039cd000 0x0000000018c60000 0x800000000318c000

def z247 : W := mkw 0xce0211ffc1086494 0x39c0423ff8210c92 0xe00001ffe000649c 0x1c00003ffc000c93

def z248 : W := mkw 0x283fedb01fb55600 0xe507fdb603f6aac0 0x013eb9c01f387800 0x4027d73803e70f00

def z249 : W := mkw 0x010000002000012a 0x0020000004000025 0x00000030e0000718 0x000000061c0000e3

def z250 : W := mkw 0x0e1719b697997694 0x21c2e336d2f32ed2 0xbdbeb9ee9f39fc9f 0x77b7d73dd3e73f93

def z251 : W := mkw 0x0400000200082080 0x0080000040010410 0xa000010e00006084 0x14000021c0000c10

def z252 : W := mkw 0x2028ec000a350000 0xc4051d800146a000 0x0000b80000380000 0x0000170000070000

def z253 : W := mkw 0xbd1fc3fb3deeffea 0xb7a3f87f67bddffd 0xffffc7ffffffffff 0xfffff8ffffffffff

def z254 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe840c1cf003e78e6 0x1d081839e007cf1c

def z255 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x561f7ef1e0000000 0x0ac3efde3c000000

def z256 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff01f09fc1ff9f 0xffffe03e13f83ff3

def z257 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe6f92f873fe4ff 0xfffcdf25f0e7fc9f

def z258 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x467f00f01fc01f01 0x88cfe01e03f803e0

def z259 : W := mkw 0xca1ffdfdc3114414 0xf943ffbfb8622882 0xffbfffffe7018419 0x1ff7fffffce03083

def z260 : W := mkw 0x3128ee002a77812a 0xc6251dc0054ef025 0xfec1fe31e0ff87ff 0xbfd83fc63c1ff0ff

def z261 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7fffffc01ffff807 0xeffffff803ffff00

def z262 : W := mkw 0xae0ad96f8b3d6cd4 0xb5c15b2df167ad9a 0xbda6f92f873fe4ff 0x77b4df25f0e7fc9f

def z263 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x437f01d01fc07b00 0xc86fe03a03f80f60

def z264 : W := mkw 0xb53dee4b3effa9ea 0xd6a7bdc967dff53d 0xffffffffffffffff 0xffffffffffffffff

def z265 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xffbffe31ffff8003 0xfff7ffc63ffff000

def z266 : W := mkw 0x110002002042812a 0x0220004004085025 0xfac04601e00780fe 0xbf5808c03c00f01f

def z267 : W := mkw 0x110002002042812a 0x0220004004085025 0xe2414631e0c607fc 0x9c4828c63c18c0ff

def z268 : W := mkw 0x0002112480000000 0x2000422490000000 0x1406382080000000 0x0280c70410000000

def z269 : W := mkw 0x0015009014801200 0x0002a01202900240 0x47ff00d01fc01b01 0xe8ffe01a03f80360

def z270 : W := mkw 0x110002002042812a 0x0220004004085025 0x10000600e0018018 0x020000c01c003003

def z271 : W := mkw 0xa008c04908240000 0x9401180921048000 0xeb98c1cf183e0002 0xfd731839e307c000

def z272 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0xda19fedfe0000000 0x1b433fdbfc000000

def z273 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xbfbffe209fff849f 0xf7f7ffc413fff093

def z274 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc80002080000000 0x1790000410000000

def z275 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b8208739849f 0x77b4d70410e73093

def z276 : W := mkw 0x0815000015805600 0x0102a00002b00ac0 0x07ff00001fc07f05 0xe0ffe00003f80fe0

def z277 : W := mkw 0x001701b014801200 0x2002e03602900240 0x67df01f018c01b00 0x8cfbe03e03180360

def z278 : W := mkw 0x10202e0002538000 0x420405c0004a7000 0x10003e0000018000 0x020007c000003000

def z279 : W := mkw 0xae08c84b0b3d6cd4 0x95c119096167ad9a 0xebf8c1cf1f3ffcff 0xfd7f1839e3e7ff9f

def z280 : W := mkw 0x303fff249ef78000 0xe607ffe493def000 0xbfbfff2e9fff8003 0xf7f7ffe5d3fff000

def z281 : W := mkw 0x110002002042812a 0x0220004004085025 0xfe814631e0c18719 0x1fd028c63c1830e3

def z282 : W := mkw 0x0802012001004400 0x2100402400200880 0x67fe01e01f007c05 0xecffc03c03e00f80

def z283 : W := mkw 0x11021324a042812a 0x2220426494085025 0xffc7ff3fe0c787ff 0xbff8ffe7fc18f0ff

def z284 : W := mkw 0xc000104dc0000000 0x18000209b8000000 0x8000000fe0000000 0x10000001fc000000

def z285 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63fe01c01f007804 0xec7fc03803e00f00

def z286 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0xebd8c1cf18ffffff 0xfd7b1839e31fffff

def z287 : W := mkw 0x3128ee002a77812a 0xc6251dc0054ef025 0x9800fe01e03f80fa 0x13001fc03c07f01f

def z288 : W := mkw 0x8000004900000000 0x1000000920000000 0xe00001cf00000000 0x1c000039e0000000

def z289 : W := mkw 0xb108c2492866896a 0x96211849250cd12d 0x425946d178c61b60 0x884b28da2f18c36c

def z290 : W := mkw 0x1000020000428000 0x0200004000085000 0x7ec1463000c78707 0xafd828c60018f0e0

def z291 : W := mkw 0x30200a000a778000 0x06040140014ef000 0x00000000003f8002 0x000000000007f000

def z292 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25a7013007c06705 0x64b4e02600f80ce0

def z293 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14631e00600e6 0xbfd828c63c00c01c

def z294 : W := mkw 0x110002002042812a 0x0220004004085025 0xfec14631e0c60360 0x9fd828c63c18c06c

def z295 : W := mkw 0x2008c00008240000 0x8401180001048000 0x0118800018380000 0x4023100003070000

def z296 : W := mkw 0x8500004b200829ea 0x10a000096401053d 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z297 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xb426392e8701e49d 0x1684c725d0e03c93

def z298 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffb9fe9fc07f05 0xfffff73fd3f80fe0

def z299 : W := mkw 0x1000020000428000 0x0200004000085000 0x0000000000c78003 0xa00000000018f000

def z300 : W := mkw 0x0015009014801200 0x0002a01202900240 0x66d900f018c01f05 0xacdb201e031803e0

def z301 : W := mkw 0x0008e40000000000 0xc0011c8000000000 0x1800fe0000000000 0x03001fc000000000

def z302 : W := mkw 0xc61ffdffc2192094 0xf8c3ffbff8432412 0xff9fffffe039809a 0x1ff3fffffc073013

def z303 : W := mkw 0x0015000000000000 0x0002a00000000000 0x079f000000000000 0x00f3e00000000000

def z304 : W := mkw 0x283fedb01fb55600 0xe507fdb603f6aac0 0x67ffb9f01ff87f05 0xecfff73e03ff0fe0

def z305 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0427000007c00001 0x0084e00000f80000

def z306 : W := mkw 0x110002002042812a 0x0220004004085025 0x4241461160c787ff 0xa84828c22c18f0ff

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec04021800784ff 0xbfd808043000f09f

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x011801c018007800 0x4023003803000f00

def z309 : W := mkw 0xc11ff5fde000012a 0xf823febfbc000025 0xffdfffffe00007fc 0x1ffbfffffc0000ff

def z310 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xffdfffffe0007f04 0x1ffbfffffc000fe0

def z311 : W := mkw 0xc01de4d954801200 0xd803bc9b2a900240 0x425946d178c01b00 0x884b28da2f180360

def z312 : W := mkw 0x24000002082c28c0 0x0480000041058518 0xa9c0810e183e78e6 0xf5381021c307cf1c

def z313 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xbc80012e8001e49f 0x37900025d0003c93

def z314 : W := mkw 0x801de44900000000 0xd003bc8920000000 0xff9fffcf00000000 0x1ff3fff9e0000000

def z315 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z316 : W := mkw 0x110002002042812a 0x0220004004085025 0x00000000000780fa 0x000000000000f01f

def z317 : W := mkw 0x0e1719b697997694 0x21c2e336d2f32ed2 0x013eb9ce1f387800 0x4027d739c3e70f00

def z318 : W := mkw 0xb108c2492866896a 0x96211849250cd12d 0xfed946f1f8c79fff 0xbfdb28de3f18f3ff

def z319 : W := mkw 0xce1ffdffc3196494 0xf9c3ffbff8632c92 0xffbfffffe7386000 0x5ff7fffffce70c00

def z320 : W := mkw 0x1f021b26a35be5be 0x23e04364d46b7cb7 0xbde6b92e87ffe7ff 0xf7bcd725d0fffcff

def z321 : W := mkw 0x3e221b269fffe494 0x27c44364d3fffc92 0xbda6b92e9fffe49f 0xf7b4d725d3fffc93

def z322 : W := mkw 0x110002002042812a 0x0220004004085025 0xf8404631e00787fe 0x1f0808c63c00f0ff

def z323 : W := mkw 0x0f021126a10865be 0x21e04224d4210cb7 0xe040013fe00067fc 0x1c080027fc000cff

def z324 : W := mkw 0x110002002042812a 0x0220004004085025 0xbc804621e00784ff 0x379008c43c00f09f

def z325 : W := mkw 0xa008c04908240840 0x9401180921048108 0x4bd8c0c1183e1862 0xe97b18182307c30c

def z326 : W := mkw 0x303de6001ce68000 0xc607bcc0039cd000 0x07bf46001fc60001 0xe0f7e8c003f8c000

def z327 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xffbfffffffc00001 0xfff7fffffff80000

def z328 : W := mkw 0x8008c04900000000 0x9001180920000000 0x8800c00f00000000 0x11001801e0000000

def z329 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x013eb9ce1f007800 0x4027d739c3e00f00

def z330 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa980812e8038649e 0x75301025d0070c93

def z331 : W := mkw 0xb43de64b1ceea8c0 0xd687bcc9639dd518 0xebd9c7cf18fe78e6 0xfd7b38f9e31fcf1c

def z332 : W := mkw 0x0000000000000000 0x0000000000000000 0x4240400100060060 0x884808002000c00c

def z333 : W := mkw 0x0e1719b683196494 0x21c2e336d0632c92 0xffbfb9fe8739e49f 0x7ff7f73fd0e73c93

def z334 : W := mkw 0x8000004900000840 0x1000000920000108 0x404000c100001860 0x080800182000030c

def z335 : W := mkw 0xfe3fffffdfffe494 0xffc7fffffbfffc92 0xffbfffffffffe49f 0xfff7fffffffffc93

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a80400000060002 0xa15008000000c000

def z337 : W := mkw 0x383fef201ff7c400 0xe707fde403fef880 0x3fbfff201fffe407 0xe7f7ffe403fffc80

def z338 : W := mkw 0x3a3fff249ff7c414 0xe747ffe493fef882 0x1fbffe209fff841b 0xe3f7ffc413fff083

def z339 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x1fbfb8001ff98003 0xe3f7f70003ff3000

def z340 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1ea77e0007c78003 0xa3d4efc000f8f000

def z341 : W := mkw 0x0e0219b683197694 0x21c04336d0632ed2 0xfde6b9fe8739ff9f 0x7fbcd73fd0e73ff3

def z342 : W := mkw 0x1e021b26835be494 0x23c04364d06b7c92 0xbfa7ff2e87ffe49f 0xf7f4ffe5d0fffc93

def z343 : W := mkw 0x001701b014800000 0x2002e03602900000 0x67bf01f01fc00001 0xecf7e03e03f80000

def z344 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1e81fe0000ff8003 0xa3d03fc0001ff000

def z345 : W := mkw 0xa40ad16f882c28c0 0xb4815a2df1058518 0xffdef9ef983e78e6 0xfffbdf3df307cf1c

def z346 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff47f1ffc07f05 0xffffe8fe3ff80fe0

def z347 : W := mkw 0x0817012015804400 0x2102e02402b00880 0x27bf01201fc06405 0xe4f7e02403f80c80

def z348 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z349 : W := mkw 0xc40211ffc00828c0 0x3880423ff8010518 0xe04001ffe00078e4 0x1c08003ffc000f1c

def z350 : W := mkw 0x0e00000201086494 0x01c0000040210c92 0x000000000000649c 0x0000000000000c93

def z351 : W := mkw 0xf028fe4dca778000 0xde051fc9b94ef000 0x9800fe0fe03f8002 0x13001fc1fc07f000

def z352 : W := mkw 0xac0ac1fb092c7ec0 0xb581583f61258fd8 0xebd8c1ff183e7fe6 0xfd7b183fe307cffc

def z353 : W := mkw 0x0802012015805600 0x2100402402b00ac0 0x25e601201fc07f05 0xe4bcc02403f80fe0

def z354 : W := mkw 0x0a02192483114414 0x2140432490622882 0xbca638208701849f 0x3794c70410e03093

def z355 : W := mkw 0x110002002042812a 0x0220004004085025 0x14410630e0c787ff 0xa28820c61c18f0ff

def z356 : W := mkw 0xa008c04908240840 0x9401180921048108 0xebd8c1cf18061860 0x9d7b1839e300c30c

def z357 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0xf4073fffe0000000 0x1e80e7fffc000000

def z358 : W := mkw 0x2e0008020b3d6cd4 0x05c001004167ad9a 0x006000001f3ffcff 0xe00c000003e7ff9f

def z359 : W := mkw 0x30350a001ef78000 0x0606a14003def000 0x07bf00001fff8003 0xe0f7e00003fff000

def z360 : W := mkw 0x0000080002110000 0x0000010000422000 0x0020000007398003 0x6004000000e73000

def z361 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1526b92e8739e419 0x42a4d725d0e73c83

def z362 : W := mkw 0xd11ff7fde042812a 0xfa23feffbc085025 0xff9fffffe0c18719 0x1ff3fffffc1830e3

def z363 : W := mkw 0x303de6001ce68000 0xc607bcc0039cd000 0x0b99c60018fe0002 0xe17338c0031fc000

def z364 : W := mkw 0x010000002000012a 0x0020000004000025 0xeac04031e00607fe 0xbd5808063c00c0ff

def z365 : W := mkw 0x3e3fffb69ffff694 0xe7c7fff6d3fffed2 0xfffffffe9fffff9f 0xffffffffd3fffff3

def z366 : W := mkw 0x0e1719b697997694 0x21c2e336d2f32ed2 0x67ffb9fe1ff87f05 0xecfff73fc3ff0fe0

def z367 : W := mkw 0x001de40000000000 0xc003bc8000000000 0x0219460000000000 0x004328c000000000

def z368 : W := mkw 0x2008c00008240000 0x8401180001048000 0xebd8c001183e00e6 0xfd7b18002307c01c

def z369 : W := mkw 0x1f000a02235be5be 0x03e00140446b7cb7 0xfee14631e7ffe7ff 0xffdc28c63cfffcff

def z370 : W := mkw 0x2408c002082c28c0 0x8481180041058518 0x0bd8c000183e78e6 0xe17b18000307cf1c

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x05a6000007000001 0x60b4c00000e00000

def z372 : W := mkw 0xbc3feffb1ffffec0 0xf787fdff63ffffd8 0xffffffff1fffffe7 0xffffffffe3fffffc

def z373 : W := mkw 0xf03dfe4ddef78000 0xde07bfc9bbdef000 0x9fbffe0fffff8003 0xf3f7ffc1fffff000

def z374 : W := mkw 0x0000080002110000 0x0000010000422000 0x1426380007018001 0x0284c70000e03000

def z375 : W := mkw 0x091701b03580572a 0x2122e03606b00ae5 0xe7ff01f1ffc07ffd 0xfcffe03e3ff80fff

def z376 : W := mkw 0x0a02112481004414 0x2140422490200882 0x0000002080000418 0x0000000410000083

def z377 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f000c00705 0xacfbe03e001800e0

def z378 : W := mkw 0xe408f44fc82c28c0 0xdc811e89f9058518 0xfbd8ffcff83e78e6 0xff7b1ff9ff07cf1c

def z379 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0x1fbfffce1ffff803 0xe3f7fff9c3ffff00

def z380 : W := mkw 0x0002012000000000 0x2000402400000000 0x2586012000000000 0x04b0c02400000000

def z381 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x151fbffee0000000 0x02a3f7ffdc000000

def z382 : W := mkw 0x8008c04900000000 0x9001180920000000 0xff99c7ffe0000000 0x1ff338fffc000000

def z383 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x25a6b92e07386405 0x64b4d725c0e70c80

def z384 : W := mkw 0x18372fb017d3d600 0x6306e5f602fa7ac0 0x14273e3007c18701 0x0284e7c600f830e0

def z385 : W := mkw 0xee1ffdffcb3d6cd4 0xfdc3ffbff967ad9a 0xffffffffff3ffcff 0xffffffffffe7ff9f

def z386 : W := mkw 0x110002002042812a 0x0220004004085025 0xe0400031e0c787ff 0xbc0800063c18f0ff

def z387 : W := mkw 0x110002002042812a 0x0220004004085025 0x0000460160060060 0x000008c02c00c00c

def z388 : W := mkw 0x0600080202192094 0x00c0010040432412 0x000000000039809a 0x0000000000073013

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0x62c0000000000004 0xac58000000000000

def z390 : W := mkw 0x190203b02142d72a 0x2320407604285ae5 0xfec147f1e0c7ffff 0xbfd828fe3c18ffff

def z391 : W := mkw 0x383fe7b01de6d600 0xe707fcf603bcdac0 0x67ff47f01fc67f05 0xecffe8fe03f8cfe0

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x1e81460000000000 0x03d028c000000000

def z393 : W := mkw 0x511737b4e042812a 0x6a22e6f69c085025 0x14073e30e0c18719 0x0280e7c61c1830e3

def z394 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8b98c00f183e00e2 0xf1731801e307c01c

def z395 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xffdffffff8061860 0x9ffbffffff00c30c

def z396 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe30ffff871b 0xe3f7ffc61ffff0e3

def z397 : W := mkw 0x201dc0001ca40000 0x8403b80003948000 0x0fbfc0001ffe0003 0xe1f7f80003ffc000

def z398 : W := mkw 0x110002002042812a 0x0220004004085025 0x98404601e0c787ff 0xb30808c03c18f0ff

def z399 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x617e01f01f007f04 0x4c2fc03e03e00fe0

def z400 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00000208000049c 0x1400000410000093

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0xea80400100000000 0x1d50080020000000

def z402 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0c00705 0xbffbfffffc1800e0

def z403 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x67ffb9fe1fc07f05 0xecfff73fc3f80fe0

def z404 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07bf00301fc00701 0xe0f7e00603f800e0

def z405 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0x67ff01f01fc7ffff 0xecffe03e03f8ffff

def z406 : W := mkw 0x8400004b000828c0 0x1080000960010518 0x8000000f000000e0 0x10000001e000001c

def z407 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25be01e01f007c05 0x64b7c03c03e00f80

def z408 : W := mkw 0x24000002082c28c0 0x0480000041058518 0x0000000018387800 0x4000000003070f00

def z409 : W := mkw 0x181703b015c2d600 0x2302e07602b85ac0 0x7fff47f01fc7ff07 0xefffe8fe03f8ffe0

def z410 : W := mkw 0x0e00080217997694 0x01c0010042f32ed2 0x006000001ff9ff9f 0xe00c000003ff3ff3

def z411 : W := mkw 0xd91ff7fdf5c2d72a 0xfb23feffbeb85ae5 0xffffffffffc7ffff 0xfffffffffff8ffff

def z412 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x9c07fe3fe0000000 0x1380ffc7fc000000

def z413 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xfe877e31e0000000 0x1fd0efc63c000000

def z414 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfffeb9ee9f39fc9f 0xffffd73dd3e73f93

def z415 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffe7c00701 0x1ff7fffffcf800e0

def z416 : W := mkw 0x203de4001ca40000 0xc407bc8003948000 0x0018000018000000 0x0003000003000000

def z417 : W := mkw 0x35000202286ea9ea 0x06a00040450dd53d 0xfec14631f8ffffff 0xffd828c63f1fffff

def z418 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe25841cf180678e4 0x9c4b0839e300cf1c

def z419 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x1f9fffce00000000 0x03f3fff9c0000000

def z420 : W := mkw 0x4e173db6c3196494 0x69c2e7b6d8632c92 0xbda7bf3ee739e49f 0x77b4f7e7dce73c93

def z421 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x153fbe001ff98001 0x42a7f7c003ff3000

def z422 : W := mkw 0x010000002000012a 0x0020000004000025 0x80000001e00000f8 0x100000003c00001f

def z423 : W := mkw 0x0002192482110000 0x2000432490422000 0xbda6b92e87398003 0x77b4d725d0e73000

def z424 : W := mkw 0x010000002000012a 0x0020000004000025 0xfec14631e00007fc 0x1fd828c63c0000ff

def z425 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x77ff3ff0ffc07f05 0xeeffe7fe1ff80fe0

def z426 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0x77ff07f0ffc1ff1d 0xeeffe0fe1ff83fe3

def z427 : W := mkw 0xe41ff5ffc82c28c0 0xfc83febff9058518 0xff9ffffff8387800 0x5ff3ffffff070f00

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0xebd841c1180678e6 0xfd7b08382300cf1c

def z429 : W := mkw 0x110002002042812a 0x0220004004085025 0x76c10630e0c1871d 0xaed820c61c1830e3

def z430 : W := mkw 0x2c0000021dac7ec0 0x0580000043b58fd8 0x006000001ffe7fe7 0xe00c000003ffcffc

def z431 : W := mkw 0xf13ffffdfef7812a 0xfe27ffffbfdef025 0xffffffffffff87ff 0xfffffffffffff0ff

def z432 : W := mkw 0xf83ffffddff7d600 0xff07ffffbbfefac0 0xffffffffffffff07 0xffffffffffffffe0

def z433 : W := mkw 0x2e3ffd269fbd6494 0xe5c7ffa4d3f7ac92 0x013eb90e1f386000 0x4027d721c3e70c00

def z434 : W := mkw 0x0602192682192094 0x20c04324d0432412 0xbd86b92e8039809a 0x17b0d725d0073013

def z435 : W := mkw 0x8408c04b00082080 0x9081180960010410 0xeb98c1cf00386086 0x7d731839e0070c10

def z436 : W := mkw 0x0c02012201086480 0x2180402440210c90 0xada6812e07386487 0x75b4d025c0e70c90

def z437 : W := mkw 0x303de6001ce68000 0xc607bcc0039cd000 0x1f9ffe0018c60000 0x83f3ffc00318c000

def z438 : W := mkw 0x0002112480000000 0x2000422490000000 0xa000012e80000000 0x14000025d0000000

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x639801c000000000 0x0c73003800000000

def z440 : W := mkw 0x0802112481004400 0x2100422490200880 0xbda6b92e87006405 0x77b4d725d0e00c80

def z441 : W := mkw 0x0000100480000000 0x0000020090000000 0x9800b80e80000000 0x13001701d0000000

def z442 : W := mkw 0x0802092003114400 0x2100412400622880 0x3da6b9200739e407 0x67b4d72400e73c80

def z443 : W := mkw 0xe408f44fc82c28c0 0xdc811e89f9058518 0x9800fe0fe03e00e2 0x13001fc1fc07c01c

def z444 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0x1da6b8000739e49f 0x63b4d70000e73c93

def z445 : W := mkw 0x0a1719b497915614 0x2142e33692f22ac2 0x77ff39f09fc1ff1d 0xeeffe73e13f83fe3

def z446 : W := mkw 0x1000020000428000 0x0200004000085000 0xbe81462080c7849f 0xb7d028c41018f093

def z447 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x0000b80e00000000 0x00001701c0000000

def z448 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xa9a6b90e07386086 0x7534d721c0e70c10

def z449 : W := mkw 0x101de60000428000 0xc203bcc000085000 0x1f9ffe0000c78003 0xa3f3ffc00018f000

def z450 : W := mkw 0xa008c04908240840 0x9401180921048108 0x63d841c118067864 0xec7b08382300cf0c

def z451 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x66c101f000c07f05 0xacd8203e00180fe0

def z452 : W := mkw 0x0802012001004400 0x2100402400200880 0x0426002007000401 0x0084c00400e00080

def z453 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0xf800ffffe0000000 0x1f001ffffc000000

def z454 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x0026000007000000 0x0004c00000e00000

def z455 : W := mkw 0x110002002042812a 0x0220004004085025 0x66c1003000c787ff 0xacd820060018f0ff

def z456 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x431fffdf60000000 0x0863fffbec000000

def z457 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001849f 0x2000000000003093

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec1003080c1879f 0xbfd82006101830f3

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0xfec14631e0c00705 0xbfd828c63c1800e0

def z460 : W := mkw 0x110002002042812a 0x0220004004085025 0x1ec1460000c787ff 0xa3d828c00018f0ff

def z461 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x679fb9fe00000000 0x0cf3f73fc0000000

def z462 : W := mkw 0x3008c20008668000 0x86011840010cd000 0x1f99c60018ff8003 0xe3f338c0031ff000

def z463 : W := mkw 0xa008c04908240840 0x9401180921048108 0xead840c1180618e6 0xbd5b08182300c31c

def z464 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x053f01f01fc07f01 0x40a7e03e03f80fe0

def z465 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xca58c0cf183e18e2 0x994b1819e307c31c

def z466 : W := mkw 0x303fefb01ef78000 0xe607fdf603def000 0x7fbffff01fff8003 0xeff7fffe03fff000

def z467 : W := mkw 0x24000002082c28c0 0x0480000041058518 0xeac04001183e78e6 0xfd5808002307cf1c

def z468 : W := mkw 0x10200a0016d38000 0x0204014002da7000 0x0020000007c18001 0x0004000000f83000

def z469 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfb98ffcfe0000000 0x1f731ff9fc000000

def z470 : W := mkw 0xdf1fffffe35be5be 0xfbe3fffffc6b7cb7 0xffffffffe7ffe7ff 0xfffffffffcfffcff

def z471 : W := mkw 0x3628fe068a7fa094 0xc6c51fc0d14ff412 0x9800fe0e803f809a 0x13001fc1d007f013

def z472 : W := mkw 0xc00000d940000000 0x1800001b28000000 0x400000d160000000 0x0800001a2c000000

def z473 : W := mkw 0xf03ff7fddce68000 0xfe07feffbb9cd000 0xff9ffffff8c60000 0x9ff3ffffff18c000

def z474 : W := mkw 0x0a02192483114414 0x2140432490622882 0x1da6b8208739841b 0x63b4d70410e73083

def z475 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x991effcfe0000000 0x1323dff9fc000000

def z476 : W := mkw 0xf51ff7ffe86ea9ea 0xfea3fefffd0dd53d 0xffdffffff8ffffff 0xfffbffffff1fffff

def z477 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x015881ce183e78e6 0xe02b1039c307cf1c

def z478 : W := mkw 0xa41dc04b1cac28c0 0x9483b80963958518 0xefffc1cf1ffe78e7 0xfdfff839e3ffcf1c

def z479 : W := mkw 0x3e2aff268b7fe494 0xe7c55fe4d16ffc92 0xbda6ff2e873fe49f 0x77b4dfe5d0e7fc93

def z480 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xeac0c00f003e00e6 0xbd581801e007c01c

def z481 : W := mkw 0xae0ad16f892c6cd4 0xb5c15a2df1258d9a 0xebd8c1ef983e7cfe 0xfd7b183df307cf9f

def z482 : W := mkw 0x0008c00000000000 0x8001180000000000 0x0b98c00000000000 0x0173180000000000

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0x6040003000000704 0x0c080006000000e0

def z484 : W := mkw 0x1f000a02235be5be 0x03e00140446b7cb7 0x0060000007ffe7ff 0xe00c000000fffcff

def z485 : W := mkw 0xa43dec4b1ebd28c0 0xd487bd8963d7a518 0xebfef9cf1f3e78e6 0xfd7fdf39e3e7cf1c

def z486 : W := mkw 0x0e1719b697997694 0x21c2e336d2f32ed2 0xbda7b93e87f9e79f 0x77b4f727d0ff3cf3

def z487 : W := mkw 0x8008c04900000000 0x9001180920000000 0xebd8c1cf000600e6 0xbd7b1839e000c01c

def z488 : W := mkw 0xce0219ffc3196494 0x39c0433ff8632c92 0xfda6b9ffe739e49f 0x7fb4d73ffce73c93

def z489 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9926b90e8739e09a 0x5324d721d0e73c13

def z490 : W := mkw 0x001701b000000000 0x2002e03600000000 0xff9f47f1e0000000 0x1ff3e8fe3c000000

def z491 : W := mkw 0x1f021b26a35be5be 0x23e04364d46b7cb7 0xbda6ff2fe73fe4ff 0x77b4dfe5fce7fc9f

def z492 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0x67ff47f17fc67f65 0xecffe8fe2ff8cfec

def z493 : W := mkw 0x8400004b000828c0 0x1080000960010518 0xeac041cf000678e6 0xbd580839e000cf1c

def z494 : W := mkw 0x303de6001ce68000 0xc607bcc0039cd000 0x1e99460018c78003 0xa3d328c00318f000

def z495 : W := mkw 0xc01ffdfdc2110000 0xf803ffbfb8422000 0xffbfffffe7398003 0x7ff7fffffce73000

def z496 : W := mkw 0x001701b000000000 0x2002e03600000000 0x67df01f018007804 0xecfbe03e03000f00

def z497 : W := mkw 0x110002002042812a 0x0220004004085025 0xeac0400100c787ff 0xbd5808002018f0ff

def z498 : W := mkw 0x0000000000000000 0x0000000000000000 0x2480002000000405 0x2490000400000080

def z499 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x0020000007c00701 0x0004000000f800e0

def z500 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd9c7fff83e78e6 0xfffb38ffff07cf1c

def z501 : W := mkw 0xbe3fff6f9fffecd4 0xf7c7ffedf3fffd9a 0xffffffef9ffffcff 0xfffffffdf3ffff9f

def z502 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07bf01c01fc07801 0xe0f7e03803f80f00

def z503 : W := mkw 0x110002002042812a 0x0220004004085025 0xbc810630e0c1879f 0x379020c61c1830f3

def z504 : W := mkw 0xce1ffdffc3196494 0xf9c3ffbff8632c92 0x013eb9ce07386000 0x4027d739c0e70c00

def z505 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013eb8001fff8003 0xe027d70003fff000

def z506 : W := mkw 0x1000020000428000 0x0200004000085000 0x0201460000c60000 0x804028c00018c000

def z507 : W := mkw 0x4015249040000000 0x4802a49208000000 0x0001061060000000 0x000020c20c000000

def z508 : W := mkw 0x00352c0016910000 0x4006a58002d22000 0x0026380007000000 0x0004c70000e00000

def z509 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffa7ff3fe739e49f 0x7ff4ffe7fce73c93

def z510 : W := mkw 0xf03ffffddef78000 0xfe07ffffbbdef000 0x1fbfffce1fff8003 0xe3f7fff9c3fff000

def z511 : W := mkw 0x1b021b24a353c53e 0x23604364946a78a7 0x14273e30e7c18719 0x0284e7c61cf830e3

def z512 : W := mkw 0x001ff52480000000 0xe003fea490000000 0xbf9fff2e80000000 0x17f3ffe5d0000000

def z513 : W := mkw 0x8408c04b000828c0 0x9081180960010518 0xebd8c1cf000078e4 0x1d7b1839e0000f1c

def z514 : W := mkw 0x3e200a021fffe494 0x07c4014043fffc92 0x002000001fffe49f 0xe004000003fffc93

def z515 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86b92e8001849f 0x37b0d725d0003093

def z516 : W := mkw 0x0e02092203196494 0x21c0412440632c92 0x25a601200739e49f 0x64b4c02400e73c93

def z517 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x63d881ce18387804 0xec7b1039c3070f00

def z518 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe15881cf183878e4 0x5c2b1039e3070f1c

def z519 : W := mkw 0xec1ff5ffddac7ec0 0xfd83febffbb58fd8 0xfffffffffffe7fe7 0xffffffffffffcffc

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x67d901f018c07f05 0xecfb203e03180fe0

def z521 : W := mkw 0x0015009014801200 0x0002a01202900240 0x63d901d018c07b04 0xec7b203a03180f60

def z522 : W := mkw 0x0015000014800000 0x0002a00002900000 0x013e00001f000000 0x4027c00003e00000

def z523 : W := mkw 0x110002002042812a 0x0220004004085025 0x66c1463160c60765 0xacd828c62c18c0ec

def z524 : W := mkw 0xb408c24b086ea8c0 0x96811849610dd518 0xffd9c7cf18fff8e7 0xfffb38f9e31fff1c

def z525 : W := mkw 0xa41de44b082c28c0 0xd483bc8961058518 0xffdfffcf183e78e6 0xfffbfff9e307cf1c

def z526 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xe11eb9ffe0000000 0x1c23d73ffc000000

def z527 : W := mkw 0xc00211fdc0000000 0x3800423fb8000000 0xfd86b9ffe0000000 0x1fb0d73ffc000000

def z528 : W := mkw 0xc608fc4fc2192094 0xd8c11f89f8432412 0x9800fe0fe039809a 0x13001fc1fc073013

def z529 : W := mkw 0xa01dc0d91ca41a40 0x9403b81b23948348 0x425940d118c61b60 0x884b281a2318c36c

def z530 : W := mkw 0x001fe5b000000000 0xe003fcb600000000 0x7f9ffff000000000 0x0ff3fffe00000000

def z531 : W := mkw 0x1a373f2497d3c414 0x6346e7e492fa7882 0x14273e2087c18419 0x0284e7c410f83083

def z532 : W := mkw 0x0002112480000000 0x2000422490000000 0x0106b90e00000000 0x0020d721c0000000

def z533 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xe21947ffe0000000 0x1c4328fffc000000

def z534 : W := mkw 0x110002002042812a 0x0220004004085025 0xbcc0002080c787ff 0xb79800041018f0ff

def z535 : W := mkw 0x0600100680082094 0x00c00200d0010412 0x8000000e80000098 0x10000001d0000013

def z536 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0xbca000208739e49f 0x7794000410e73c93

def z537 : W := mkw 0x2000000008240000 0x0400000001048000 0x00000000183e0002 0xe00000000307c000

def z538 : W := mkw 0x2e3ffd269fbd6494 0xe5c7ffa4d3f7ac92 0xbdbeb92e9f39e49f 0x77b7d725d3e73c93

def z539 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x046700301fc07f05 0xe08ce00603f80fe0

def z540 : W := mkw 0x0600180682192094 0x00c00300d0432412 0xbc80b82e8039849f 0x37901705d0073093

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0xa880000000000086 0x3510000000000010

def z542 : W := mkw 0xe03ffdfddeb50000 0xfc07ffbfbbd6a000 0x013eb9ce1f380000 0x4027d739c3e70000

def z543 : W := mkw 0x111de6002042812a 0xc223bcc004085025 0xffdffe31e0c787ff 0xbffbffc63c18f0ff

def z544 : W := mkw 0x1035260014c28000 0x4206a4c002985000 0x0001060000c00000 0x000020c000180000

def z545 : W := mkw 0x0400000200082080 0x0080000040010410 0xebd881ce18387886 0xfd7b1039c3070f10

def z546 : W := mkw 0x110002002042812a 0x0220004004085025 0xeac1461160c603e6 0xbd5828c22c18c07c

def z547 : W := mkw 0x0802012001004400 0x2100402400200880 0xbda601208701e49f 0x77b4c02410e03c93

def z548 : W := mkw 0x110002002042812a 0x0220004004085025 0x0001061060c00300 0x000020c20c180060

def z549 : W := mkw 0x0802012001004400 0x2100402400200880 0x2000012000006404 0x0400002400000c80

def z550 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xeb98c1cf003e00e2 0x1d731839e007c01c

def z551 : W := mkw 0xf03de6d95ce68000 0xde07bcdb2b9cd000 0x421946d178c60000 0x884328da2f18c000

def z552 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0xa9a0810e0739e49f 0x75341021c0e73c93

def z553 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xeb9ef9cf00000000 0x1d73df39e0000000

def z554 : W := mkw 0x1000020000428000 0x0200004000085000 0xfec1460100c780e7 0xbfd828c02018f01c

def z555 : W := mkw 0x1115029034c2932a 0x0222a05206985265 0x425946d178c61b60 0x884b28da2f18c36c

def z556 : W := mkw 0x001701b000000000 0x2002e03600000000 0x0407003000000000 0x0080e00600000000

def z557 : W := mkw 0x1000020000428000 0x0200004000085000 0x1401060000c18001 0x028020c000183000

def z558 : W := mkw 0x0e1ffd2683196494 0xe1c3ffa4d0632c92 0xbfbfff2e8739e49f 0x77f7ffe5d0e73c93

def z559 : W := mkw 0xce0afd6fc3196494 0xf9c15fadf8632c92 0xbda6ff2fe739e49f 0x77b4dfe5fce73c93

def z560 : W := mkw 0x0600180682192094 0x00c00300d0432412 0x0000b80e00380000 0x00001701c0070000

def z561 : W := mkw 0x2008c00008240000 0x8401180001048000 0x0218400018060000 0x804308000300c000

def z562 : W := mkw 0x363dfe069effa094 0xc6c7bfc0d3dff412 0x9fbffe0e9fff809b 0xf3f7ffc1d3fff013

def z563 : W := mkw 0x343dee021effa080 0xc687bdc043dff410 0xbfbfff0e1fffe087 0xf7f7ffe1c3fffc10

def z564 : W := mkw 0x31200a003ef7812a 0x0624014007def025 0xfee14631ffff87ff 0xffdc28c63ffff0ff

def z565 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0x9f9ffe0fe0000000 0x13f3ffc1fc000000

def z566 : W := mkw 0x8400004b000828c0 0x1080000960010518 0xe9c081cf003878e6 0x7d381039e0070f1c

def z567 : W := mkw 0xb43dee4b1effa8c0 0xd687bdc963dff518 0x9fbffe0f1fff80e3 0xf3f7ffc1e3fff01c

def z568 : W := mkw 0x3e3fff269fffe494 0xe7c7ffe4d3fffc92 0x1fbfff0e1fffe003 0xe3f7ffe1c3fffc00

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000000600e6 0xa00800000000c01c

def z570 : W := mkw 0x080201b015805600 0x2100403602b00ac0 0x606001f01fc07f05 0xec0c003e03f80fe0

def z571 : W := mkw 0x0000000000000000 0x0000000000000000 0x4241001000c00300 0x8848200200180060

def z572 : W := mkw 0x0802012001004400 0x2100402400200880 0x0126010007006000 0x4024c02000e00c00

def z573 : W := mkw 0xa41fc1fb082c28c0 0xb483f83f61058518 0xefdfc1ff183e78e6 0xfdfbf83fe307cf1c

def z574 : W := mkw 0xa81fc1f91da45e40 0xb503f83f23b48bc8 0x67ff41f11fc67f65 0xecffe83e23f8cfec

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x604001c000007804 0x0c08003800000f00

def z576 : W := mkw 0x110002002042812a 0x0220004004085025 0x0000000000c18719 0x00000000001830e3

def z577 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xbd86b92e8000649c 0x17b0d725d0000c93

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x88004001000600e2 0x110008002000c01c

def z579 : W := mkw 0xc41ff5ffc00828c0 0xf883febff8010518 0xffdfffffe00078e4 0x1ffbfffffc000f1c

def z580 : W := mkw 0x0000000000000000 0x0000000000000000 0x0681000000c00001 0xa0d0200000180000

def z581 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0xfbd8c7cff83ff8fe 0xff7b18f9ff07ff1f

def z582 : W := mkw 0x110002002042812a 0x0220004004085025 0x0040000000c60360 0x800800000018c06c

def z583 : W := mkw 0x34200a021effa8c0 0x0684014043dff518 0x006000001ffff8e7 0xe00c000003ffff1c

def z584 : W := mkw 0xe41ff5ffc82c28c0 0xfc83febff9058518 0x011eb9ce18387800 0x4023d739c3070f00

def z585 : W := mkw 0x3028ca001ef78000 0x8605194003def000 0x0bb8c0001fff8003 0xe177180003fff000

def z586 : W := mkw 0x801fc1f900000000 0xb003f83f20000000 0xef9fc1ff00000000 0x1df3f83fe0000000

def z587 : W := mkw 0x1900020035c2d72a 0x0320004006b85ae5 0xfee14631ffc7ffff 0xffdc28c63ff8ffff

def z588 : W := mkw 0xe01de4d948240840 0xdc03bc9b29048108 0x425946d178061860 0x884b28da2f00c30c

def z589 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x002000001f007800 0x4004000003e00f00

def z590 : W := mkw 0xd11ff7fde042812a 0xfa23feffbc085025 0xffdfffffe0c60360 0x9ffbfffffc18c06c

def z591 : W := mkw 0x110002002042812a 0x0220004004085025 0x1e814630e0c7871b 0xa3d028c61c18f0e3

def z592 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x625901f018c07f04 0x8c4b203e03180fe0

def z593 : W := mkw 0xe41de4db482c28c0 0xdc83bc9b69058518 0xebd9c7df783e78e6 0xfd7b38fbef07cf1c

def z594 : W := mkw 0xc00ad1fdc0000000 0xb8015a3fb8000000 0xeb98c1ffe0000000 0x1d73183ffc000000

def z595 : W := mkw 0x383fefb01ff7d600 0xe707fdf603fefac0 0x1fbffe301fff8703 0xe3f7ffc603fff0e0

def z596 : W := mkw 0x2c1701b21dac7ec0 0x2582e03643b58fd8 0x67ff01f01ffe7fe7 0xecffe03e03ffcffc

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x2180010000006004 0x6430002000000c00

def z598 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x023946001fff8003 0xe04728c003fff000

def z599 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x07bfb8001ff80001 0xe0f7f70003ff0000

def z600 : W := mkw 0x010000002000012a 0x0020000004000025 0xe6c10031e0c007fd 0xbcd820063c1800ff

def z601 : W := mkw 0x2008c00008240000 0x8401180001048000 0x0800c000003e0002 0x010018000007c000

def z602 : W := mkw 0xae0ad96f8b3d6cd4 0xb5c15b2df167ad9a 0xebfef9cf1f3e78e6 0xfd7fdf39e3e7cf1c

def z603 : W := mkw 0x0015009000000000 0x0002a01200000000 0x421900d000000000 0x0843201a00000000

def z604 : W := mkw 0x3e3dee021fffe494 0xc7c7bdc043fffc92 0x1fbffe001fffe49f 0xe3f7ffc003fffc93

def z605 : W := mkw 0xa608d84f8a3d28d4 0x94c11b09f147a51a 0xfbd8f9cf983ff8fe 0xff7b1f39f307ff1f

def z606 : W := mkw 0x0000009000001200 0x0000001200000240 0x404000d000001b00 0x0808001a00000360

def z607 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1a19fe0018ff8002 0x83433fc0031ff000

def z608 : W := mkw 0xc41ff5ffc0082080 0xf883febff8010410 0xff9fffffe0386086 0x7ff3fffffc070c10

def z609 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0400001000000e4 0x1c0800002000001c

def z610 : W := mkw 0x0000000000000000 0x0000000000000000 0xa980810e00000000 0x15301021c0000000

def z611 : W := mkw 0x0800000001005600 0x0100000000200ac0 0x0040000000007f04 0x0008000000000fe0

def z612 : W := mkw 0x1015020014c28000 0x0202a04002985000 0x1fbf46001fc78003 0xe3f7e8c003f8f000

def z613 : W := mkw 0xb03de6491ce68840 0xd607bcc9239cd108 0x425946c118c61860 0x884b28d82318c30c

def z614 : W := mkw 0x38200a001ff7d600 0x0704014003fefac0 0x006000001fffff07 0xe00c000003ffffe0

def z615 : W := mkw 0x0e17192697996494 0x21c2e324d2f32c92 0xbfbfb92e9ff9e49f 0xf7f7f725d3ff3c93

def z616 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x017e01c01fc07f05 0xe02fc03803f80fe0

def z617 : W := mkw 0x0a02192483114414 0x2140432490622882 0x0026380007000000 0x0004c70000e00000

def z618 : W := mkw 0x001de40000000000 0xc003bc8000000000 0xff9ffe31e0000000 0x1ff3ffc63c000000

def z619 : W := mkw 0xa008c04908240840 0x9401180921048108 0x0000400100060060 0x000008002000c00c

def z620 : W := mkw 0xac1fc1fb1dac7ec0 0xb583f83f63b58fd8 0xebfec1cf1f3e78e6 0xfd7fd839e3e7cf1c

def z621 : W := mkw 0x18372fb017d3d600 0x6306e5f602fa7ac0 0x77ff3ff01fc1ff05 0xeeffe7fe03f83fe0

def z622 : W := mkw 0xb428ca4b1effa8c0 0x9685194963dff518 0xebf8c1cf1ffff8e7 0xfd7f1839e3ffff1c

def z623 : W := mkw 0x190203202142c52a 0x23204064042858a5 0xffe74731e7c7e7ff 0xfffce8e63cf8fcff

def z624 : W := mkw 0xc00211fdc0000000 0x3800423fb8000000 0xfe8147ffe0000000 0x1fd028fffc000000

def z625 : W := mkw 0x3028e60008668000 0xc6051cc0010cd000 0x0000460000060000 0x000008c00000c000

def z626 : W := mkw 0x17001a06a25ba1be 0x02e00340d44b7437 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z627 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x425840c1183e78e6 0xe84b08182307cf1c

def z628 : W := mkw 0xae0ad96f8b3d6cd4 0xb5c15b2df167ad9a 0xbdbeb9ee9f39fc9f 0x77b7d73dd3e73f93

def z629 : W := mkw 0x202008001eb50000 0x0404010003d6a000 0x002000001f380000 0x4004000003e70000

def z630 : W := mkw 0xa400004b082c28c0 0x1480000961058518 0xe04001cf183e78e6 0xfc080039e307cf1c

def z631 : W := mkw 0xe40ad1ffc82c28c0 0xbc815a3ff9058518 0xebd8c1fff83e78e6 0xfd7b183fff07cf1c

def z632 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x66e7003007c00705 0xacdce00600f800e0

def z633 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x63d801f018007f04 0xec7b003e03000fe0

def z634 : W := mkw 0x2000000008240840 0x0400000001048108 0x0040000018061860 0x800800000300c30c

def z635 : W := mkw 0x1b021b24a353c53e 0x23604364946a78a7 0xfee77e31e7c787ff 0xbfdcefc63cf8f0ff

def z636 : W := mkw 0x1115029034c2932a 0x0222a05206985265 0xfed946f1f8c79fff 0xbfdb28de3f18f3ff

def z637 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x17bf3e001fc18001 0xe2f7e7c003f83000

def z638 : W := mkw 0xd03ffffdd6d38000 0xfa07ffffbada7000 0xffbfffffe7c18001 0x1ff7fffffcf83000

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0x425800c018001800 0x884b001803000300

def z640 : W := mkw 0x15000202204aa1aa 0x02a0004044095435 0xffc1c73fe0ffe7ff 0xfff838e7fc1ffcff

def z641 : W := mkw 0x383fefb01ff7d600 0xe707fdf603fefac0 0x1fbfffc01ffff803 0xe3f7fff803ffff00

def z642 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x163f7e001fc78001 0x82c7efc003f8f000

def z643 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xa126b92e8738649c 0x5424d725d0e70c93

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0x0401003000c00701 0x00802006001800e0

def z645 : W := mkw 0x0015009014801200 0x0002a01202900240 0x0001001000c00300 0x0000200200180060

def z646 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0xfec1c63fe0ff87ff 0xbfd838c7fc1ff0ff

def z647 : W := mkw 0xd11de6d96042812a 0xda23bcdb2c085025 0x425946d160c60360 0x884b28da2c18c06c

def z648 : W := mkw 0xc01fe5f940000000 0xf803fcbf28000000 0x679f47f160000000 0x0cf3e8fe2c000000

def z649 : W := mkw 0x0800000001004400 0x0100000000200880 0x0020000007006405 0x6004000000e00c80

def z650 : W := mkw 0xac0ac16b092c6cc0 0xb581582d61258d98 0xeffec1ef1f3e7ce7 0xfdffd83de3e7cf9c

def z651 : W := mkw 0x1f171bb6b7dbf7be 0x23e2e376d6fb7ef7 0xffffffffffffffff 0xffffffffffffffff

def z652 : W := mkw 0x000201b000000000 0x2000403600000000 0x600001f000000000 0x0c00003e00000000

def z653 : W := mkw 0x010000002000012a 0x0020000004000025 0x00400000000007fc 0x00080000000000ff

def z654 : W := mkw 0x800ad16d80000000 0xb0015a2db0000000 0xff9ef9ef80000000 0x1ff3df3df0000000

def z655 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0x9800c60fe03f80fa 0x130018c1fc07f01f

def z656 : W := mkw 0xf43fffffdeffa8c0 0xfe87fffffbdff518 0xfffffffffffff8e7 0xffffffffffffff1c

def z657 : W := mkw 0x1000020000428000 0x0200004000085000 0xfe814631e0c78003 0xbfd028c63c18f000

def z658 : W := mkw 0xb428ee4b0a7fa8c0 0xd6851dc9614ff518 0xfbd8ffcf183ff8e6 0xff7b1ff9e307ff1c

def z659 : W := mkw 0x0400000200082080 0x0080000040010410 0x0000000000386086 0x6000000000070c10

def z660 : W := mkw 0x2e0ad9268b3d6494 0xa5c15b24d167ac92 0xbfbef92e9f3fe49f 0xf7f7df25d3e7fc93

def z661 : W := mkw 0x17001a06a25ba1be 0x02e00340d44b7437 0xfec1fe3fe0ff87ff 0xbfd83fc7fc1ff0ff

def z662 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x0000800e00380000 0x00001001c0070000

def z663 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa5a6012e8700649d 0x74b4c025d0e00c93

def z664 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xb800b92e8039e49e 0x17001725d0073c93

def z665 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0xeb99c7df60000000 0x1d7338fbec000000

def z666 : W := mkw 0x081fe5b015805600 0xe103fcb602b00ac0 0x7ffffff01fc07f05 0xeffffffe03f80fe0

def z667 : W := mkw 0x343dee021effa8c0 0xc687bdc043dff518 0x1ffffe001ffff8e7 0xe3ffffc003ffff1c

def z668 : W := mkw 0x103dee0016d38000 0xc207bdc002da7000 0x1fbffe0007c18001 0x03f7ffc000f83000

def z669 : W := mkw 0x0000000014800000 0x0000000002900000 0x002000001fc00001 0xe004000003f80000

def z670 : W := mkw 0x201de40008240000 0xc403bc8001048000 0x1f9ffe00183e0002 0xe3f3ffc00307c000

def z671 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x142638208739e49f 0x6284c70410e73c93

def z672 : W := mkw 0x0400000200082080 0x0080000040010410 0x8800800e00380082 0x11001001c0070010

def z673 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67bf01f007c00701 0x0cf7e03e00f800e0

def z674 : W := mkw 0xae0ad96f8b3d6cd4 0xb5c15b2df167ad9a 0x013eb9ce1f387800 0x4027d739c3e70f00

def z675 : W := mkw 0x111703b02042812a 0x2222e07604085025 0xffdf47f1e0c787ff 0xbffbe8fe3c18f0ff

def z676 : W := mkw 0xd10213fde042812a 0x3a20427fbc085025 0xfec147ffe0c787ff 0xbfd828fffc18f0ff

def z677 : W := mkw 0xa608d84f8a3d28d4 0x94c11b09f147a51a 0x9800f80f803f80fa 0x13001f01f007f01f

def z678 : W := mkw 0xac1fc1fb1dac7ec0 0xb583f83f63b58fd8 0x67ff81fe1ff87f05 0xecfff03fc3ff0fe0

def z679 : W := mkw 0x110002002042812a 0x0220004004085025 0xf4410631e0c187fd 0x1e8820c63c1830ff

def z680 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x0006380000000000 0x0000c70000000000

def z681 : W := mkw 0x35000202286ea9ea 0x06a00040450dd53d 0x0040000018ffffff 0xe0080000031fffff

def z682 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xa020012e8739e49f 0x74040025d0e73c93

def z683 : W := mkw 0x0015000014800000 0x0002a00002900000 0x0219000018c00000 0x8043200003180000

def z684 : W := mkw 0xa41dc0db1cac3ac0 0x9483b81b63958758 0xebd9c1df18fe7be6 0xfd7b383be31fcf7c

def z685 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x1ea146001fff8003 0xe3d428c003fff000

def z686 : W := mkw 0xac1fc1fb1dac7ec0 0xb583f83f63b58fd8 0x013e81ce1f387800 0x4027d039c3e70f00

def z687 : W := mkw 0x0a02192483114414 0x2140432490622882 0xbda6b92e87018419 0x17b4d725d0e03083

def z688 : W := mkw 0x080201b001005600 0x2100403600200ac0 0x0000003000000700 0x00000006000000e0

def z689 : W := mkw 0x0a00080003114414 0x0140010000622882 0x0020000007018419 0x0004000000e03083

def z690 : W := mkw 0x0000000014801200 0x0000000002900240 0x0040000018c01b00 0x8008000003180360

def z691 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040000000c00705 0xa0080000001800e0

def z692 : W := mkw 0x383dee001ff7d600 0xc707bdc003fefac0 0x1ffffe001fffff07 0xe3ffffc003ffffe0

def z693 : W := mkw 0x281fc1b01da45600 0xa503f83603b48ac0 0x6fffc1f01ffe7f07 0xedfff83e03ffcfe0

def z694 : W := mkw 0xa43dec4b1ebd28c0 0xd487bd8963d7a518 0x013eb9ce1f387800 0x4027d739c3e70f00

def z695 : W := mkw 0x0600180682192094 0x00c00300d0432412 0xb980b90e8039e09e 0x77301721d0073c13

def z696 : W := mkw 0x511737b4e042812a 0x6a22e6f69c085025 0xfec77e31e0c787ff 0xbfd8efc63c18f0ff

def z697 : W := mkw 0x0e00180683196494 0x01c00300d0632c92 0x9820b80e8739e49f 0x73041701d0e73c93

def z698 : W := mkw 0x001711b480000000 0x2002e23690000000 0xff9fb9fe80000000 0x1ff3f73fd0000000

def z699 : W := mkw 0x0400000200082080 0x0080000040010410 0xbd80812e8039e49f 0x77b01025d0073c93

def z700 : W := mkw 0xc10211fde000012a 0x3820423fbc000025 0xe04001ffe00007fc 0x1c08003ffc0000ff

def z701 : W := mkw 0x001701b000000000 0x2002e03600000000 0x011e01c000000000 0x0023c03800000000

def z702 : W := mkw 0xc01711fdc0000000 0x3802e23fb8000000 0xe79f01ffe0000000 0x1cf3e03ffc000000

def z703 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0xebd9c7df78fe7be6 0xfd7b38fbef1fcf7c

def z704 : W := mkw 0x0000000000000000 0x0000000000000000 0xfe814631e001849f 0x3fd028c63c003093

def z705 : W := mkw 0xa008c04908240840 0x9401180921048108 0x001800c018001800 0x0003001803000300

def z706 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x779f3ff0e0000000 0x0ef3e7fe1c000000

def z707 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x35a6b92e8739e41d 0x66b4d725d0e73c83

def z708 : W := mkw 0xc808f44dd5805600 0xd9011e89bab00ac0 0x9860fe0fffc07f05 0xf30c1fc1fff80fe0

def z709 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0x9fbffe0f1fff8003 0xf3f7ffc1e3fff000

def z710 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xda18fecfe0000000 0x1b431fd9fc000000

def z711 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfde6b93e8739e79f 0x7fbcd727d0e73cf3

def z712 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffbeb9ee8739e49f 0x7ff7d73dd0e73c93

def z713 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x1da7be001fff8003 0xe3b4f7c003fff000

def z714 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9e81fe0fe0000000 0x13d03fc1fc000000

def z715 : W := mkw 0x110002002042812a 0x0220004004085025 0xfa414631e0c787fe 0x9f4828c63c18f0ff

def z716 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe040012f800064fc 0x1c080025f0000c9f

def z717 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa000012e8001e49f 0x34000025d0003c93

def z718 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbfbeb92e9f39e49f 0xf7f7d725d3e73c93

def z719 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x1000be0ee0000000 0x020017c1dc000000

def z720 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x033ffe001fff8003 0xe067ffc003fff000

def z721 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1826fe00073f8002 0x0304dfc000e7f000

def z722 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x053fb8001ff80001 0x40a7f70003ff0000

def z723 : W := mkw 0x1e021326814ae494 0x23c04264d0295c92 0xbe81472e80c7e49f 0xb7d028e5d018fc93

def z724 : W := mkw 0x0e0219b683197694 0x21c04336d0632ed2 0xbda6b9ee8739fc9f 0x77b4d73dd0e73f93

def z725 : W := mkw 0x20352c001eb50000 0x4406a58003d6a000 0x002638001f380000 0x4004c70003e70000

def z726 : W := mkw 0x110002002042812a 0x0220004004085025 0xffc7fe31e0c787ff 0xbff8ffc63c18f0ff

def z727 : W := mkw 0xaa0ad96d8b354c54 0xb5415b2db166a98a 0x567e78e19f079c79 0x8acfcf1c33e0f38f

def z728 : W := mkw 0xce0211ffc1086494 0x39c0423ff8210c92 0x000001ce00006000 0x00000039c0000c00

def z729 : W := mkw 0x31200a003ef7812a 0x0624014007def025 0xffe7fe31ffff87ff 0xfffcffc63ffff0ff

def z730 : W := mkw 0x110002002042812a 0x0220004004085025 0xe2414631e0c787ff 0xbc4828c63c18f0ff

def z731 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x015881ce183e7860 0xc02b1039c307cf0c

def z732 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbfb8001ff98003 0xe3f7f70003ff3000

def z733 : W := mkw 0x0000080002110000 0x0000010000422000 0x09a6b80007380002 0x6134d70000e70000

def z734 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x8000010e80006098 0x10000021d0000c13

def z735 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x63feb9c01f387804 0xec7fd73803e70f00

def z736 : W := mkw 0x0000100480000000 0x0000020090000000 0x9800fe0fe0000000 0x13001fc1fc000000

def z737 : W := mkw 0x24000002082c28c0 0x0480000041058518 0xebd881ce183e78e6 0xfd7b1039c307cf1c

def z738 : W := mkw 0x0000080002110000 0x0000010000422000 0x1fa7b80007f98003 0xe3f4f70000ff3000

def z739 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xffffffc11ffff8e7 0xfffffff823ffff1c

def z740 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fff01f01fc1ff07 0xefffe03e03f83fe0

def z741 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe958c1cf183e78e6 0x5d2b1839e307cf1c

def z742 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe001f3f8002 0x43f7ffc003e7f000

def z743 : W := mkw 0xac1fc1fb1dac7ec0 0xb583f83f63b58fd8 0x8c27c03f07fe07e3 0x1184f807e0ffc0fc

def z744 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0xfe877fffe0000000 0x1fd0effffc000000

def z745 : W := mkw 0x213dec003eb5012a 0xc427bd8007d6a025 0xe17eb831ff3807fc 0x5c2fd7063fe700ff

def z746 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbffe001f3e0002 0xe3f7ffc003e7c000

def z747 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe00784ff 0xbffbfffffc00f09f

def z748 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xbfbffe30ffff879f 0xf7f7ffc61ffff0f3

def z749 : W := mkw 0x0400080202192080 0x0080010040432410 0xbda6b92e8739e49f 0x77b4d725d0e73c93

def z750 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff01f09fc07f05 0xffffe03e13f80fe0

def z751 : W := mkw 0xe408e44b482c28c0 0xdc811c8969058518 0xebd8c7cf783e78e6 0xfd7b18f9ef07cf1c

def z752 : W := mkw 0x30200a000a778000 0x06040140014ef000 0x1da6b800073f8003 0x63b4d70000e7f000

def z753 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xb9a6b90e8739e09e 0x7734d721d0e73c13

def z754 : W := mkw 0x303dee001ef78840 0xc607bdc003def108 0x1ffffe001fff9863 0xe3ffffc003fff30c

def z755 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd8c1ef983e78e6 0xfffb183df307cf1c

def z756 : W := mkw 0x1f0213b6a14af7be 0x23e04276d4295ef7 0xfec147ffe0c7ffff 0xbfd828fffc18ffff

def z757 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x153fbffeffc07f01 0x42a7f7ffdff80fe0

def z758 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9800fe0fe001809a 0x13001fc1fc003013

def z759 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff41f11fc07f05 0xfdffe83e23f80fe0

def z760 : W := mkw 0x31352e003ef7812a 0x4626a5c007def025 0xfee77e31ffff87ff 0xffdcefc63ffff0ff

def z761 : W := mkw 0x0002192482110000 0x2000432490422000 0xbda6b92e8739849f 0x77b4d725d0e73093

def z762 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xff9fffffe0060060 0x1ff3fffffc00c00c

def z763 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xbc80fe2fe001849f 0x37901fc5fc003093

def z764 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x67f901f01fc07f05 0xecff203e03f80fe0

def z765 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe3d801ee98007c9c 0xfc7b003dd3000f93

def z766 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffe7c06705 0x7ff7fffffcf80ce0

def z767 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xf800fe3fe0000000 0x1f001fc7fc000000

def z768 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z769 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xffdffffff83e1862 0xfffbffffff07c30c

def z770 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xffdfffffe0c07f05 0xbffbfffffc180fe0

def z771 : W := mkw 0x94352e4b16dba8c0 0x5286a5c962db7518 0xf4673fcf07c1f8e5 0x1e8ce7f9e0f83f1c

def z772 : W := mkw 0xe01ff5fddca40000 0xfc03febfbb948000 0xffbffffffffe0003 0xfff7ffffffffc000

def z773 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xbfbffe209fff8003 0xf7f7ffc413fff000

def z774 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xb4073f3ee0000000 0x1680e7e7dc000000

def z775 : W := mkw 0x200008000a350000 0x040001000146a000 0x1da6b8001f3f8003 0xe3b4d70003e7f000

def z776 : W := mkw 0x201de4001ca40000 0xc403bc8003948000 0x1fbffe001ffe0003 0xe3f7ffc003ffc000

def z777 : W := mkw 0x11150a0036d3812a 0x0222a14006da7025 0xfffffe31ffff87ff 0xffffffc63ffff0ff

def z778 : W := mkw 0x0000080002110000 0x0000010000422000 0x3da6b82007398407 0x67b4d70400e73080

def z779 : W := mkw 0xce0211ffc1087694 0x39c0423ff8210ed2 0xe04001ffe0007f9c 0x1c08003ffc000ff3

def z780 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x5ffffe117fff87ff 0xebffffc22ffff0ff

def z781 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x77ff07f0ffc07f05 0xeeffe0fe1ff80fe0

def z782 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9b98fe0fe0000000 0x13731fc1fc000000

def z783 : W := mkw 0x481725b055805600 0x6902e4b60ab00ac0 0x67ff07f07fc07f05 0xecffe0fe0ff80fe0

def z784 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xffffbffeffc07f05 0xfffff7ffdff80fe0

def z785 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe00ffff801b 0xe3f7ffc01ffff003

def z786 : W := mkw 0x3028ca001ef78000 0x8605194003def000 0x1fbef8001fff8003 0xe3f7df0003fff000

def z787 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x013e01c01fc07f01 0x4027c03803f80fe0

def z788 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xffdffffff8067864 0xfffbffffff00cf0c

def z789 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0xffffffcf1ffff807 0xfffffff9e3ffff00

def z790 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x0000fe0f60000000 0x00001fc1ec000000

def z791 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x47ff00d01fc07f05 0xe8ffe01a03f80fe0

def z792 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xffbffe31ffff849f 0xfff7ffc63ffff093

def z793 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xbfbffe001fff8087 0xf7f7ffc003fff010

def z794 : W := mkw 0x1f021b26a35be5be 0x23e04364d46b7cb7 0x4367ff1f67fe6360 0xc86cffe3ecffcc6c

def z795 : W := mkw 0xe03decd95eb50000 0xdc07bd9b2bd6a000 0x433ffed17f380000 0x4867ffda2fe70000

def z796 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1c27be0007f98003 0x0384f7c000ff3000

def z797 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe6c1013e80c0679d 0xbcd82027d0180cf3

def z798 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe001ffe0000 0xc3f7ffc003ffc000

def z799 : W := mkw 0x3e3ff7269deee494 0xe7c7fee4d3bddc92 0xa219472e98c6649c 0x944328e5d318cc93

def z800 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xfc07ffffe0000000 0x1f80fffffc000000

def z801 : W := mkw 0xe008f44dc8240000 0xdc011e89b9048000 0x9800fe0fe03e0002 0x13001fc1fc07c000

def z802 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x05beb8001f380001 0x60b7d70003e70000

def z803 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffff1ffffffff 0xfffffffe3fffffff

def z804 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25fe01e01fc07f05 0xe4bfc03c03f80fe0

def z805 : W := mkw 0xce1ff5ffc1086494 0xf9c3febff8210c92 0xe21947ffe000649c 0x1c4328fffc000c93

def z806 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0c1879f 0xbffbfffffc1830f3

def z807 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0x5fbffec11fff8003 0xebf7ffd823fff000

def z808 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0xff9ffe3fe0000000 0x1ff3ffc7fc000000

def z809 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0x9818fecfe0000000 0x13031fd9fc000000

def z810 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x0bd8c1ce183e78e6 0xe17b1839c307cf1c

def z811 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x993efe01ff3f80fa 0x5327dfc03fe7f01f

def z812 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbffe001ff80001 0xe3f7ffc003ff0000

def z813 : W := mkw 0xc000344dc0000000 0x58000689b8000000 0x90003e0fe0000000 0x120007c1fc000000

def z814 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x9f9fffcfe0000000 0x13f3fff9fc000000

def z815 : W := mkw 0x10000a0002538000 0x02000140004a7000 0x1da6fe00073f8003 0x63b4dfc000e7f000

def z816 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x0126b8001fff8003 0xe024d70003fff000

def z817 : W := mkw 0xce1decdb43196494 0xd9c3bd9b68632c92 0x423946d16739e49f 0x684728da2ce73c93

def z818 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x77ffbffeffc07f05 0xeefff7ffdff80fe0

def z819 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x111ebfcee0000000 0x0223d7f9dc000000

def z820 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe000013fe000649c 0x1c000027fc000c93

def z821 : W := mkw 0xa03dec491eb50000 0xd407bd8923d6a000 0x013eb9ce1f380000 0x4027d739c3e70000

def z822 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x007800c01fc07f05 0xe00f001803f80fe0

def z823 : W := mkw 0xf13deed97ef7812a 0xde27bddb2fdef025 0xfffffef1ffff87ff 0xffffffde3ffff0ff

def z824 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07bf01f01fc07f01 0xe0f7e03e03f80fe0

def z825 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0xfec101fe80c1ff9f 0xbfd8203fd0183ff3

def z826 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffffffffe7c06705 0xfffffffffcf80ce0

def z827 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xea58c1cf183e78e6 0x9d4b1839e307cf1c

def z828 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x4bd8c1cf183e7862 0xe97b1839e307cf0c

def z829 : W := mkw 0xf03deed95ef78840 0xde07bddb2bdef108 0x5ffffed17fff9863 0xebffffda2ffff30c

def z830 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffffffffc07f05 0xfffffffffff80fe0

def z831 : W := mkw 0xd11ff7fde042812a 0xfa23feffbc085025 0x015eb9ce00c787ff 0xa02bd739c018f0ff

def z832 : W := mkw 0x110002002042812a 0x0220004004085025 0xffc14731e0c7e7ff 0xfff828e63c18fcff

def z833 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x0118c1cf183e7860 0x40231839e307cf0c

def z834 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9da6b82e8739849b 0x73b4d705d0e73093

def z835 : W := mkw 0x0000080002110000 0x0000010000422000 0x1926b80007398002 0x4324d70000e73000

def z836 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x1da7b80007f98003 0x63b4f70000ff3000

def z837 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xffffffffffc01b01 0xfffffffffff80360

def z838 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x25bf01f01fc07f05 0x64b7e03e03f80fe0

def z839 : W := mkw 0xf03deed95ef78000 0xde07bddb2bdef000 0xffbfffdf7fff8003 0xfff7fffbeffff000

def z840 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xeac0412f800664fe 0xbd580825f000cc9f

def z841 : W := mkw 0x0802012015805600 0x2100402402b00ac0 0x67fe01e01fc07f05 0xecffc03c03f80fe0

def z842 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6b92e8739849b 0x17b4d725d0e73093

def z843 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x153eb8001f398001 0x42a7d70003e73000

def z844 : W := mkw 0xf0221bfddef78000 0x3e04437fbbdef000 0xe02001ffffff8003 0xfc04003ffffff000

def z845 : W := mkw 0x1f021326a14ae5be 0x23e04264d4295cb7 0xb401073ee0c1e79d 0x168020e7dc183cf3

def z846 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x002638001fff8003 0xe004c70003fff000

def z847 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9d26b92e8739e49b 0x53a4d725d0e73c93

def z848 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7fbffe301fff8003 0xeff7ffc603fff000

def z849 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffffc1ff9f 0xfffffffffff83ff3

def z850 : W := mkw 0x11000a002253812a 0x02200140044a7025 0x1de6b80007ff87ff 0xe3bcd70000fff0ff

def z851 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe31ffff8707 0xffffffc63ffff0e0

def z852 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x63d881ce183e78e6 0xec7b1039c307cf1c

def z853 : W := mkw 0x2008c8000a350000 0x840119000146a000 0x013eb8001f380000 0x4027d70003e70000

def z854 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd9c1ff98ffffff 0xfffb383ff31fffff

def z855 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xa126b92e8739e49f 0x7424d725d0e73c93

def z856 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xf91effffe0000000 0x1f23dffffc000000

def z857 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x477f01f01fc07f01 0xc8efe03e03f80fe0

def z858 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0018419 0x1ff3fffffc003083

def z859 : W := mkw 0x3008ca000a778000 0x86011940014ef000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z860 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6b92e8739e419 0x57b4d725d0e73c83

def z861 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xbfbffe21ffff84ff 0xf7f7ffc43ffff09f

def z862 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xbd87ff3fe0000000 0x17b0ffe7fc000000

def z863 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0x14073ffee0000000 0x0280e7ffdc000000

def z864 : W := mkw 0x303dee901ef78000 0xc607bdd203def000 0x5fbffed01fff8003 0xebf7ffda03fff000

def z865 : W := mkw 0x0000080002110000 0x0000010000422000 0x1526b80007398001 0x42a4d70000e73000

def z866 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfec1fe3fe0c00705 0xbfd83fc7fc1800e0

def z867 : W := mkw 0xae0ad16f892c6cd4 0xb5c15a2df1258d9a 0xe25841ef98067cfc 0x9c4b083df300cf9f

def z868 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc1ff9f 0xecffe03e03f83ff3

def z869 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0xbdbeb8209f39849f 0x77b7d70413e73093

def z870 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xf61f7fffe0000000 0x1ec3effffc000000

def z871 : W := mkw 0x0e1711b695887694 0x21c2e236d2b10ed2 0xe25901fe98c07f9c 0x9c4b203fd3180ff3

def z872 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x25a6b92e0739e49f 0x64b4d725c0e73c93

def z873 : W := mkw 0xc01ff5fdc0001200 0xf803febfb8000240 0xffdfffffe0001b00 0x1ffbfffffc000360

def z874 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x63d8c1cf183e7864 0xec7b1839e307cf0c

def z875 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x437f01d01fc07f05 0xe86fe03a03f80fe0

def z876 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x657f01f01fc07f05 0x4cafe03e03f80fe0

def z877 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x3fbfff001fffe007 0xe7f7ffe003fffc00

def z878 : W := mkw 0x0008ec0002110000 0xc0011d8000422000 0x1da6fe0007398003 0x63b4dfc000e73000

def z879 : W := mkw 0xc00211fdc0000000 0x3800423fb8000000 0xff87ffffe0000000 0x1ff0fffffc000000

def z880 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x427800c01fc07f05 0xe84f001803f80fe0

def z881 : W := mkw 0xb13de6493ce6896a 0xd627bcc9279cd12d 0x425946d178c61b60 0x884b28da2f18c36c

def z882 : W := mkw 0x3108ca002a77812a 0x86211940054ef025 0xfffffe31ffff87ff 0xffffffc63ffff0ff

def z883 : W := mkw 0x641735b6c82c28c0 0x6c82e6b6d9058518 0x14473e30f83e78e6 0xe288e7c61f07cf1c

def z884 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0xa000012f800064fc 0x14000025f0000c9f

def z885 : W := mkw 0x1b171bb4b7d3d73e 0x2362e37696fa7ae7 0x14273e30e7c18719 0x0284e7c61cf830e3

def z886 : W := mkw 0x0802112481004400 0x2100422490200880 0xffe7ff3fe7c06705 0xfffcffe7fcf80ce0

def z887 : W := mkw 0xe81ff5fddda45600 0xfd03febfbbb48ac0 0xfffffffffffe7f07 0xffffffffffffcfe0

def z888 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfa80fe0fe0000000 0x1f501fc1fc000000

def z889 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0000086 0x3ff3fffffc000010

def z890 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0xb800ff2fe0000000 0x17001fe5fc000000

def z891 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0xff9fffcfe0000000 0x1ff3fff9fc000000

def z892 : W := mkw 0x0000080002110000 0x0000010000422000 0x05a6b80007380001 0x60b4d70000e70000

def z893 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9926b90e8739e49f 0x7324d721d0e73c93

def z894 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x5f9fffdf60000000 0x0bf3fffbec000000

def z895 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xffbfffffff000000 0x5ff7ffffffe00000

def z896 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe00600e2 0x1ff3fffffc00c01c

def z897 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x011881ce183e78e2 0x40231039c307cf1c

def z898 : W := mkw 0x1f000a02235be5be 0x03e00140446b7cb7 0x00200000073fe4ff 0x6004000000e7fc9f

def z899 : W := mkw 0x382aefb00b77d600 0xe7055df6016efac0 0x7840fff0003fff06 0x0f081ffe0007ffe0

def z900 : W := mkw 0xa400004b082c28c0 0x1480000961058518 0xe3d801cf183e78e6 0xfc7b0039e307cf1c

def z901 : W := mkw 0xc81735fdd5805600 0x7902e6bfbab00ac0 0xf7ff3fffffc07f05 0xfeffe7fffff80fe0

def z902 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbdbeb9ee9f39fc9f 0x77b7d73dd3e73f93

def z903 : W := mkw 0xcc0211ffc1087ec0 0x3980423ff8210fd8 0xe04001ffe0007fe4 0x1c08003ffc000ffc

def z904 : W := mkw 0x0615189696993294 0x00c2a312d2d32652 0xda59b8de98f99b9a 0x9b4b371bd31f3373

def z905 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xfbd8c1cf983ff8fe 0xff7b1839f307ff1f

def z906 : W := mkw 0x110002002042812a 0x0220004004085025 0xffc1c73fe0c787ff 0xbff838e7fc18f0ff

def z907 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0x9800ffcfe0000000 0x13001ff9fc000000

def z908 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe309fff879f 0xffffffc613fff0f3

def z909 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1dbeb8001fff8003 0xe3b7d70003fff000

def z910 : W := mkw 0xc81ff5fdd5804400 0xf903febfbab00880 0xffbfffffffc06405 0xfff7fffffff80c80

def z911 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1da6b90e0739e49f 0x63b4d721c0e73c93

def z912 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffffc67fe7 0xfffffffffff8cffc

def z913 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1ffffe001ffff807 0xe3ffffc003ffff00

def z914 : W := mkw 0x0f021126a10865be 0x21e04224d4210cb7 0xa040012e800067fc 0x14080025d0000cff

def z915 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013fbe001ff80000 0x4027f7c003ff0000

def z916 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x07bffe001ffe0001 0xe0f7ffc003ffc000

def z917 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01f09fc07f9d 0xfcffe03e13f80ff3

def z918 : W := mkw 0x0000080002110000 0x0000010000422000 0x1da6b8000739849f 0x63b4d70000e73093

def z919 : W := mkw 0x0e02192683196cd4 0x21c04324d0632d9a 0xbde6b92e8739fcff 0x77bcd725d0e73f9f

def z920 : W := mkw 0x191703b035c2d72a 0x2322e07606b85ae5 0x993e47c1ff07f8fa 0x5327c8f83fe0ff1f

def z921 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x03beb8001f380000 0xe077d70003e70000

def z922 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffffc07f01 0x5ff7fffffff80fe0

def z923 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8958c1cf183e78e6 0xf12b1839e307cf1c

def z924 : W := mkw 0xf03deed95ef78000 0xde07bddb2bdef000 0x1fbffec01fff8003 0xe3f7ffd803fff000

def z925 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xa9d881ce183e78e6 0xf53b1039c307cf1c

def z926 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdffffff80678e6 0xfffbffffff00cf1c

def z927 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x9fbffe011fff80e3 0xf3f7ffc023fff01c

def z928 : W := mkw 0x11000a002253812a 0x02200140044a7025 0x5fe7fe1167ff8363 0xebfcffc22cfff06c

def z929 : W := mkw 0x110002002042812a 0x0220004004085025 0xffd947f1e0c787ff 0xbffb28fe3c18f0ff

def z930 : W := mkw 0x0602192682192094 0x20c04324d0432412 0xbda6b92e8739809b 0x77b4d725d0e73013

def z931 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x9c07be3ee0000000 0x1380f7c7dc000000

def z932 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0xfd86ffffe0000000 0x1fb0dffffc000000

def z933 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x1f9ffffee0000000 0x03f3ffffdc000000

def z934 : W := mkw 0xb03deed91ef79a40 0xd607bddb23def348 0x5ffffed11fff9b63 0xebffffda23fff36c

def z935 : W := mkw 0xb528ee4b2a7fa9ea 0xd6a51dc9654ff53d 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z936 : W := mkw 0x0008c80002110000 0x8001190000422000 0x1fbef80007398003 0x63f7df0000e73000

def z937 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x0bbef8001f380000 0x4177df0003e70000

def z938 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbfa7b92e87f9e49f 0xf7f4f725d0ff3c93

def z939 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffbfffffe701e49f 0x7ff7fffffce03c93

def z940 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x17bf3e001fff8003 0xe2f7e7c003fff000

def z941 : W := mkw 0x3f200a023fffe5be 0x07e4014047fffcb7 0x006000001fffe7ff 0xe00c000003fffcff

def z942 : W := mkw 0x1f021326a14ae5be 0x23e04264d4295cb7 0xa040012e80c7e7ff 0xb4080025d018fcff

def z943 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe209fff841b 0xe3f7ffc413fff083

def z944 : W := mkw 0x0e0219b683197694 0x21c04336d0632ed2 0xffe7b9fe87f9ff9f 0xfffcf73fd0ff3ff3

def z945 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0x000001ce00007800 0x00000039c0000f00

def z946 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b90e07398003 0x77b4d721c0e73000

def z947 : W := mkw 0x17000a02225ba1be 0x02e00140444b7437 0x0040000000ff87ff 0xa0080000001ff0ff

def z948 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x0000012e80006418 0x00000025d0000c83

def z949 : W := mkw 0x080201b015805600 0x2100403602b00ac0 0x63f801f01fc07f05 0xec7f003e03f80fe0

def z950 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe001fff80fb 0xe3f7ffc003fff01f

def z951 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd9c7fff8fe7fe7 0xfffb38ffff1fcffc

def z952 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xff9ffffff8001800 0x1ff3ffffff000300

def z953 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x033fb8001ff80000 0xc067f70003ff0000

def z954 : W := mkw 0x110002002042812a 0x0220004004085025 0x56414631e0c787ff 0xaac828c63c18f0ff

def z955 : W := mkw 0x2008c8000a350000 0x840119000146a000 0xfffef8219f3f84ff 0xffffdf0433e7f09f

def z956 : W := mkw 0x0a02192483114414 0x2140432490622882 0xbda6b92e8739841b 0x77b4d725d0e73083

def z957 : W := mkw 0xce0211ffc1086494 0x39c0423ff8210c92 0xfe8147ffe001e49f 0x3fd028fffc003c93

def z958 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe358c1cf183e78e4 0xdc6b1839e307cf1c

def z959 : W := mkw 0x0000080002110000 0x0000010000422000 0xffe6f801073f80e7 0xfffcdf0020e7f01c

def z960 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa000010e00006084 0x14000021c0000c10

def z961 : W := mkw 0x0000080002110000 0x0000010000422000 0x1da6b8208739841b 0x63b4d70410e73083

def z962 : W := mkw 0xa408e44b082c28c0 0xd4811c8961058518 0xfbd8ffcf183e78e6 0xff7b1ff9e307cf1c

def z963 : W := mkw 0x110002002042812a 0x0220004004085025 0xfec14631f8c7ffff 0xffd828c63f18ffff

def z964 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffe01ffff80ff 0xffffffc03ffff01f

def z965 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013eb8001f3f8002 0x4027d70003e7f000

def z966 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0xdf9ffedfe0000000 0x1bf3ffdbfc000000

def z967 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x0026b80007380000 0x0004d70000e70000

def z968 : W := mkw 0x2008c8000a350000 0x840119000146a000 0x1da6f800073f8003 0x63b4df0000e7f000

def z969 : W := mkw 0xb508c24b286ea9ea 0x96a11849650dd53d 0x151987fef8f9ff19 0x42a330ffdf1f3fe3

def z970 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x013eb8001f3e0002 0xe027d70003e7c000

def z971 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xefd8c1ef183e7ce7 0xfdfb183de307cf9c

def z972 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1ea7fe0007ff8003 0xa3d4ffc000fff000

def z973 : W := mkw 0xe03decd95eb50000 0xdc07bd9b2bd6a000 0x013eb8c01f380000 0x4027d71803e70000

def z974 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x14273e001ff98001 0x4284e7c003ff3000

def z975 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfbd8ffcff8007804 0xff7b1ff9ff000f00

def z976 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe001fff849f 0xe3f7ffc003fff093

def z977 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd9c7df783e78e6 0xfd7b38fbef07cf1c

def z978 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xffbffe31ffff871b 0xfff7ffc63ffff0e3

def z979 : W := mkw 0xc80af5fdc1005600 0xf9015ebfb8200ac0 0xf840ffffe0007f04 0x1f081ffffc000fe0

def z980 : W := mkw 0xce02116fc1086494 0x39c0422df8210c92 0xa000012fe000649c 0x14000025fc000c93

def z981 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xbc80fe2fe0000000 0x17901fc5fc000000

def z982 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff41f19fc7ffff 0xffffe83e33f8ffff

def z983 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xbffffe209fff87ff 0xf7ffffc413fff0ff

def z984 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x07ff01c01fc07f05 0xe0ffe03803f80fe0

def z985 : W := mkw 0x203dec901eb51200 0xc407bd9203d6a240 0x013eb8c01f381800 0x4027d71803e70300

def z986 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0000704 0x1ffbfffffc0000e0

def z987 : W := mkw 0x9f02136fa14aedfe 0x33e0426df4295dbf 0xfec147ffe0c7ffff 0xbfd828fffc18ffff

def z988 : W := mkw 0x110002002042812a 0x0220004004085025 0xbc814631e0c787ff 0x379028c63c18f0ff

def z989 : W := mkw 0x303dee901ef79200 0xc607bdd203def240 0x1fbffec01fff9803 0xe3f7ffd803fff300

def z990 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x093ef8001f3e0002 0x4127df0003e7c000

def z991 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0x9c07fe0fe0000000 0x1380ffc1fc000000

def z992 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xdffffe11ffff83fb 0xfbffffc23ffff07f

def z993 : W := mkw 0xc80af56dc1004400 0xf9015eadb8200880 0xbda6ff2fe7006405 0x77b4dfe5fce00c80

def z994 : W := mkw 0x0000080002110000 0x0000010000422000 0x1fa7fe0007398003 0x63f4ffc000e73000

def z995 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xf800ffcfe0000000 0x1f001ff9fc000000

def z996 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x14273e0007ff8003 0x0284e7c000fff000

def z997 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff47f1ffc1ff9f 0xffffe8fe3ff83ff3

def z998 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x9fbffe31ffff87fb 0xf3f7ffc63ffff0ff

def z999 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x1dbeb8001f398003 0x63b7d70003e73000

def z1000 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1c27fe001fff8003 0xe384ffc003fff000

def z1001 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfee7fe31e7ff87ff 0xbfdcffc63cfff0ff

def z1002 : W := mkw 0x0015009014801200 0x0002a01202900240 0x67ff01d01fc07b05 0xecffe03a03f80f60

def z1003 : W := mkw 0xf13de6d97ce6812a 0xde27bcdb2f9cd025 0x425946d178c60360 0x884b28da2f18c06c

def z1004 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1926fe00073f8002 0x4324dfc000e7f000

def z1005 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1527be0007f98001 0x42a4f7c000ff3000

def z1006 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xff99ffffe0000000 0x1ff33ffffc000000

def z1007 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x6fff81f01ff87f07 0xedfff03e03ff0fe0

def z1008 : W := mkw 0x313dee903ef7932a 0xc627bdd207def265 0xfffffef1ffff9fff 0xffffffde3ffff3ff

def z1009 : W := mkw 0x0000080002110000 0x0000010000422000 0x1fbeb8001f398003 0xe3f7d70003e73000

def z1010 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xbc80012e8000649c 0x17900025d0000c93

def z1011 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1ef983e7cfe 0xfd7b183df307cf9f

def z1012 : W := mkw 0x001ff52480000000 0xe003fea490000000 0xff9fff3fe0000000 0x1ff3ffe7fc000000

def z1013 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xffffb9fe9fc1ff9f 0xfffff73fd3f83ff3

def z1014 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdffffff8001800 0x9ffbffffff000300

def z1015 : W := mkw 0x2028ec000a350000 0xc4051d800146a000 0x1da6b80007398003 0x63b4d70000e73000

def z1016 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0xe7ff01fe9fc07f05 0xfcffe03fd3f80fe0

def z1017 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1126b90e8739e018 0x4224d721d0e73c03

def z1018 : W := mkw 0x081725b015805600 0x6102e4b602b00ac0 0x77ff3ff01fc07f05 0xeeffe7fe03f80fe0

def z1019 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xa998c1cf183e78e6 0x75331839e307cf1c

def z1020 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe219fff84ff 0xffffffc433fff09f

def z1021 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xffbffe011fff8003 0xfff7ffc023fff000

def z1022 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9da6b90e8739e09b 0x73b4d721d0e73c13

def z1023 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0xe04001cf000078e4 0x1c080039e0000f1c

def z1024 : W := mkw 0x3f000a022b7fedfe 0x07e00140456ffdbf 0x006000001fffffff 0xe00c000003ffffff

def z1025 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1da7fe0007ff8003 0x63b4ffc000fff000

def z1026 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x113ebe001f398000 0x4227d7c003e73000

def z1027 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1ffffe001fff8707 0xe3ffffc003fff0e0

def z1028 : W := mkw 0x3028ee001ef78000 0xc6051dc003def000 0x1da6fe001fff8003 0xe3b4dfc003fff000

def z1029 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x9c27fe31e7ff87fb 0x1384ffc63cfff0ff

def z1030 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffa6f92f8739e49f 0x7ff4df25f0e73c93

def z1031 : W := mkw 0x8e0211ff81087ed4 0x31c0423ff0210fda 0xe04001ff80007ffc 0x1c08003ff0000fff

def z1032 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9ffffff8007800 0x5ff3ffffff000f00

def z1033 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc67fe7 0xecffe03e03f8cffc

def z1034 : W := mkw 0xe008f44dc8240840 0xdc011e89b9048108 0x9800fe0fe0060060 0x13001fc1fc00c00c

def z1035 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01f1ffc07f05 0xfcffe03e3ff80fe0

def z1036 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0x991efe0fe0000000 0x1323dfc1fc000000

def z1037 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x679fffff60000000 0x0cf3ffffec000000

def z1038 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff81fe1fc07f05 0xfdfff03fc3f80fe0

def z1039 : W := mkw 0x10202e0002538000 0x420405c0004a7000 0x1da6be0007398003 0x63b4d7c000e73000

def z1040 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xb400012e8001e49d 0x16800025d0003c93

def z1041 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xb980ff0fe0000000 0x17301fe1fc000000

def z1042 : W := mkw 0x0815000015805600 0x0102a00002b00ac0 0x67ff01c01fc07f05 0xecffe03803f80fe0

def z1043 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x193efe001f380000 0x4327dfc003e70000

def z1044 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0018003 0x3ff3fffffc003000

def z1045 : W := mkw 0x31352e003ef7812a 0x4626a5c007def025 0x14673e30ffff87ff 0xe28ce7c61ffff0ff

def z1046 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfffef9ef9f3ffcff 0xffffdf3df3e7ff9f

def z1047 : W := mkw 0x0a1711b495805614 0x2142e23692b00ac2 0x67ff01f09fc07f1d 0xecffe03e13f80fe3

def z1048 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0xffbffe31e739849f 0x7ff7ffc63ce73093

def z1049 : W := mkw 0x1f000a0237dbf7be 0x03e0014046fb7ef7 0x006000001fffffff 0xe00c000003ffffff

def z1050 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0xfec041ef8007fcff 0xbfd8083df000ff9f

def z1051 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xa9a6b90e0739e49f 0x7534d721c0e73c93

def z1052 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe7ff3fe7f9e79f 0xfffcffe7fcff3cf3

def z1053 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe30ffff8003 0xe3f7ffc61ffff000

def z1054 : W := mkw 0x110002002042812a 0x0220004004085025 0x9e814631e0c787fb 0xb3d028c63c18f0ff

def z1055 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x153fbe30fff98719 0x42a7f7c61fff30e3

def z1056 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x2000012e00006404 0x04000025c0000c80

def z1057 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x173ffe001fff8001 0xc2e7ffc003fff000

def z1058 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9800fe0fe00600e2 0x13001fc1fc00c01c

def z1059 : W := mkw 0xc01df4ddd4801200 0xd803be9bba900240 0xda59fedff8c01b00 0x9b4b3fdbff180360

def z1060 : W := mkw 0x110002002042812a 0x0220004004085025 0xf6414631e0c787fd 0x9ec828c63c18f0ff

def z1061 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6f92f873fe4ff 0x77b4df25f0e7fc9f

def z1062 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0xffbfffffffff8003 0xfff7fffffffff000

def z1063 : W := mkw 0xc01de4d940000000 0xd803bc9b28000000 0xff9fffdf60000000 0x1ff3fffbec000000

def z1064 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0x604001fe00007f04 0x0c08003fc0000fe0

def z1065 : W := mkw 0xc01df44dd4800000 0xd803be89ba900000 0x9fbffe0fffc00001 0xf3f7ffc1fff80000

def z1066 : W := mkw 0xe008f44dc8240840 0xdc011e89b9048108 0xda58fecff8061860 0x9b4b1fd9ff00c30c

def z1067 : W := mkw 0xc01ff56dc0000000 0xf803feadb8000000 0xbf9fff2fe0000000 0x17f3ffe5fc000000

def z1068 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x9c27fe3fe7c00701 0x1384ffc7fcf800e0

def z1069 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0007804 0x1ffbfffffc000f00

def z1070 : W := mkw 0x0000080002110000 0x0000010000422000 0x7ffeb9c01f39f807 0xefffd73803e73f00

def z1071 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xcb58c1cf183e78e2 0xd96b1839e307cf1c

def z1072 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x5ffffec01fff9803 0xebffffd803fff300

def z1073 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xffbfffffe7c00001 0x1ff7fffffcf80000

def z1074 : W := mkw 0x8f02116fa1086dfe 0x31e0422df4210dbf 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z1075 : W := mkw 0x0015000014800000 0x0002a00002900000 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1076 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0x1fbffe011fff8063 0xe3f7ffc023fff00c

def z1077 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x153fbe001f380000 0x42a7f7c003e70000

def z1078 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x07bfb8001f380000 0x40f7f70003e70000

def z1079 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff01f01fc07b00 0xccffe03e03f80f60

def z1080 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9c01fe3fe0000000 0x13803fc7fc000000

def z1081 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffbfffffe7000001 0x7ff7fffffce00000

def z1082 : W := mkw 0xce0211ffc1086cd4 0x39c0423ff8210d9a 0xe04001ffe0007cfc 0x1c08003ffc000f9f

def z1083 : W := mkw 0x0000080016910000 0x0000010002d22000 0x1da6b8001ff98003 0xe3b4d70003ff3000

def z1084 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x627901f01fc07f05 0xec4f203e03f80fe0

def z1085 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x163f7e001fff8003 0xe2c7efc003fff000

def z1086 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xffdffffff83e00e6 0xfffbffffff07c01c

def z1087 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfda6b93fe739e49f 0x7fb4d727fce73c93

def z1088 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x7ffffe317fff8767 0xefffffc62ffff0ec

def z1089 : W := mkw 0x1f000a02235be5be 0x03e00140446b7cb7 0x0020000007f9e79f 0x6004000000ff3cf3

def z1090 : W := mkw 0x203dec901eb51200 0xc407bd9203d6a240 0x437fb8d01ff81b00 0xc86ff71a03ff0360

def z1091 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63ff01d01fc07b04 0xec7fe03a03f80f60

def z1092 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fffb9f01fc07f05 0xeffff73e03f80fe0

def z1093 : W := mkw 0x481711b4d5805600 0x2902e2369ab00ac0 0x67ff01f0ffc07f05 0xecffe03e1ff80fe0

def z1094 : W := mkw 0x10000a0002538000 0x02000140004a7000 0x1da6b80007ff8003 0xe3b4d70000fff000

def z1095 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0c607e7 0xbffbfffffc18c0fc

def z1096 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x9fbffe01ffff8003 0xf3f7ffc03ffff000

def z1097 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xfbd8c7cff83e78e6 0xff7b18f9ff07cf1c

def z1098 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9d86fe0fe0000000 0x13b0dfc1fc000000

def z1099 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xe31fffffe0000000 0x1c63fffffc000000

def z1100 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbffe001f398003 0x63f7ffc003e73000

def z1101 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd9c1df18fe7be6 0xfd7b383be31fcf7c

def z1102 : W := mkw 0xe81ff5fddda45e40 0xfd03febfbbb48bc8 0xffffffffffc67f65 0xfffffffffff8cfec

def z1103 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xfac0fe0fe00600e6 0xbf581fc1fc00c01c

def z1104 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1da6b92e8739e41b 0x63b4d725d0e73c83

def z1105 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xefff01f01fc07f87 0xfdffe03e03f80ff0

def z1106 : W := mkw 0x110002002042812a 0x0220004004085025 0xffe74631e7c787ff 0xfffce8c63cf8f0ff

def z1107 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe31ffff80e7 0xffffffc63ffff01c

def z1108 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013eb8001ffe0000 0xc027d70003ffc000

def z1109 : W := mkw 0x0600180682192094 0x00c00300d0432412 0xbda6b90e8739e09f 0x77b4d721d0e73c13

def z1110 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffff007f04 0x5fffffffffe00fe0

def z1111 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b80007398087 0x77b4d70000e73010

def z1112 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0x9906ff0fe0000000 0x1320dfe1fc000000

def z1113 : W := mkw 0x0800000015805600 0x0100000002b00ac0 0x017801c01fc07f05 0xe02f003803f80fe0

def z1114 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa980812e8000649c 0x15301025d0000c93

def z1115 : W := mkw 0x303dee901ef79200 0xc607bdd203def240 0x7fffffd01ffffb07 0xeffffffa03ffff60

def z1116 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x467f00f01fc07f05 0xe8cfe01e03f80fe0

def z1117 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x571fffffe0000000 0x0ae3fffffc000000

def z1118 : W := mkw 0x0000080002110000 0x0000010000422000 0x1da6b80007380000 0x43b4d70000e70000

def z1119 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xff9fffffe0c00300 0x1ff3fffffc180060

def z1120 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0060060 0x9ffbfffffc00c00c

def z1121 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbfa6f92e873fe49f 0xf7f4df25d0e7fc93

def z1122 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfde6b92f8739e4ff 0x7fbcd725f0e73c9f

def z1123 : W := mkw 0xb13dee493ef7896a 0xd627bdc927def12d 0x5ffffed17fff9b63 0xebffffda2ffff36c

def z1124 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd9c7cf183e78e6 0xfffb38f9e307cf1c

def z1125 : W := mkw 0x10000a0002538000 0x02000140004a7000 0x1da7be0007f98003 0x63b4f7c000ff3000

def z1126 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0xa00001ee80007c9c 0x1400003dd0000f93

def z1127 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffe7000000 0x1ff7fffffce00000

def z1128 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe001fff871b 0xe3f7ffc003fff0e3

def z1129 : W := mkw 0x0000080002110000 0x0000010000422000 0xffa7fe31e7398003 0x7ff4ffc63ce73000

def z1130 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0xffffffcf1fff80e7 0xfffffff9e3fff01c

def z1131 : W := mkw 0x40023524c0000000 0x680046a498000000 0xbd86bf2ee0000000 0x17b0d7e5dc000000

def z1132 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0xff9effefe0000000 0x1ff3dffdfc000000

def z1133 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xfe87fe3fe0000000 0x1fd0ffc7fc000000

def z1134 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7fbfffc01fff8003 0xeff7fff803fff000

def z1135 : W := mkw 0x101dee0002538000 0xc203bdc0004a7000 0x1fbffe0007ff8003 0xe3f7ffc000fff000

def z1136 : W := mkw 0x0000080002110000 0x0000010000422000 0x1426380007398003 0x6284c70000e73000

def z1137 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x63f901d01fc07f05 0xec7f203a03f80fe0

def z1138 : W := mkw 0x11352e0036d3812a 0x4226a5c006da7025 0xffe7fe31e7ff87ff 0xfffcffc63cfff0ff

def z1139 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x013eb8001f380000 0x4027d70003e70000

def z1140 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xeb9fffdf60000000 0x1d73fffbec000000

def z1141 : W := mkw 0x801de44900000000 0xd003bc8920000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1142 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x193efe001fff8003 0xe327dfc003fff000

def z1143 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x7ffffe301fff87ff 0xefffffc603fff0ff

def z1144 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x0bbef8001fff8003 0xe177df0003fff000

def z1145 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x0126b90e0739e09a 0x4024d721c0e73c13

def z1146 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe25841cf183e78e6 0xfc4b0839e307cf1c

def z1147 : W := mkw 0x0600180682192094 0x00c00300d0432412 0x9926b80e8739809a 0x5324d701d0e73013

def z1148 : W := mkw 0x0000080002110000 0x0000010000422000 0x1fa6f800073f8003 0xe3f4df0000e7f000

def z1149 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xffdffffff8c07b04 0xfffbffffff180f60

def z1150 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x993effcfff007800 0x5327dff9ffe00f00

def z1151 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbca6b82e8739849f 0x3794d705d0e73093

def z1152 : W := mkw 0xc01ff5fdd4801200 0xf803febfba900240 0xffdffffff8c01f05 0xbffbffffff1803e0

def z1153 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0xda01fe1fe0000000 0x1b403fc3fc000000

def z1154 : W := mkw 0x110002002042812a 0x0220004004085025 0xfed946f1f8c79fff 0xbfdb28de3f18f3ff

def z1155 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffffc07b00 0xdffffffffff80f60

def z1156 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa000012e80006000 0x14000025d0000c00

def z1157 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xb526b92e8739e49d 0x56a4d725d0e73c93

def z1158 : W := mkw 0x0000080002110000 0x0000010000422000 0xbda6b82087398003 0x77b4d70410e73000

def z1159 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6ff2fe739e49f 0x77b4dfe5fce73c93

def z1160 : W := mkw 0x0600180682192094 0x00c00300d0432412 0x9c26b80e8739809b 0x1384d701d0e73013

def z1161 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x9fbffe009fff809b 0xf3f7ffc013fff013

def z1162 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9c26b82e8739e49f 0x7384d705d0e73c93

def z1163 : W := mkw 0x31200a003ef7812a 0x0624014007def025 0xbde6b8209fff87ff 0xf7bcd70413fff0ff

def z1164 : W := mkw 0x001dec0016910000 0xc003bd8002d22000 0x1fbffe001ff98003 0xe3f7ffc003ff3000

def z1165 : W := mkw 0xc01decd942110000 0xd803bd9b28422000 0x5fbffed167398003 0x6bf7ffda2ce73000

def z1166 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd87bf3ee0000000 0x17b0f7e7dc000000

def z1167 : W := mkw 0x110002002042812a 0x0220004004085025 0x9c414631e0c787ff 0xb38828c63c18f0ff

def z1168 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xeb98c1cf183e78e2 0x5d731839e307cf1c

def z1169 : W := mkw 0xa008c8490a350840 0x940119092146a108 0x5ffef8c11f3f9863 0xebffdf1823e7f30c

def z1170 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffa7b93e8739e49f 0x7ff4f727d0e73c93

def z1171 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x9d1fffffe0000000 0x13a3fffffc000000

def z1172 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x09beb8001f380002 0x6137d70003e70000

def z1173 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x017eb8001fff87ff 0xe02fd70003fff0ff

def z1174 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbc26b92e8739e49f 0x1784d725d0e73c93

def z1175 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0xfea14631e739e49f 0x7fd428c63ce73c93

def z1176 : W := mkw 0x0e0211b681086494 0x21c04236d0210c92 0xe00001fe8000649c 0x1c00003fd0000c93

def z1177 : W := mkw 0xc01ff5fdc0000840 0xf803febfb8000108 0xffdfffffe0001860 0x1ffbfffffc00030c

def z1178 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9ffffff8000000 0xfff3ffffff000000

def z1179 : W := mkw 0xe008f44dc8240000 0xdc011e89b9048000 0x9b98fe0ff83e0002 0xf3731fc1ff07c000

def z1180 : W := mkw 0x0015080016910000 0x0002a10002d22000 0x07bfb8001ff80001 0xe0f7f70003ff0000

def z1181 : W := mkw 0xa03dec491eb50840 0xd407bd8923d6a108 0x437ef8c11f3e1860 0xc86fdf1823e7c30c

def z1182 : W := mkw 0x0015089016911200 0x0002a11202d22240 0x5fffb8d01ff99b03 0xebfff71a03ff3360

def z1183 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0xffbffe31ff380000 0x5ff7ffc63fe70000

def z1184 : W := mkw 0x0000080002110000 0x0000010000422000 0x0126b80007398003 0x6024d70000e73000

def z1185 : W := mkw 0xce0211ffc1086494 0x39c0423ff8210c92 0xa00001ee8000649c 0x1400003dd0000c93

def z1186 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0c00300 0x9ffbfffffc180060

def z1187 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x07bfb8001fff8003 0xe0f7f70003fff000

def z1188 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x47ff01d01fc07b01 0xe8ffe03a03f80f60

def z1189 : W := mkw 0x0000080002110000 0x0000010000422000 0x9da6b8008739809b 0x73b4d70010e73013

def z1190 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0xa000013e8000679c 0x14000027d0000cf3

def z1191 : W := mkw 0x1f021326a14ae5be 0x23e04264d4295cb7 0xb800472fe007e4fe 0x170008e5fc00fc9f

def z1192 : W := mkw 0x303dee901ef79200 0xc607bdd203def240 0x1fbffe101fff8303 0xe3f7ffc203fff060

def z1193 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xff9ffffff8380000 0x5ff3ffffff070000

def z1194 : W := mkw 0x00352c0016910000 0x4006a58002d22000 0x1da6b80007398003 0x63b4d70000e73000

def z1195 : W := mkw 0x8e02116f81086494 0x31c0422df0210c92 0xe00001ef8000649c 0x1c00003df0000c93

def z1196 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0x1fbffe0007380000 0x43f7ffc000e70000

def z1197 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xffffffffffc07805 0xfffffffffff80f00

def z1198 : W := mkw 0x10150a0016d38000 0x0202a14002da7000 0x1fbffe001fff8003 0xe3f7ffc003fff000

def z1199 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xff87ff3fe0000000 0x1ff0ffe7fc000000

def z1200 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xfe81473fe000649c 0x1fd028e7fc000c93

def z1201 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0c00701 0x1ff3fffffc1800e0

def z1202 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x0fbff8001ffe0003 0xe1f7ff0003ffc000

def z1203 : W := mkw 0x11000a002253812a 0x02200140044a7025 0x1da7be30e7f9871b 0x63b4f7c61cff30e3

def z1204 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xff9fffffe0006404 0x1ff3fffffc000c80

def z1205 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xffffffffffc00705 0xfffffffffff800e0

def z1206 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffe011fff87ff 0xffffffc023fff0ff

def z1207 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe04001ee80007c9c 0x1c08003dd0000f93

def z1208 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xbd9fbffee0000000 0x17b3f7ffdc000000

def z1209 : W := mkw 0x110002002042812a 0x0220004004085025 0xfe814631e0c787fb 0x1fd028c63c18f0ff

def z1210 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1cf183ffcff 0xfd7b1839e307ff9f

def z1211 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x7fff47f01fc07f05 0xefffe8fe03f80fe0

def z1212 : W := mkw 0x2028ec000a350000 0xc4051d800146a000 0x0126b80007380000 0x4024d70000e70000

def z1213 : W := mkw 0x0e00180683196494 0x01c00300d0632c92 0x9da6b80e8739e49f 0x73b4d701d0e73c93

def z1214 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x63fe01c01fc07f05 0xec7fc03803f80fe0

def z1215 : W := mkw 0x40003404c0000000 0x4800068098000000 0x9800be0ee0000000 0x130017c1dc000000

def z1216 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z1217 : W := mkw 0x0e02112681087694 0x21c04224d0210ed2 0xa040012e80007f9c 0x14080025d0000ff3

def z1218 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x427900d01fc07b00 0xc84f201a03f80f60

def z1219 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7ffffff01fffff07 0xeffffffe03ffffe0

def z1220 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe0000004 0xbffbfffffc000000

def z1221 : W := mkw 0x3128ee002a77812a 0xc6251dc0054ef025 0xbda6fe21e73f84ff 0x77b4dfc43ce7f09f

def z1222 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0380002 0x7ff3fffffc070000

def z1223 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffffc01f01 0x9ffffffffff803e0

def z1224 : W := mkw 0xc00af56dc0000000 0xf8015eadb8000000 0x9c06fe2fe0000000 0x1380dfc5fc000000

def z1225 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xbd9effefe0000000 0x17b3dffdfc000000

def z1226 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xffbffe31ffff80fb 0xfff7ffc63ffff01f

def z1227 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67bf01f01fc07f01 0x4cf7e03e03f80fe0

def z1228 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xffdffffff80618e6 0xbffbffffff00c31c

def z1229 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x8000002e80000498 0x10000005d0000093

def z1230 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbfa7ff2e8739e49f 0x77f4ffe5d0e73c93

def z1231 : W := mkw 0x0f0211b6a10877be 0x21e04236d4210ef7 0xe04001ffe0007ffc 0x1c08003ffc000fff

def z1232 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0xffffffcf1fff9863 0xfffffff9e3fff30c

def z1233 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xdb1fffdfe0000000 0x1b63fffbfc000000

def z1234 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe107fff8303 0xe3f7ffc20ffff060

def z1235 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0x9801fe1fe0000000 0x13003fc3fc000000

def z1236 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbde6b92e873fe4ff 0xf7bcd725d0e7fc9f

def z1237 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0006004 0x7ff3fffffc000c00

def z1238 : W := mkw 0x3128ee002a77812a 0xc6251dc0054ef025 0xffe7fe31e7ff87ff 0xfffcffc63cfff0ff

def z1239 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffffb9fe9ff9ff9f 0xfffff73fd3ff3ff3

def z1240 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0000405 0x3ff3fffffc000080

def z1241 : W := mkw 0x401ff5b4c0000000 0xe803feb698000000 0xbf9fff3ee0000000 0x17f3ffe7dc000000

def z1242 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xffff47f1ffc67fe7 0xffffe8fe3ff8cffc

def z1243 : W := mkw 0x110002002042812a 0x0220004004085025 0xffd94631f8c787ff 0xfffb28c63f18f0ff

def z1244 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x17bfbe001ff98001 0xe2f7f7c003ff3000

def z1245 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1e3ffe001fff8003 0x83c7ffc003fff000

def z1246 : W := mkw 0x11352e0036d3812a 0x4226a5c006da7025 0xbda7be30e7f9879f 0x77b4f7c61cff30f3

def z1247 : W := mkw 0x1f170bb237dbf7be 0x23e2e17646fb7ef7 0x67ff01f01fffffff 0xecffe03e03ffffff

def z1248 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffdef9cf183e78e6 0xfffbdf39e307cf1c

def z1249 : W := mkw 0x8e02116f81086cd4 0x31c0422df0210d9a 0xa00001ee80007c9c 0x1400003dd0000f93

def z1250 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xe040013e8000679c 0x1c080027d0000cf3

def z1251 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa480012e8000649d 0x34900025d0000c93

def z1252 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x057f01f01fc07f05 0xe0afe03e03f80fe0

def z1253 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0xfb99ffdfe0000000 0x1f733ffbfc000000

def z1254 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda7b93e87f9e79f 0x77b4f727d0ff3cf3

def z1255 : W := mkw 0x11021324a042812a 0x2220426494085025 0xbdc6b92e80c787ff 0xb7b8d725d018f0ff

def z1256 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0xfe99feffe0000000 0x1fd33fdffc000000

def z1257 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffff007804 0xffffffffffe00f00

def z1258 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe001ff98001 0x43f7ffc003ff3000

def z1259 : W := mkw 0xc01ff5fdd4800000 0xf803febfba900000 0xff9ffffff8c00000 0x9ff3ffffff180000

def z1260 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xff9fffffe0000700 0x1ff3fffffc0000e0

def z1261 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xb800012e8001e49e 0x17000025d0003c93

def z1262 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x779fbffee0000000 0x0ef3f7ffdc000000

def z1263 : W := mkw 0xb13dee493ef7812a 0xd627bdc927def025 0xffffffffffff87ff 0xfffffffffffff0ff

def z1264 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x3fbffe201fff8407 0xe7f7ffc403fff080

def z1265 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1dbefe001f3f8003 0x63b7dfc003e7f000

def z1266 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xeffec1cf1f3e78e7 0xfdffd839e3e7cf1c

def z1267 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xfa19ffffe0000000 0x1f433ffffc000000

def z1268 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x142638001fff8003 0xe284c70003fff000

def z1269 : W := mkw 0xf13deed97ef7812a 0xde27bddb2fdef025 0x5ffffed17fff8363 0xebffffda2ffff06c

def z1270 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x5fbffe117fff8003 0xebf7ffc22ffff000

def z1271 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffff007c05 0x7ff7ffffffe00f80

def z1272 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x667f01f01fc07f05 0x8ccfe03e03f80fe0

def z1273 : W := mkw 0xb03dee491ef78000 0xd607bdc923def000 0x1fbfffce1fff8003 0xe3f7fff9c3fff000

def z1274 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe0007ff8003 0x03f7ffc000fff000

def z1275 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0xfffffec11fff98e7 0xffffffd823fff31c

def z1276 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0x1507bf3ee0000000 0x02a0f7e7dc000000

def z1277 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1ffffe001fff80e7 0xe3ffffc003fff01c

def z1278 : W := mkw 0x001711b480000000 0x2002e23690000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1279 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffe31ffff8363 0xffffffc63ffff06c

def z1280 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1fff83e78e6 0xfd7b183fff07cf1c

def z1281 : W := mkw 0xa03dec491eb50840 0xd407bd8923d6a108 0x013eb8c01f381800 0x4027d71803e70300

def z1282 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1427be0007f98001 0x0284f7c000ff3000

def z1283 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x153fbe001fff8003 0xe2a7f7c003fff000

def z1284 : W := mkw 0x30350a001ef78000 0x0606a14003def000 0x1fbfb8001fff8003 0xe3f7f70003fff000

def z1285 : W := mkw 0xca1ff5fdc1004414 0xf943febfb8200882 0xff9fffffe0000418 0x1ff3fffffc000083

def z1286 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0xfd87bfffe0000000 0x1fb0f7fffc000000

def z1287 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0xe7ff01f11fc07fe5 0xfcffe03e23f80ffc

def z1288 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffe7c07f05 0x1ffffffffcf80fe0

def z1289 : W := mkw 0x0000100480000000 0x0000020090000000 0xfe81fe3fe0000000 0x1fd03fc7fc000000

def z1290 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x0126b90e0739e419 0x4024d721c0e73c83

def z1291 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbde6b92e87f9e79f 0xf7bcd725d0ff3cf3

def z1292 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe7f93f87ffe7ff 0xfffcff27f0fffcff

def z1293 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1426b82e87398419 0x0284d705d0e73083

def z1294 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe001809a 0x1ff3fffffc003013

def z1295 : W := mkw 0x202008001eb50000 0x0404010003d6a000 0x1da6b8001f398003 0x63b4d70003e73000

def z1296 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0xebfef8011f3e00e6 0xfd7fdf0023e7c01c

def z1297 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda7bf3ee739e49f 0x77b4f7e7dce73c93

def z1298 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x77ff01f09fc1ff1d 0xeeffe03e13f83fe3

def z1299 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xffffffffe7007f05 0x7ffffffffce00fe0

def z1300 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe6b92e8739e49f 0xfffcd725d0e73c93

def z1301 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1d3ffe001fff8003 0x43a7ffc003fff000

def z1302 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0xfffffe117fff83e7 0xffffffc22ffff07c

def z1303 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0x67ff39f01fc07f05 0xecffe73e03f80fe0

def z1304 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x193eb8001f398002 0x4327d70003e73000

def z1305 : W := mkw 0xb13dee493ef7896a 0xd627bdc927def12d 0xfffffef1ffff9fff 0xffffffde3ffff3ff

def z1306 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1fbef8001f3f8003 0xe3f7df0003e7f000

def z1307 : W := mkw 0xc008f4ddc0000000 0xd8011e9bb8000000 0xd800fedfe0000000 0x1b001fdbfc000000

def z1308 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x14273e0007f98003 0x6284e7c000ff3000

def z1309 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffbfffffe7006000 0x5ff7fffffce00c00

def z1310 : W := mkw 0xf03deed95ef79200 0xde07bddb2bdef240 0x5ffffed17fff9b03 0xebffffda2ffff360

def z1311 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffbfffffe7000401 0x1ff7fffffce00080

def z1312 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x033ffe001f380000 0x4067ffc003e70000

def z1313 : W := mkw 0x4e0219b6c3196494 0x29c04336d8632c92 0xbda6b93ee739e49f 0x77b4d727dce73c93

def z1314 : W := mkw 0x0e00080203196494 0x01c0010040632c92 0xbda6b90e0739e49f 0x77b4d721c0e73c93

def z1315 : W := mkw 0x110002002042812a 0x0220004004085025 0xfc414631e0c787ff 0x1f8828c63c18f0ff

def z1316 : W := mkw 0x2008c8000a350000 0x840119000146a000 0x0bbef8001f3e0002 0xe177df0003e7c000

def z1317 : W := mkw 0x0600180682192094 0x00c00300d0432412 0xbda6b82e8739849f 0x77b4d705d0e73093

def z1318 : W := mkw 0xc81735fdd5805600 0x7902e6bfbab00ac0 0xf4673fffe7c07f05 0x1e8ce7fffcf80fe0

def z1319 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0060002 0xbff3fffffc00c000

def z1320 : W := mkw 0xce0211ffc1086494 0x39c0423ff8210c92 0xe00001ffe0006000 0x1c00003ffc000c00

def z1321 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x7ffffe30ffff871f 0xefffffc61ffff0e3

def z1322 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdffffff8c07f05 0xfffbffffff180fe0

def z1323 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xffff7ff1ffc07f05 0xffffeffe3ff80fe0

def z1324 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0x1dbeb80007398003 0x63b7d70000e73000

def z1325 : W := mkw 0x8008c84902110000 0x9001190920422000 0xffbef9cf07398003 0x7ff7df39e0e73000

def z1326 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x8b98c1cf183e78e2 0xf1731839e307cf1c

def z1327 : W := mkw 0xe01ff5fdc8240840 0xfc03febfb9048108 0xff9ffffff8001800 0x1ff3ffffff000300

def z1328 : W := mkw 0x401735b4c0000000 0x6802e6b698000000 0xff9fbffee0000000 0x1ff3f7ffdc000000

def z1329 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0x77ff39f09fc07f05 0xeeffe73e13f80fe0

def z1330 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xffe7ff3fe73fe4ff 0xfffcffe7fce7fc9f

def z1331 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xff9fffffe03e0002 0x1ff3fffffc07c000

def z1332 : W := mkw 0xa03dec491eb50000 0xd407bd8923d6a000 0xebbef9cf1f380000 0x5d77df39e3e70000

def z1333 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe000049c 0x1ff3fffffc000093

def z1334 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1fbffe017fff8063 0xe3f7ffc02ffff00c

def z1335 : W := mkw 0xc008f44dc0000000 0xd8011e89b8000000 0x9918ffcfe0000000 0x13231ff9fc000000

def z1336 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1ffffe30ffff87ff 0xe3ffffc61ffff0ff

def z1337 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xde1ffeffe0000000 0x1bc3ffdffc000000

def z1338 : W := mkw 0x0e0211b681087694 0x21c04236d0210ed2 0x000001ce00007800 0x00000039c0000f00

def z1339 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xefd9c1cf18fe78e7 0xfdfb3839e31fcf1c

def z1340 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1cf183e7860 0xdd7b1839e307cf0c

def z1341 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x0000010e0000649c 0x00000021c0000c93

def z1342 : W := mkw 0x0e0219b683197694 0x21c04336d0632ed2 0xbda6b93e8739e79f 0x77b4d727d0e73cf3

def z1343 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0xf79f3fffe0000000 0x1ef3e7fffc000000

def z1344 : W := mkw 0x0015080016910000 0x0002a10002d22000 0xffffb8309ff9879f 0xfffff70613ff30f3

def z1345 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x1407be3ee0000000 0x0280f7c7dc000000

def z1346 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0xfe81ffffe0000000 0x1fd03ffffc000000

def z1347 : W := mkw 0x00352c0016910000 0x4006a58002d22000 0x0126b80007380000 0x4024d70000e70000

def z1348 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x011fbfde60000000 0x0023f7fbcc000000

def z1349 : W := mkw 0x303dee000a778000 0xc607bdc0014ef000 0x1fbffe00073f8003 0x63f7ffc000e7f000

def z1350 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xff9fffffe0007800 0x1ff3fffffc000f00

def z1351 : W := mkw 0x0000080002110000 0x0000010000422000 0x3da6b9000739e007 0x67b4d72000e73c00

def z1352 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x7ffffe001fff8007 0xefffffc003fff000

def z1353 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x437fffdf7fc07b00 0xc86ffffbeff80f60

def z1354 : W := mkw 0x481735b4d5805600 0x6902e6b69ab00ac0 0xbda7bf3ee7c06705 0x77b4f7e7dcf80ce0

def z1355 : W := mkw 0xe03ff5fddca40000 0xfc07febfbb948000 0xff9ffffff8000000 0x1ff3ffffff000000

def z1356 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0x67ffffff7fc07f05 0xecffffffeff80fe0

def z1357 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x011effcf60000000 0x0023dff9ec000000

def z1358 : W := mkw 0x00152c0002110000 0x4002a58000422000 0x1da7be0007398003 0x63b4f7c000e73000

def z1359 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x0bbffe001ffe0002 0xe177ffc003ffc000

def z1360 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x437ffe117ffe0360 0xc86fffc22fffc06c

def z1361 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffdffffff8c07f04 0x9ffbffffff180fe0

def z1362 : W := mkw 0x201dec000a350000 0xc403bd800146a000 0x1fbffe001f3f8003 0xe3f7ffc003e7f000

def z1363 : W := mkw 0x0f021126a10865be 0x21e04224d4210cb7 0xa000012fe00064fc 0x14000025fc000c9f

def z1364 : W := mkw 0x001dec0002110000 0xc003bd8000422000 0x013eb80007380000 0x4027d70000e70000

def z1365 : W := mkw 0x111dee002253812a 0xc223bdc0044a7025 0xfffffe31e7ff87ff 0xffffffc63cfff0ff

def z1366 : W := mkw 0x0000080002110000 0x0000010000422000 0x1c26b80007398003 0x0384d70000e73000

def z1367 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0x4358c1cf183e78e6 0xe86b1839e307cf1c

def z1368 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1fa7fe0007ff8003 0xe3f4ffc000fff000

def z1369 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x5ffffe101fff8303 0xebffffc203fff060

def z1370 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xb926b92e8739e49e 0x5724d725d0e73c93

def z1371 : W := mkw 0x10200a0016d38000 0x0204014002da7000 0x1da6b80007f98003 0x63b4d70000ff3000

def z1372 : W := mkw 0x0815009015805600 0x0102a01202b00ac0 0x66f900f01fc07f05 0xecdf201e03f80fe0

def z1373 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xff9ffffff8060000 0x9ff3ffffff00c000

def z1374 : W := mkw 0xc81ff5fdc1005600 0xf903febfb8200ac0 0xffdffffff8007f04 0xfffbffffff000fe0

def z1375 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0x7fffffc11ffff867 0xeffffff823ffff0c

def z1376 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x637f01f01fc07f04 0xcc6fe03e03f80fe0

def z1377 : W := mkw 0x8e0ad16f81086494 0xb1c15a2df0210c92 0xeb98c1ef8000649c 0x1d73183df0000c93

def z1378 : W := mkw 0x110002002042812a 0x0220004004085025 0xde414631e0c787fb 0x9bc828c63c18f0ff

def z1379 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbffe301fff8703 0xe3f7ffc603fff0e0

def z1380 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x6fff41f01fc67f07 0xedffe83e03f8cfe0

def z1381 : W := mkw 0x0002112480000000 0x2000422490000000 0xbd86ff2fe0000000 0x17b0dfe5fc000000

def z1382 : W := mkw 0xb708da4faa7fa9fe 0x96e11b49f54ff53f 0x9800fe0fe03f80fa 0x13001fc1fc07f01f

def z1383 : W := mkw 0x11000a002253812a 0x02200140044a7025 0x9da6fe01e73f80fb 0x73b4dfc03ce7f01f

def z1384 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x9ffffe01ffff87ff 0xf3ffffc03ffff0ff

def z1385 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x9f9ffe3fe0000000 0x13f3ffc7fc000000

def z1386 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xfb9effcfe0000000 0x1f73dff9fc000000

def z1387 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0xfb98ffffe0000000 0x1f731ffffc000000

def z1388 : W := mkw 0x30200a001ef78000 0x0604014003def000 0x1fa7fe001fff8003 0xe3f4ffc003fff000

def z1389 : W := mkw 0x800ad16d80000000 0xb0015a2db0000000 0xff9fffffe0000000 0x1ff3fffffc000000

def z1390 : W := mkw 0xc01df4ddc0000000 0xd803be9bb8000000 0x4219fedf60000000 0x08433fdbec000000

def z1391 : W := mkw 0x10352e0016d38000 0x4206a5c002da7000 0x1fbfbe001ff98003 0xe3f7f7c003ff3000

def z1392 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1b3ffe001fff8002 0xc367ffc003fff000

def z1393 : W := mkw 0x110002002042812a 0x0220004004085025 0xffc1c631e0ff87ff 0xfff838c63c1ff0ff

def z1394 : W := mkw 0x35200a023effa9ea 0x06a4014047dff53d 0x006000001fffffff 0xe00c000003ffffff

def z1395 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xefd9c1ff183e78e6 0xfdfb383fe307cf1c

def z1396 : W := mkw 0x0000080002110000 0x0000010000422000 0x7fe7b83007f98707 0xeffcf70600ff30e0

def z1397 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x013eb8001f398003 0x6027d70003e73000

def z1398 : W := mkw 0x0400000200082080 0x0080000040010410 0xebd8c1cf183e78e6 0xfd7b1839e307cf1c

def z1399 : W := mkw 0xb03dee491ef78840 0xd607bdc923def108 0x1fbffec01fff9803 0xe3f7ffd803fff300

def z1400 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x017e01c01fc07b00 0xc02fc03803f80f60

def z1401 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x67ffb8301ff80705 0xecfff70603ff00e0

def z1402 : W := mkw 0x110002002042812a 0x0220004004085025 0xfec147f1e0c7ffff 0xbfd828fe3c18ffff

def z1403 : W := mkw 0x30352e001ef78000 0x4606a5c003def000 0x1ea77e001fff8003 0xe3d4efc003fff000

def z1404 : W := mkw 0x103dee0016d38000 0xc207bdc002da7000 0x1fbffe0007f98003 0x63f7ffc000ff3000

def z1405 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x9826b80e8739809a 0x1304d701d0e73013

def z1406 : W := mkw 0xc01735fdc0000000 0x7802e6bfb8000000 0x94073e3fe0000000 0x1280e7c7fc000000

def z1407 : W := mkw 0x0015080002110000 0x0002a10000422000 0x1fbfb80007398003 0x63f7f70000e73000

def z1408 : W := mkw 0x703dee905ef78000 0xce07bdd20bdef000 0x1fbffe107fff8003 0xe3f7ffc20ffff000

def z1409 : W := mkw 0x0e0219b683197694 0x21c04336d0632ed2 0xfffeb9fe9f39ff9f 0xffffd73fd3e73ff3

def z1410 : W := mkw 0xcf0211ffe10865be 0x39e0423ffc210cb7 0xe04001ffe00067fc 0x1c08003ffc000cff

def z1411 : W := mkw 0xc00235fdc0000000 0x780046bfb8000000 0xf0003fffe0000000 0x1e0007fffc000000

def z1412 : W := mkw 0x2008c8000a350000 0x840119000146a000 0x1dbeb8001f398003 0x63b7d70003e73000

def z1413 : W := mkw 0x0e0219b683196494 0x21c04336d0632c92 0xfda6b9fe8739e49f 0x7fb4d73fd0e73c93

def z1414 : W := mkw 0xc81ff5fdc1004400 0xf903febfb8200880 0xffffffffff007c05 0xffffffffffe00f80

def z1415 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffffffffe7c00705 0xbffffffffcf800e0

def z1416 : W := mkw 0x0e02112681086cd4 0x21c04224d0210d9a 0xa040012e80007cfc 0x14080025d0000f9f

def z1417 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1cf18fe7fe7 0xfd7b1839e31fcffc

def z1418 : W := mkw 0xc01df44dc0000000 0xd803be89b8000000 0x9a19fe0fe0000000 0x13433fc1fc000000

def z1419 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x5ffffe31ffff877b 0xebffffc63ffff0ef

def z1420 : W := mkw 0x1f021326a14ae5be 0x23e04264d4295cb7 0xe241473fe0c667fc 0x9c4828e7fc18ccff

def z1421 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xff9fffffe0c00001 0xbff3fffffc180000

def z1422 : W := mkw 0x313dee003ef7812a 0xc627bdc007def025 0x1ffffe001fff8363 0xe3ffffc003fff06c

def z1423 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x013f01d01fc07b00 0x4027e03a03f80f60

def z1424 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xfffffe311fff87e7 0xffffffc623fff0fc

def z1425 : W := mkw 0xe01ff5fdc8240000 0xfc03febfb9048000 0xffdffffff83e7806 0xfffbffffff07cf00

def z1426 : W := mkw 0x0802012001004400 0x2100402400200880 0x67ff01f01fc07f05 0xecffe03e03f80fe0

def z1427 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff41f11fc67f65 0xecffe83e23f8cfec

def z1428 : W := mkw 0xe01ff5fddca41a40 0xfc03febfbb948348 0xffdffffff8c61b60 0x9ffbffffff18c36c

def z1429 : W := mkw 0x17000a02225ba1be 0x02e00140444b7437 0x00000000003f80fa 0x000000000007f01f

def z1430 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1fbefe001f3f8003 0xe3f7dfc003e7f000

def z1431 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x013eb9c01f387800 0x4027d73803e70f00

def z1432 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013eb8001ff98001 0x4027d70003ff3000

def z1433 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xfde6b9ee8739fc9f 0x7fbcd73dd0e73f93

def z1434 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x013eb8001ff80001 0xe027d70003ff0000

def z1435 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1fbfffc01ffff803 0xe3f7fff803ffff00

def z1436 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbde6b92e9f39fc9f 0xf7bcd725d3e73f93

def z1437 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa180012e8000649c 0x74300025d0000c93

def z1438 : W := mkw 0x0f021126a10865be 0x21e04224d4210cb7 0xa000013ee000679c 0x14000027dc000cf3

def z1439 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x013efe001f3e0000 0x4027dfc003e7c000

def z1440 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x67ff47f17fc07f05 0xecffe8fe2ff80fe0

def z1441 : W := mkw 0x313dee903ef7932a 0xc627bdd207def265 0x5ffffed17fff9b63 0xebffffda2ffff36c

def z1442 : W := mkw 0x0e02192683197694 0x21c04324d0632ed2 0xbde6b92e8739ff9f 0x77bcd725d0e73ff3

def z1443 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1bbefe001f3f8002 0xe377dfc003e7f000

def z1444 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0x9806fe0fe0000000 0x1300dfc1fc000000

def z1445 : W := mkw 0x201dc8001eb50000 0x8403b90003d6a000 0x1fbff8001fff8003 0xe3f7ff0003fff000

def z1446 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x1dbeb8001f380000 0x43b7d70003e70000

def z1447 : W := mkw 0xc00af5fdc0000000 0xf8015ebfb8000000 0x9800fe3fe0000000 0x13001fc7fc000000

def z1448 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xffdfffffe00000e4 0x1ffbfffffc00001c

def z1449 : W := mkw 0x1f020b22235be5be 0x23e04164446b7cb7 0x67e7013007ffe7ff 0xecfce02600fffcff

def z1450 : W := mkw 0x010008002211012a 0x0020010004422025 0xfde6b831e73987ff 0x7fbcd7063ce730ff

def z1451 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0x000000208000649c 0x0000000410000c93

def z1452 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xe15881cf183e78e6 0xfc2b1039e307cf1c

def z1453 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffffc07801 0xfff7fffffff80f00

def z1454 : W := mkw 0x0e02112681086494 0x21c04224d0210c92 0xa880012e8000649e 0x35100025d0000c93

def z1455 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd8c1cf183ff8e7 0xfffb1839e307ff1c

def z1456 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x5ffffe011fff8063 0xebffffc023fff00c

def z1457 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0x1dbfbe001ff98003 0x63b7f7c003ff3000

def z1458 : W := mkw 0xdf0213ffe14ae5be 0x3be0427ffc295cb7 0xfec147ffe0c7e7ff 0xbfd828fffc18fcff

def z1459 : W := mkw 0xc81ff5fdd5805600 0xf903febfbab00ac0 0xffbfffffffc00701 0xfff7fffffff800e0

def z1460 : W := mkw 0xf03dee495ef78000 0xde07bdc92bdef000 0x1fbffe017fff8003 0xe3f7ffc02ffff000

def z1461 : W := mkw 0x081701b015805600 0x2102e03602b00ac0 0x617e01f01fc07f05 0xec2fc03e03f80fe0

def z1462 : W := mkw 0x303dee001ef78000 0xc607bdc003def000 0xbfbfff0e1fff8003 0xf7f7ffe1c3fff000

def z1463 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xffd9c7fff83ffcff 0xfffb38ffff07ff9f

def z1464 : W := mkw 0x4e0211b6c1086494 0x29c04236d8210c92 0xa000013ee000649c 0x14000027dc000c93

def z1465 : W := mkw 0x303dee001ef79200 0xc607bdc003def240 0x1ffffe001fff9b03 0xe3ffffc003fff360

def z1466 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0xbda6b92e8739e09a 0x57b4d725d0e73c13

def z1467 : W := mkw 0x081711b495805600 0x2102e23692b00ac0 0x67ffb9fe1fc07f05 0xecfff73fc3f80fe0

def z1468 : W := mkw 0x202008001eb50000 0x0404010003d6a000 0x0126b8001f380000 0x4024d70003e70000

def z1469 : W := mkw 0xc01ff5fdc0000000 0xf803febfb8000000 0xf51fbfffe0000000 0x1ea3f7fffc000000

def z1470 : W := mkw 0xf03deed95ef78000 0xde07bddb2bdef000 0xffbffef1ffff8003 0xfff7ffde3ffff000

def z1471 : W := mkw 0x3028ee000a778000 0xc6051dc0014ef000 0x1c26fe00073f8003 0x0384dfc000e7f000

def z1472 : W := mkw 0x0e02192683196494 0x21c04324d0632c92 0x1526b92e8739e49f 0x62a4d725d0e73c93

def z1473 : W := mkw 0x303dee901ef79200 0xc607bdd203def240 0x7ffffef01fff9f07 0xefffffde03fff3e0

def z1474 : W := mkw 0xa408c04b082c28c0 0x9481180961058518 0xebd8c1ff183e7fe6 0xfd7b183fe307cffc

def z1475 : W := mkw 0x203dec001eb50000 0xc407bd8003d6a000 0x033ef8001f3e0000 0xc067df0003e7c000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z7,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z6])],[(0,[z0,z9,z2,z3,z4,z5,z6]),(0,[z10,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z11]),(0,[z0,z2,z12,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z14,z5,z6])],[(0,[z15,z0,z2,z3,z4,z5,z6]),(0,[z16,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z17,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z18]),(0,[z0,z2,z3,z4,z19,z20,z6])],[(0,[z0,z2,z3,z14,z13,z5,z6])],[(0,[z0,z2,z3,z4,z21,z5,z6]),(0,[z0,z22,z2,z3,z13,z5,z6])],[(0,[z23,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z3,z25,z5,z6]),(0,[z26,z0,z2,z4,z5,z6,z27])],[(0,[z0,z2,z28,z3,z4,z5,z29])],[(0,[z30,z0,z22,z2,z3,z5,z6]),(0,[z31,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z32,z5,z6])],[(0,[z33,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z34,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z6,z27]),(0,[z0,z2,z3,z4,z36,z5,z6]),(0,[z0,z2,z3,z37,z4,z5,z6])],[],[(1,[z0,z2,z3,z4,z5,z38]),(1,[z0,z9,z2,z3,z5,z6]),(0,[z39,z40,z2,z3,z4,z5,z6])],[(0,[z41,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z42,z3,z4,z5,z6]),(1,[z0,z43,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z44])],[(0,[z0,z2,z3,z45,z4,z5,z6]),(0,[z0,z2,z46,z3,z4,z5,z6]),(1,[z47,z0,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z49,z6])],[(0,[z0,z2,z3,z50,z4,z5,z29])],[(0,[z0,z2,z3,z4,z5,z51,z6]),(1,[z0,z2,z52,z4,z5,z53])]],
   [[],[(0,[z0,z2,z54,z3,z4,z55,z6])],[(1,[z0,z2,z3,z35,z5,z56]),(0,[z0,z57,z2,z12,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z58]),(0,[z0,z2,z3,z59,z5,z60,z6]),(0,[z0,z2,z3,z61,z5,z62,z6])],[(0,[z0,z2,z3,z13,z5,z63,z6])],[(0,[z0,z2,z3,z64,z13,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z29]),(0,[z65,z0,z2,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z67,z5,z6]),(0,[z0,z2,z3,z4,z68,z5,z6])],[(0,[z69,z2,z3,z4,z70,z5,z6])],[(0,[z71,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z72,z3,z4,z20,z6])],[(0,[z0,z2,z3,z4,z5,z6,z73]),(0,[z0,z2,z3,z74,z4,z5,z6])],[(0,[z75,z0,z22,z2,z3,z5,z6]),(0,[z65,z66,z0,z2,z3,z5,z6]),(1,[z0,z2,z76,z3,z5,z6]),(0,[z77,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z78]),(0,[z79,z0,z2,z3,z4,z5,z6])],[],[(0,[z40,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z13,z5,z6,z56]),(0,[z0,z22,z2,z3,z5,z29,z6]),(0,[z0,z80,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z81,z5,z6])],[(0,[z0,z2,z3,z82,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z63,z6]),(0,[z0,z83,z2,z3,z4,z5,z6]),(1,[z0,z22,z3,z84,z5,z6]),(0,[z0,z85,z2,z3,z4,z5,z6]),(1,[z86,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z72,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z87]),(0,[z0,z2,z3,z4,z70,z5,z53]),(0,[z88,z0,z2,z3,z4,z5,z6])],[(0,[z47,z0,z2,z3,z4,z5,z29]),(0,[z77,z66,z0,z2,z3,z5,z6]),(0,[z89,z0,z2,z3,z5,z6,z90])],[(1,[z0,z2,z3,z91,z5,z6]),(0,[z26,z0,z43,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z92,z6,z93])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z94]),(0,[z95,z0,z2,z3,z4,z70,z5]),(1,[z0,z2,z3,z5,z62,z6])],[(0,[z30,z0,z2,z3,z96,z5,z6]),(0,[z0,z2,z3,z4,z97,z5,z29]),(0,[z66,z0,z2,z3,z5,z6,z93]),(0,[z0,z2,z3,z98,z5,z92,z6])],[(0,[z0,z99,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z53,z100])],[(1,[z40,z2,z3,z101,z5,z6]),(1,[z0,z2,z3,z13,z5,z56]),(0,[z0,z2,z3,z4,z102,z5,z6])],[(0,[z103,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z104,z3,z4,z5,z6]),(0,[z33,z0,z2,z3,z5,z6,z93])],[],[(0,[z39,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z105,z4,z5,z6]),(0,[z0,z2,z3,z106,z4,z5,z6]),(0,[z0,z2,z3,z107,z4,z5,z6]),(0,[z108,z0,z2,z3,z4,z5,z6])],[(0,[z109,z0,z57,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z29,z6,z56]),(0,[z110,z0,z2,z3,z13,z5,z6])],[(0,[z0,z57,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z112,z4,z5,z6]),(0,[z0,z2,z113,z3,z4,z5,z56]),(0,[z114,z0,z2,z3,z4,z5,z29]),(0,[z77,z0,z2,z3,z13,z5,z6])],[(0,[z109,z115,z0,z3,z4,z5,z6]),(0,[z116,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z91,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z117,z6])],[(0,[z0,z2,z3,z118,z4,z5,z6])],[(0,[z0,z2,z3,z4,z119,z5,z6]),(0,[z0,z2,z3,z4,z5,z60,z6])],[(0,[z0,z120,z3,z4,z5,z60,z6]),(0,[z121,z0,z2,z3,z35,z5,z6])],[(0,[z0,z2,z3,z4,z5,z122,z56]),(0,[z0,z2,z3,z4,z5,z123,z6])]],
   [[(0,[z66,z0,z2,z3,z5,z124,z6]),(0,[z0,z2,z3,z35,z5,z6,z100]),(0,[z0,z2,z3,z35,z5,z6,z93]),(1,[z0,z2,z3,z125,z5,z6])],[(0,[z0,z2,z3,z4,z126,z5,z56]),(0,[z0,z2,z54,z3,z126,z5,z6]),(0,[z0,z2,z3,z98,z4,z5,z56])],[(0,[z0,z2,z3,z4,z5,z56,z127]),(0,[z0,z2,z3,z4,z5,z128,z56])],[(0,[z129,z0,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z113,z3,z5,z6]),(0,[z0,z2,z3,z13,z5,z122,z6])],[(0,[z0,z2,z111,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z61,z5,z56]),(0,[z0,z2,z130,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z90,z27])],[(0,[z131,z114,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z132,z4,z5,z6])],[(0,[z0,z3,z4,z19,z5,z48,z6])],[(0,[z131,z0,z2,z3,z4,z5,z29])],[(0,[z133,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z134,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z29]),(0,[z135,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z50,z5,z124,z6])],[(0,[z0,z2,z136,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z119,z5,z6]),(0,[z0,z22,z2,z3,z5,z60,z6]),(0,[z0,z2,z3,z4,z137,z5,z6]),(0,[z138,z0,z2,z3,z4,z5,z6])],[(0,[z131,z0,z2,z3,z139,z5,z6]),(0,[z0,z2,z3,z4,z140,z5,z6]),(0,[z0,z2,z141,z3,z4,z5,z6]),(1,[z0,z2,z3,z142,z5,z6]),(0,[z95,z0,z2,z3,z4,z5,z60]),(0,[z0,z2,z3,z4,z143,z5,z6])],[(0,[z66,z0,z2,z3,z4,z5,z56]),(1,[z0,z2,z3,z4,z144,z6]),(0,[z0,z2,z3,z4,z5,z145,z6]),(0,[z95,z0,z2,z3,z35,z5,z6])],[(0,[z39,z0,z2,z3,z126,z5,z6]),(0,[z146,z0,z2,z3,z4,z5,z6]),(0,[z0,z147,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z84,z5,z6])],[(0,[z0,z2,z28,z3,z4,z5,z56]),(0,[z148,z0,z2,z149,z4,z5,z6]),(1,[z114,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z6,z150])],[(0,[z109,z0,z2,z3,z35,z5,z6]),(0,[z151,z0,z22,z2,z3,z5,z6]),(0,[z121,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z100,z93])]],
   [[(0,[z33,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z70,z5,z29]),(0,[z0,z2,z3,z4,z5,z6,z152]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z154,z4,z5,z6])],[(0,[z0,z2,z3,z155,z4,z5,z56])],[(0,[z0,z2,z3,z4,z156,z5,z6]),(0,[z148,z114,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z157,z5,z6])],[(0,[z66,z115,z0,z2,z3,z5,z6]),(0,[z109,z0,z3,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z29,z158]),(0,[z0,z2,z4,z20,z5,z122,z6])],[(0,[z0,z2,z3,z4,z159,z5,z6]),(0,[z0,z2,z3,z4,z160,z5,z6])],[(0,[z2,z3,z64,z4,z5,z6,z56]),(0,[z148,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z50,z4,z5,z56]),(0,[z161,z0,z2,z3,z4,z5,z6]),(0,[z0,z85,z57,z3,z4,z5,z6]),(0,[z0,z22,z2,z52,z3,z5,z6]),(1,[z0,z2,z3,z162,z5,z6])],[(0,[z0,z2,z3,z4,z5,z163,z6]),(0,[z114,z2,z3,z4,z164,z5,z6]),(0,[z0,z2,z3,z165,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z70,z6])],[(0,[z166,z0,z57,z2,z3,z5,z6]),(1,[z0,z22,z2,z3,z5,z6])],[(0,[z66,z0,z2,z3,z25,z5,z6])],[(0,[z0,z167,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z168,z4,z5,z6]),(0,[z0,z2,z3,z4,z169,z5,z6]),(0,[z0,z2,z3,z4,z5,z170,z6])],[(0,[z71,z0,z2,z3,z171,z5,z6])],[(0,[z172,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z56]),(0,[z0,z2,z3,z4,z173,z5,z6])],[(0,[z115,z0,z22,z2,z3,z5,z6]),(0,[z66,z39,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z35,z5,z6,z174])],[(0,[z0,z2,z3,z4,z5,z29,z60]),(0,[z0,z2,z3,z4,z5,z6,z158]),(0,[z66,z0,z2,z54,z3,z5,z6]),(0,[z95,z0,z2,z3,z13,z5,z6]),(0,[z95,z0,z2,z3,z4,z5,z100])],[(1,[z0,z2,z3,z4,z175,z6])],[(0,[z176,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z177,z3,z5,z6])]],
   [[(0,[z109,z0,z2,z3,z13,z5,z6]),(1,[z0,z2,z3,z178,z5,z6]),(0,[z0,z2,z3,z4,z5,z29,z6]),(0,[z0,z2,z3,z98,z4,z5,z179])],[(0,[z30,z0,z2,z3,z4,z163,z6]),(0,[z40,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z180,z5,z6])],[(0,[z0,z2,z3,z4,z5,z63,z56]),(1,[z2,z3,z4,z164,z5,z56]),(0,[z181,z0,z2,z3,z4,z5,z6]),(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z183,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z184,z5,z56]),(0,[z185,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z28,z3,z186,z5,z6]),(1,[z187,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z188,z5,z6]),(0,[z47,z0,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z5,z48,z6]),(0,[z0,z2,z3,z4,z189,z5,z6]),(0,[z0,z2,z3,z4,z190,z5,z6])],[(0,[z0,z2,z3,z4,z5,z191,z6]),(0,[z0,z2,z12,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z192,z29]),(0,[z0,z2,z3,z4,z5,z193,z6]),(0,[z95,z194,z2,z3,z4,z5,z6]),(1,[z69,z2,z3,z4,z5,z6])],[(1,[z0,z2,z195,z4,z5,z6]),(0,[z0,z2,z3,z13,z196,z5,z6])],[(0,[z30,z0,z2,z3,z4,z140,z6]),(0,[z47,z0,z2,z3,z4,z19,z6]),(0,[z0,z2,z3,z4,z5,z60,z27])],[(0,[z0,z2,z3,z4,z197,z5,z6])],[(0,[z131,z2,z3,z4,z5,z6,z56]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z22,z2,z3,z4,z5,z29]),(0,[z66,z0,z2,z2,z3,z5,z6]),(0,[z26,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z48,z122,z6]),(0,[z0,z2,z3,z4,z198,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z199])],[(1,[z151,z2,z3,z4,z164,z6]),(0,[z0,z85,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z200,z4,z5,z6]),(0,[z0,z2,z3,z4,z201,z5,z6])],[],[(0,[z0,z2,z3,z202,z4,z5,z6]),(0,[z0,z2,z52,z3,z35,z5,z6])],[(0,[z0,z2,z149,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z29]),(0,[z0,z2,z3,z4,z5,z29,z100])]],
   [[(1,[z0,z2,z3,z96,z5,z6]),(0,[z148,z2,z3,z4,z5,z63,z6]),(0,[z0,z85,z3,z25,z4,z5,z6]),(1,[z0,z2,z3,z34,z5,z6]),(0,[z0,z2,z52,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z203,z5,z6])],[(1,[z0,z204,z3,z4,z5,z6]),(0,[z0,z205,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z206]),(0,[z95,z0,z3,z4,z5,z6,z90]),(0,[z0,z2,z3,z4,z207,z5,z6]),(0,[z0,z2,z3,z4,z208,z5,z6])],[(1,[z0,z2,z113,z13,z5,z6]),(0,[z0,z2,z3,z4,z70,z61,z5])],[(0,[z0,z2,z3,z209,z4,z5,z6]),(0,[z0,z57,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z48,z6]),(0,[z210,z0,z2,z3,z4,z5,z6]),(0,[z211,z0,z2,z3,z4,z5,z6]),(0,[z212,z0,z2,z3,z4,z5,z6])],[(0,[z66,z151,z0,z2,z3,z5,z6]),(0,[z66,z0,z2,z3,z164,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z213]),(0,[z214,z0,z2,z3,z4,z5,z6])],[(0,[z215,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z0,z2,z216,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z217]),(0,[z0,z2,z3,z35,z67,z5,z6]),(0,[z0,z2,z3,z4,z218,z5,z6])],[(0,[z148,z2,z3,z4,z5,z6,z56]),(0,[z219,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z220])],[(0,[z0,z2,z3,z4,z5,z6,z221]),(0,[z0,z2,z3,z4,z222,z5,z6]),(0,[z223,z0,z2,z3,z35,z5,z6])],[(0,[z114,z2,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z64,z4,z5,z29]),(0,[z148,z0,z2,z3,z4,z63,z6]),(0,[z0,z2,z3,z4,z224,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z100])],[(1,[z0,z2,z3,z225,z5,z6]),(0,[z226,z0,z2,z3,z4,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z227,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z29]),(1,[z0,z2,z3,z228,z5,z6]),(0,[z103,z66,z0,z2,z3,z5,z6]),(0,[z219,z66,z0,z2,z3,z5,z6]),(1,[z0,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z4,z229,z5,z6]),(0,[z0,z2,z3,z4,z230,z5,z6])],[(0,[z0,z2,z3,z4,z5,z56,z90])],[(0,[z0,z85,z2,z3,z13,z5,z6])],[(0,[z223,z66,z0,z2,z3,z5,z6]),(0,[z231,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z232,z6]),(1,[z0,z2,z3,z4,z5,z78]),(0,[z233,z0,z2,z3,z4,z5,z6]),(0,[z33,z0,z2,z3,z4,z5,z124])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z131,z0,z2,z3,z4,z5,z56]),(1,[z234,z0,z2,z3,z4,z5]),(0,[z0,z22,z2,z3,z5,z6,z206]),(0,[z0,z2,z3,z4,z55,z5,z6])]],
   [[(0,[z235,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z236,z3,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z237,z6])],[(0,[z30,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z67,z4,z70])],[(0,[z0,z2,z3,z238,z4,z5,z6]),(0,[z0,z2,z72,z3,z4,z5,z29]),(0,[z0,z57,z2,z25,z4,z5,z6]),(0,[z231,z66,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z239,z6])],[(0,[z0,z2,z3,z4,z5,z6,z240]),(0,[z0,z2,z3,z241,z4,z5,z6]),(0,[z0,z2,z3,z50,z4,z5,z124])],[(0,[z0,z2,z3,z35,z164,z5,z6]),(0,[z0,z2,z3,z4,z5,z92,z6])],[],[(0,[z234,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z5,z6,z100]),(0,[z0,z22,z2,z3,z5,z6,z93])],[(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z243,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z5,z56]),(0,[z0,z2,z3,z4,z5,z244,z6])],[(0,[z245,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z246,z4,z5,z6]),(1,[z0,z2,z3,z5,z6,z247])],[(0,[z133,z2,z111,z3,z4,z5,z6]),(0,[z223,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z106,z13,z5,z6])],[(0,[z115,z0,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z248,z4,z5,z6]),(0,[z249,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z29,z27]),(0,[z0,z2,z3,z13,z70,z5,z6])],[(0,[z0,z2,z250,z3,z4,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z56]),(0,[z0,z22,z2,z3,z55,z5,z6])],[(0,[z0,z2,z3,z25,z4,z5,z29])],[(0,[z77,z0,z2,z3,z4,z5,z29]),(0,[z251,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z252,z35,z5,z6])],[(0,[z0,z2,z3,z4,z5,z253,z6]),(0,[z0,z22,z2,z3,z5,z239,z6])]],
   [[(0,[z0,z2,z3,z252,z4,z5,z6]),(0,[z0,z2,z3,z4,z254,z5,z6]),(0,[z0,z2,z3,z4,z5,z255,z6])],[(0,[z2,z3,z64,z4,z5,z63,z6]),(0,[z75,z0,z2,z3,z4,z5,z6]),(0,[z71,z256,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z5,z92,z6]),(0,[z223,z0,z257,z3,z4,z5,z6])],[(0,[z0,z57,z12,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z20,z5,z6]),(1,[z66,z0,z3,z119,z5,z6]),(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z259]),(0,[z0,z2,z3,z35,z5,z124,z6])],[(0,[z0,z2,z3,z4,z260,z5,z6]),(1,[z0,z2,z3,z261,z5,z6]),(0,[z0,z2,z3,z4,z5,z262,z6]),(1,[z263,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z84,z5,z6])],[(0,[z66,z0,z57,z2,z3,z5,z6])],[(0,[z66,z0,z2,z3,z126,z5,z6]),(0,[z0,z85,z3,z4,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z264,z6]),(1,[z0,z2,z3,z265,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z27])],[(0,[z0,z2,z266,z3,z4,z5,z6]),(0,[z66,z0,z2,z267,z3,z5,z6])],[(0,[z268,z0,z2,z3,z4,z5,z6])],[(0,[z39,z0,z2,z3,z101,z5,z6]),(0,[z0,z57,z3,z4,z5,z6,z90]),(0,[z66,z0,z2,z3,z61,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z270,z3,z4,z5,z6]),(1,[z223,z0,z2,z4,z122,z6])],[(0,[z66,z131,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z271,z5,z6])],[(0,[z131,z115,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z272,z6]),(0,[z71,z0,z2,z3,z273,z5,z6]),(0,[z274,z0,z2,z3,z4,z5,z6]),(1,[z275,z0,z2,z3,z5,z6]),(0,[z0,z2,z52,z3,z4,z5,z27]),(0,[z276,z0,z2,z3,z4,z5,z6])],[(0,[z277,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z278,z3,z4,z5,z6]),(0,[z0,z2,z12,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z279,z6])],[(0,[z0,z2,z3,z4,z280,z5,z6]),(0,[z0,z2,z281,z3,z4,z5,z6])],[(1,[z0,z2,z24,z3,z5,z6]),(0,[z282,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z283,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z5,z284,z29]),(0,[z285,z0,z2,z3,z4,z5,z6])],[(0,[z30,z0,z2,z28,z4,z5,z6]),(0,[z0,z22,z2,z3,z4,z5,z56])],[(0,[z0,z22,z2,z3,z5,z6,z27]),(0,[z0,z2,z3,z4,z5,z286,z6])],[(0,[z0,z2,z3,z84,z4,z5,z6]),(0,[z0,z2,z3,z4,z287,z5,z6]),(0,[z0,z2,z3,z4,z288,z5,z6])],[(0,[z121,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z289,z6])],[(0,[z0,z2,z290,z3,z4,z5,z6]),(0,[z0,z2,z3,z291,z4,z5,z56]),(0,[z0,z85,z2,z3,z4,z48,z6]),(0,[z292,z0,z2,z3,z4,z5,z6]),(0,[z223,z0,z2,z3,z68,z5,z6]),(0,[z293,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z101,z4,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z56]),(0,[z0,z2,z294,z3,z4,z5,z6]),(0,[z0,z2,z3,z295,z4,z5,z6]),(0,[z0,z2,z3,z4,z296,z5,z6]),(0,[z0,z297,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z140,z6]),(0,[z133,z2,z3,z4,z5,z63,z6]),(0,[z0,z2,z3,z13,z5,z6,z90])],[(0,[z95,z298,z2,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z265,z5,z6])],[],[(0,[z0,z2,z3,z13,z19,z5,z6]),(0,[z0,z2,z299,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z186,z5,z6]),(0,[z300,z0,z2,z3,z4,z5,z6])],[(0,[z301,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z302]),(0,[z303,z0,z2,z3,z4,z5,z6]),(0,[z0,z3,z25,z4,z5,z48,z6]),(0,[z0,z2,z3,z304,z4,z5,z6]),(0,[z0,z2,z3,z98,z4,z55,z6])],[(0,[z133,z2,z3,z4,z5,z6,z56]),(0,[z305,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z306,z3,z4,z5,z6]),(1,[z0,z2,z3,z98,z92,z6])],[(0,[z0,z2,z3,z4,z13,z5,z29]),(0,[z307,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z64,z4,z5,z56]),(0,[z308,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z309])],[(0,[z71,z0,z2,z3,z4,z5,z56]),(0,[z95,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z29,z93]),(0,[z0,z2,z3,z19,z5,z170,z6])],[(0,[z0,z2,z3,z4,z5,z6,z310]),(0,[z0,z2,z3,z4,z5,z311,z56]),(0,[z114,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z19,z122,z6]),(0,[z0,z2,z3,z312,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z70,z5])],[(1,[z0,z313,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z314,z5,z6])],[(1,[z0,z2,z3,z4,z5,z315]),(0,[z109,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z316,z3,z4,z5,z6]),(0,[z0,z57,z2,z3,z35,z5,z6]),(0,[z211,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z5,z124,z6,z93])],[(0,[z0,z2,z317,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z5,z63,z6]),(0,[z0,z2,z3,z4,z5,z318,z6])],[(0,[z30,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z319]),(0,[z0,z2,z3,z320,z4,z5,z6]),(0,[z0,z2,z54,z3,z98,z5,z6]),(0,[z0,z2,z3,z4,z321,z5,z6])],[(0,[z151,z0,z2,z3,z4,z5,z6]),(0,[z69,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z72,z3,z4,z5,z56])],[(0,[z0,z2,z322,z3,z4,z5,z6]),(0,[z0,z2,z323,z3,z4,z5,z6])],[(0,[z0,z2,z324,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z325,z5,z6]),(0,[z0,z2,z52,z4,z5,z53,z6])],[(0,[z0,z2,z3,z326,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z327]),(0,[z0,z22,z2,z3,z67,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z93])],[(0,[z0,z2,z3,z4,z328,z5,z6]),(0,[z66,z0,z2,z3,z5,z6,z56])],[(0,[z30,z0,z2,z64,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z329,z56]),(0,[z0,z2,z3,z4,z5,z53,z56]),(0,[z0,z330,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z139,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z331,z6]),(1,[z0,z2,z3,z4,z203,z5])]],
   [[(0,[z66,z109,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z273,z5,z6])],[(0,[z66,z0,z2,z111,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z60,z53])],[(0,[z30,z0,z2,z3,z35,z5,z6]),(0,[z332,z0,z2,z3,z4,z5,z6]),(0,[z66,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z52,z3,z13,z5,z6]),(0,[z0,z2,z3,z13,z5,z53,z6])],[(0,[z133,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z333,z3,z4,z5,z6])],[(0,[z0,z2,z3,z25,z4,z5,z56]),(0,[z0,z2,z3,z4,z334,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z335]),(0,[z336,z0,z2,z3,z4,z5,z6]),(0,[z0,z205,z2,z3,z13,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z337,z5,z6]),(0,[z77,z0,z2,z3,z4,z5,z56]),(0,[z0,z22,z3,z84,z4,z5,z6]),(0,[z0,z2,z3,z4,z338,z5,z6]),(0,[z223,z0,z2,z3,z4,z20,z6])],[(0,[z339,z0,z2,z111,z3,z5,z6]),(0,[z0,z57,z2,z3,z13,z5,z6]),(0,[z33,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z72,z3,z4,z122,z6]),(0,[z0,z2,z340,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z50,z5,z6])],[(1,[z0,z341,z3,z4,z5,z6]),(0,[z0,z2,z3,z342,z4,z5,z6]),(0,[z343,z0,z2,z3,z4,z5,z6])],[(1,[z2,z111,z3,z4,z5,z56]),(0,[z30,z66,z0,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z325,z5,z6])],[(1,[z0,z2,z3,z4,z5,z94]),(0,[z0,z2,z3,z344,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z0,z346,z2,z3,z4,z5,z6])],[(0,[z148,z151,z2,z3,z4,z5,z6]),(0,[z347,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z348]),(0,[z0,z2,z3,z4,z5,z124,z6]),(0,[z0,z2,z3,z4,z5,z6,z349])],[(0,[z0,z2,z3,z35,z5,z6,z56])],[],[(0,[z0,z350,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z351])],[(0,[z0,z2,z54,z3,z101,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z352,z6]),(0,[z353,z0,z2,z3,z4,z5,z6]),(0,[z0,z354,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z67,z4,z5,z6])],[(0,[z75,z0,z2,z3,z35,z5,z6]),(0,[z0,z85,z2,z3,z4,z5,z29]),(0,[z235,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z27,z100]),(0,[z0,z2,z355,z3,z4,z5,z6])],[(0,[z30,z0,z2,z3,z13,z5,z6]),(1,[z133,z2,z28,z4,z5,z6]),(0,[z66,z0,z2,z12,z3,z5,z6]),(0,[z47,z0,z85,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z356,z5,z6])],[(0,[z66,z40,z0,z2,z3,z5,z6])],[(0,[z0,z2,z76,z3,z19,z5,z6]),(1,[z0,z2,z3,z4,z5,z357])],[(0,[z133,z2,z28,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z5,z122,z6]),(0,[z47,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z358,z4,z5,z6])],[(0,[z0,z2,z64,z4,z5,z122,z6]),(0,[z0,z2,z3,z359,z4,z5,z6]),(0,[z360,z0,z2,z3,z4,z5,z6]),(0,[z223,z0,z361,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z362]),(0,[z0,z2,z54,z3,z4,z5,z6])],[(0,[z0,z22,z2,z3,z5,z124,z6]),(0,[z0,z2,z3,z4,z5,z6,z174])],[(0,[z0,z2,z3,z363,z4,z5,z6]),(0,[z0,z298,z2,z3,z4,z5,z6])],[(0,[z364,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z365,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z366,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z34,z5,z6]),(0,[z360,z66,z0,z2,z3,z5,z6]),(0,[z47,z0,z22,z2,z3,z5,z6]),(0,[z0,z22,z2,z113,z3,z5,z6]),(0,[z367,z0,z2,z3,z4,z5,z6]),(0,[z275,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z368,z4,z5,z6])],[(0,[z0,z2,z3,z369,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z60,z6]),(0,[z0,z2,z3,z370,z4,z5,z6])],[(0,[z0,z2,z177,z3,z4,z5,z6]),(1,[z0,z2,z3,z241,z5,z6])],[(0,[z371,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z372,z6]),(0,[z0,z2,z3,z4,z5,z29,z373]),(0,[z0,z2,z3,z105,z4,z5,z29]),(1,[z0,z205,z2,z3,z5,z6]),(0,[z374,z0,z2,z3,z4,z5,z6]),(0,[z0,z375,z2,z3,z4,z5,z6])],[(0,[z0,z376,z22,z2,z3,z5,z6]),(0,[z377,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z29,z378]),(0,[z26,z95,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z379,z6])],[(0,[z39,z0,z2,z3,z35,z5,z6])],[(0,[z380,z0,z2,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z11]),(0,[z374,z66,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z381,z6]),(0,[z0,z2,z3,z4,z382,z5,z6])],[(0,[z39,z0,z2,z3,z4,z5,z6]),(0,[z75,z0,z2,z3,z13,z5,z6])],[(0,[z0,z383,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z384,z4,z5,z6]),(0,[z0,z2,z3,z4,z119,z5,z29]),(0,[z0,z2,z3,z4,z5,z29,z53]),(0,[z0,z2,z3,z4,z5,z6,z385]),(0,[z0,z2,z3,z35,z20,z5,z6]),(0,[z0,z2,z386,z3,z4,z5,z6])],[(0,[z0,z2,z387,z3,z4,z5,z6]),(0,[z388,z0,z2,z3,z4,z5,z6]),(0,[z389,z0,z2,z3,z4,z5,z6]),(0,[z114,z2,z3,z64,z4,z5,z6]),(0,[z0,z2,z3,z390,z4,z5,z6]),(0,[z0,z2,z3,z4,z391,z5,z6]),(0,[z392,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z122,z6]),(0,[z0,z2,z3,z4,z393,z5,z6]),(0,[z0,z2,z54,z3,z4,z92,z6])],[(0,[z0,z2,z3,z4,z394,z5,z6])],[(0,[z0,z2,z3,z35,z126,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z395]),(0,[z0,z2,z3,z295,z35,z5,z6]),(1,[z0,z2,z3,z396,z5,z6])],[(0,[z0,z2,z3,z397,z4,z5,z6]),(0,[z0,z2,z398,z3,z4,z5,z6]),(0,[z399,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z24,z3,z4,z5,z6])],[(0,[z66,z0,z2,z3,z64,z5,z6]),(0,[z0,z2,z3,z13,z13,z5,z6]),(0,[z0,z2,z3,z35,z61,z5,z6])],[(0,[z400,z0,z22,z2,z3,z5,z6]),(0,[z401,z0,z2,z3,z4,z5,z6])],[(0,[z0,z111,z3,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z402])],[(0,[z40,z0,z2,z3,z126,z5,z6]),(1,[z148,z2,z3,z4,z63,z6]),(1,[z0,z85,z3,z4,z19,z6]),(0,[z0,z2,z3,z4,z5,z6,z403]),(0,[z404,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z405,z4,z5,z6]),(0,[z0,z2,z3,z55,z5,z92,z6])],[(0,[z0,z2,z3,z4,z406,z5,z6]),(0,[z407,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z408,z4,z5,z6])]],
   [[(0,[z66,z0,z111,z3,z4,z5,z6]),(0,[z66,z75,z0,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z25,z5,z6]),(0,[z66,z0,z2,z72,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z409,z4,z5,z6])],[(0,[z0,z410,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z411])],[],[(0,[z131,z109,z0,z3,z4,z5,z6])],[(0,[z131,z2,z3,z64,z4,z5,z6]),(0,[z0,z2,z52,z3,z4,z5,z53])],[(0,[z109,z2,z111,z3,z4,z5,z6]),(0,[z131,z0,z22,z2,z3,z5,z6]),(0,[z0,z22,z2,z54,z3,z5,z6]),(0,[z0,z2,z3,z84,z13,z5,z6]),(0,[z26,z0,z120,z2,z3,z4,z5])],[(1,[z0,z2,z3,z4,z5,z412]),(0,[z0,z120,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z413,z5,z6])],[(1,[z0,z414,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z415]),(0,[z0,z2,z3,z13,z21,z5,z6]),(0,[z0,z2,z3,z416,z35,z5,z6]),(0,[z0,z2,z3,z4,z417,z5,z6])],[(0,[z0,z2,z3,z101,z13,z5,z6]),(0,[z66,z0,z2,z3,z418,z5,z6]),(0,[z0,z2,z3,z4,z5,z419,z6]),(0,[z0,z2,z3,z4,z70,z5,z124]),(0,[z0,z2,z3,z4,z420,z5,z6])],[(0,[z0,z2,z3,z195,z4,z5,z6]),(0,[z151,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z416,z4,z5,z6]),(0,[z0,z2,z3,z421,z4,z5,z6])],[(0,[z422,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z35,z13,z5,z6])],[(0,[z423,z0,z2,z3,z4,z5,z6]),(0,[z424,z0,z2,z3,z4,z5,z6])],[(0,[z0,z361,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z425,z5,z6])],[(0,[z0,z22,z2,z3,z5,z48,z6]),(0,[z0,z120,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z426,z4,z5,z6])],[(0,[z2,z111,z3,z4,z5,z6,z56]),(1,[z0,z22,z2,z3,z5,z29]),(0,[z0,z2,z3,z4,z5,z6,z427])],[(0,[z0,z2,z3,z13,z5,z29,z6])]],
   [[(0,[z428,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z164,z5,z6]),(1,[z148,z2,z3,z4,z5,z56])],[(0,[z133,z151,z2,z3,z4,z5,z6]),(0,[z0,z2,z429,z3,z4,z5,z6]),(1,[z0,z2,z3,z35,z5,z6])],[(0,[z66,z0,z2,z28,z3,z5,z6]),(0,[z148,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z430,z4,z5,z6]),(0,[z0,z22,z2,z2,z3,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z381])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z431])],[],[(0,[z0,z2,z3,z4,z5,z6,z432]),(0,[z187,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z164,z6])],[(0,[z115,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z76,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z329]),(0,[z0,z2,z3,z4,z5,z29,z29]),(1,[z66,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z433,z4,z5,z6]),(0,[z0,z2,z72,z3,z91,z5,z6])],[(0,[z0,z2,z3,z35,z5,z63,z6])],[(0,[z0,z2,z3,z4,z5,z56,z27]),(0,[z434,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z435,z5,z6])],[(0,[z0,z436,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z13,z5,z6]),(0,[z66,z47,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z437,z4,z5,z6])],[(0,[z66,z0,z2,z3,z98,z5,z6]),(0,[z438,z0,z22,z2,z3,z5,z6])],[(0,[z0,z85,z2,z3,z4,z19,z6])],[(0,[z439,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z164,z5,z6])],[],[(0,[z440,z0,z2,z3,z4,z5,z56])]],
   [[(0,[z441,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z221])],[(0,[z442,z0,z2,z3,z4,z5,z6]),(0,[z148,z0,z2,z195,z4,z5,z6]),(1,[z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z443])],[(0,[z0,z2,z3,z4,z178,z5,z6])],[],[(0,[z234,z0,z2,z3,z25,z4,z5]),(0,[z0,z444,z2,z3,z4,z5,z6])],[(0,[z0,z445,z2,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z6])],[(0,[z115,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z52,z3,z4,z5,z29]),(0,[z0,z2,z446,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z447,z6]),(0,[z0,z2,z3,z4,z5,z6,z58]),(0,[z0,z2,z54,z3,z35,z5,z6]),(0,[z0,z2,z3,z125,z61,z5,z6])],[(0,[z0,z448,z2,z3,z4,z5,z6]),(1,[z0,z2,z72,z4,z20,z6]),(0,[z0,z2,z449,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z450,z5,z6]),(0,[z40,z0,z22,z2,z3,z5,z6]),(0,[z26,z66,z0,z2,z3,z5,z6]),(0,[z66,z0,z2,z3,z50,z5,z6]),(0,[z451,z0,z2,z3,z4,z5,z6]),(1,[z0,z257,z3,z4,z5,z6])],[(0,[z452,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z453]),(0,[z0,z2,z3,z4,z5,z60,z56]),(0,[z0,z57,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z144,z5,z6])],[(0,[z454,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z240]),(0,[z0,z2,z3,z67,z4,z20,z6])],[(0,[z148,z0,z204,z3,z4,z5,z6]),(1,[z0,z2,z3,z82,z5,z6]),(0,[z0,z2,z455,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z5,z6]),(0,[z0,z2,z3,z4,z5,z124,z100])],[(0,[z66,z0,z2,z3,z70,z5,z6]),(0,[z33,z0,z2,z3,z50,z5,z6])],[(1,[z0,z2,z3,z4,z5,z456]),(0,[z0,z2,z3,z13,z119,z5,z6]),(0,[z0,z2,z3,z225,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z126,z5,z6]),(0,[z457,z0,z2,z3,z4,z5,z6])],[(0,[z458,z0,z2,z3,z4,z5,z6]),(0,[z459,z0,z2,z3,z4,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z460,z3,z4,z5,z6])],[(1,[z131,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z461,z6]),(0,[z0,z2,z3,z462,z4,z5,z6])],[(0,[z131,z0,z111,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z463,z5,z6]),(0,[z0,z2,z3,z67,z13,z5,z6]),(0,[z0,z2,z3,z13,z5,z92,z6]),(0,[z223,z464,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z67,z4,z5,z100])],[(0,[z0,z2,z3,z4,z465,z5,z6]),(0,[z0,z2,z3,z4,z466,z5,z6]),(0,[z0,z2,z3,z467,z4,z5,z6]),(0,[z0,z2,z468,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z469,z6]),(0,[z0,z2,z3,z4,z5,z6,z470]),(0,[z371,z66,z0,z2,z3,z5,z6])],[(0,[z0,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z55,z5,z29]),(0,[z0,z2,z3,z4,z471,z5,z6]),(0,[z0,z2,z3,z4,z5,z472,z6]),(0,[z0,z2,z3,z4,z5,z6,z473]),(0,[z0,z474,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z62,z6])],[(0,[z0,z2,z3,z171,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z475,z6]),(0,[z30,z0,z2,z3,z4,z5,z29]),(0,[z71,z0,z22,z2,z3,z5,z6])],[(0,[z151,z0,z2,z3,z4,z5,z469]),(0,[z0,z2,z3,z4,z13,z5,z56]),(0,[z114,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z54,z3,z13,z5,z6]),(0,[z0,z2,z3,z35,z50,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z476]),(0,[z0,z2,z3,z4,z477,z5,z6])],[(0,[z0,z2,z3,z4,z5,z478,z6]),(0,[z0,z2,z3,z4,z479,z5,z6]),(0,[z0,z22,z2,z3,z20,z5,z6]),(0,[z2,z3,z4,z70,z425,z5,z6])],[(0,[z0,z2,z3,z4,z480,z5,z6]),(0,[z0,z2,z3,z4,z5,z92,z29]),(0,[z0,z2,z3,z4,z5,z6,z373]),(0,[z66,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z481,z6])],[(0,[z95,z0,z2,z3,z4,z5,z56]),(0,[z0,z22,z57,z2,z3,z5,z6]),(0,[z482,z0,z2,z3,z4,z5,z6])],[(0,[z483,z0,z2,z3,z4,z5,z6]),(1,[z39,z2,z3,z126,z5,z6]),(0,[z0,z22,z2,z3,z126,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z378]),(0,[z275,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z368,z13,z5,z6]),(0,[z0,z2,z3,z35,z70,z5,z6])],[(0,[z243,z0,z2,z3,z4,z5,z29]),(1,[z0,z2,z3,z484,z4,z5]),(0,[z0,z2,z3,z35,z5,z485,z6]),(1,[z0,z2,z3,z68,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z486,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z175,z6]),(0,[z166,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z487,z5,z6])]],
   [[(0,[z339,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z56,z93]),(0,[z0,z2,z3,z4,z5,z56,z100]),(0,[z0,z22,z2,z3,z61,z5,z6]),(0,[z0,z2,z52,z3,z218,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z488])],[(0,[z0,z489,z2,z3,z4,z5,z6]),(0,[z490,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z491,z4,z5,z6]),(0,[z0,z2,z3,z101,z5,z92,z6]),(0,[z166,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z492,z4,z5,z6]),(0,[z0,z2,z3,z35,z493,z5,z6])],[(0,[z0,z2,z3,z4,z5,z453,z6]),(0,[z263,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z494,z4,z5,z6]),(0,[z66,z0,z2,z3,z5,z6,z495]),(0,[z496,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z497,z3,z4,z5,z6])],[(0,[z498,z0,z2,z3,z4,z5,z6]),(1,[z2,z3,z64,z4,z5,z56]),(0,[z499,z0,z2,z3,z4,z5,z6])],[(0,[z39,z0,z2,z3,z4,z5,z327]),(0,[z39,z0,z2,z3,z13,z5,z6]),(0,[z75,z114,z2,z3,z4,z5,z6]),(1,[z0,z22,z2,z3,z5,z56]),(0,[z166,z66,z0,z2,z3,z5,z6]),(0,[z66,z33,z0,z2,z3,z5,z6]),(1,[z89,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z500,z6])],[(0,[z30,z0,z489,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z160,z5,z6])],[],[(0,[z75,z0,z2,z3,z4,z5,z29]),(0,[z0,z22,z2,z3,z5,z481,z6]),(1,[z0,z2,z3,z4,z477,z6])],[(0,[z133,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z501,z6]),(0,[z502,z0,z2,z3,z4,z5,z6])],[(0,[z66,z0,z2,z3,z5,z6,z90]),(0,[z0,z22,z2,z3,z225,z5,z6]),(0,[z251,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z59,z5,z6])],[(1,[z0,z2,z3,z4,z5,z453]),(0,[z2,z3,z4,z164,z5,z63,z6]),(0,[z77,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z503,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z504])],[(0,[z0,z2,z28,z4,z5,z122,z6]),(0,[z0,z256,z2,z3,z4,z5,z6]),(1,[z0,z2,z54,z3,z55,z6])],[(0,[z66,z0,z2,z3,z19,z5,z6])],[(0,[z148,z0,z2,z3,z261,z5,z6]),(0,[z0,z2,z3,z4,z5,z29,z56]),(0,[z0,z2,z3,z67,z4,z61,z6])],[(0,[z0,z22,z2,z3,z64,z5,z6]),(0,[z0,z2,z3,z505,z4,z5,z6])]],
   [[],[(0,[z0,z2,z3,z4,z5,z63,z6]),(0,[z0,z2,z506,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z142,z5,z6]),(0,[z0,z2,z3,z4,z507,z5,z6]),(0,[z508,z0,z2,z3,z4,z5,z6]),(1,[z0,z509,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z27]),(0,[z0,z2,z3,z4,z5,z6,z510])],[(0,[z2,z3,z4,z164,z5,z6,z56]),(0,[z0,z2,z3,z511,z4,z5,z6]),(0,[z512,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z513,z5,z6])],[],[(0,[z0,z2,z3,z4,z514,z5,z6]),(0,[z515,z0,z2,z3,z4,z5,z6])],[(0,[z2,z111,z3,z64,z4,z5,z6]),(1,[z30,z2,z64,z4,z5,z6])],[(0,[z30,z0,z2,z3,z4,z5,z402]),(0,[z0,z2,z3,z4,z5,z6,z395])],[(0,[z40,z0,z341,z3,z4,z5,z6]),(0,[z0,z516,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z517,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z56]),(0,[z0,z376,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z518,z5,z6]),(0,[z0,z2,z3,z4,z265,z5,z6]),(1,[z26,z0,z2,z4,z5,z27])],[(0,[z0,z2,z3,z4,z5,z6,z519])],[(0,[z0,z2,z3,z84,z4,z5,z29]),(0,[z0,z2,z12,z3,z142,z5,z6]),(0,[z520,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z162,z5,z6]),(0,[z521,z0,z2,z3,z4,z5,z6])],[(0,[z522,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z310]),(0,[z0,z85,z2,z3,z4,z5,z56]),(0,[z223,z0,z2,z3,z421,z5,z6])],[(0,[z0,z2,z523,z3,z4,z5,z6]),(0,[z0,z2,z3,z101,z4,z5,z29]),(1,[z346,z2,z3,z4,z5,z6])],[(0,[z0,z22,z2,z3,z5,z63,z6]),(0,[z0,z2,z52,z3,z4,z5,z56])],[]],
   [[(0,[z0,z2,z3,z4,z5,z524,z6])],[(0,[z0,z2,z3,z4,z5,z525,z6])],[(0,[z0,z57,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z526,z6])],[(0,[z131,z0,z2,z3,z4,z5,z315]),(0,[z109,z0,z3,z84,z4,z5,z6]),(0,[z301,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z527,z6])],[(0,[z0,z2,z3,z4,z102,z5,z56]),(0,[z0,z2,z3,z4,z5,z6,z528]),(0,[z26,z0,z509,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z327]),(0,[z0,z2,z3,z4,z529,z5,z6]),(0,[z0,z22,z2,z3,z5,z6,z56]),(0,[z66,z0,z2,z3,z5,z53,z6])],[(0,[z530,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z531,z4,z5,z6])],[(0,[z532,z0,z2,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z5,z533,z6]),(0,[z0,z2,z534,z3,z4,z5,z6]),(0,[z26,z0,z2,z3,z35,z5,z6])],[(0,[z223,z0,z2,z3,z4,z5,z56]),(0,[z535,z0,z22,z2,z3,z5,z6]),(0,[z0,z536,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z537,z4,z5,z6])],[(0,[z0,z22,z2,z111,z3,z5,z6]),(0,[z0,z2,z3,z538,z4,z5,z6]),(0,[z539,z0,z2,z3,z4,z5,z6])],[(0,[z109,z0,z85,z3,z4,z5,z6]),(0,[z0,z22,z22,z2,z3,z5,z6])],[(0,[z30,z0,z227,z3,z4,z5,z6]),(0,[z540,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z6,z100]),(0,[z0,z2,z3,z13,z5,z6,z93]),(0,[z451,z0,z2,z3,z35,z5,z6])],[(0,[z541,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z542])],[(0,[z109,z0,z3,z4,z5,z48,z6]),(0,[z0,z2,z3,z4,z63,z122,z6]),(0,[z0,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z55,z5,z56]),(1,[z298,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z543,z4,z5,z6])],[(1,[z0,z2,z3,z159,z5,z6]),(0,[z0,z2,z3,z4,z119,z5,z56]),(0,[z0,z2,z544,z3,z4,z5,z6]),(1,[z194,z2,z3,z4,z5,z6]),(0,[z121,z0,z2,z113,z4,z5,z6])],[(0,[z151,z0,z2,z3,z4,z5,z29]),(1,[z33,z0,z2,z3,z5,z93])]],
   [[(0,[z30,z0,z2,z3,z4,z5,z475]),(0,[z71,z0,z2,z3,z4,z144,z6]),(1,[z0,z361,z3,z4,z5,z6]),(0,[z26,z346,z2,z3,z4,z5,z6])],[(0,[z545,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z55,z5,z6]),(0,[z0,z2,z3,z4,z5,z122,z6])],[(0,[z0,z2,z3,z4,z5,z412,z6]),(0,[z0,z2,z3,z4,z5,z92,z56]),(0,[z0,z2,z546,z3,z4,z5,z6])],[(1,[z0,z2,z3,z5,z170,z6]),(0,[z0,z2,z72,z4,z20,z5,z6]),(0,[z0,z2,z3,z4,z20,z6,z100]),(0,[z0,z2,z3,z98,z4,z5,z6])],[(0,[z0,z2,z111,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z328,z5,z29]),(0,[z71,z263,z2,z3,z4,z5,z6])],[(0,[z547,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z341,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z56,z411]),(0,[z129,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z548,z3,z4,z5,z6]),(0,[z549,z0,z22,z2,z3,z5,z6]),(0,[z223,z0,z2,z3,z4,z122,z6])],[(0,[z0,z2,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z550,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z551]),(0,[z0,z2,z3,z4,z61,z5,z6])],[(0,[z131,z0,z2,z3,z4,z5,z94]),(0,[z0,z2,z3,z4,z5,z6,z179]),(0,[z0,z552,z2,z3,z4,z5,z6])],[(1,[z71,z0,z25,z4,z5,z6]),(0,[z26,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z553,z6])],[(0,[z0,z2,z554,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z61,z6,z100])],[(0,[z133,z0,z2,z3,z4,z5,z348]),(0,[z0,z2,z3,z4,z20,z164,z6])],[(0,[z0,z2,z3,z555,z4,z5,z6]),(0,[z556,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z12,z3,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z29]),(0,[z66,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z557,z3,z4,z5,z6]),(0,[z0,z2,z558,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z29,z559])],[(0,[z560,z0,z2,z3,z4,z5,z6]),(1,[z166,z0,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z122,z6])],[]],
   [[(0,[z0,z2,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z561,z4,z5,z6])],[(0,[z0,z2,z3,z4,z562,z5,z6]),(0,[z0,z2,z3,z4,z563,z5,z6]),(0,[z0,z2,z3,z98,z4,z92,z6]),(0,[z0,z2,z3,z4,z564,z5,z6])],[(1,[z0,z2,z3,z4,z5,z565]),(0,[z0,z2,z3,z4,z5,z124,z29]),(0,[z66,z66,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z566,z5,z6]),(0,[z33,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z567,z6]),(0,[z0,z2,z3,z155,z4,z5,z6]),(0,[z114,z2,z3,z4,z5,z29,z6]),(0,[z66,z0,z85,z2,z3,z5,z6])],[(1,[z0,z2,z3,z4,z5,z469]),(0,[z0,z2,z3,z484,z4,z5,z6]),(0,[z0,z2,z3,z4,z122,z6,z100])],[(1,[z0,z489,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z101,z5,z6]),(0,[z0,z2,z3,z4,z61,z5,z100])],[(0,[z0,z2,z3,z4,z568,z5,z6]),(0,[z0,z2,z35,z4,z13,z5,z6]),(0,[z569,z0,z2,z3,z4,z5,z6]),(0,[z570,z0,z2,z3,z4,z5,z6])],[(0,[z571,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z559]),(0,[z0,z2,z3,z13,z5,z6,z27]),(0,[z0,z2,z3,z13,z5,z264,z6]),(0,[z0,z2,z3,z50,z4,z5,z6])],[(0,[z572,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z573,z6]),(1,[z75,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z67,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z6,z11]),(0,[z0,z2,z3,z4,z5,z574,z6]),(0,[z0,z2,z3,z35,z304,z5,z6]),(0,[z0,z2,z3,z98,z4,z5,z357])],[(0,[z575,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z576,z3,z4,z5,z6]),(0,[z0,z577,z2,z3,z4,z5,z6])],[(0,[z0,z2,z12,z3,z228,z5,z6]),(0,[z0,z350,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z241,z5,z48,z6])],[(0,[z40,z0,z2,z3,z101,z5,z6]),(0,[z0,z2,z267,z3,z4,z5,z6])],[(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z151,z2,z3,z4,z164,z5,z6]),(0,[z0,z2,z3,z35,z538,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z579])],[(0,[z66,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z35,z4,z5,z6])],[(0,[z580,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z4,z5,z29]),(0,[z0,z2,z3,z359,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z53,z90]),(0,[z0,z2,z3,z4,z5,z6,z247])],[(1,[z115,z111,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z61,z100])]],
   [[(1,[z0,z2,z3,z218,z5,z6]),(1,[z2,z3,z4,z425,z5,z6])],[(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z2,z3,z84,z4,z5,z56]),(0,[z0,z2,z455,z3,z4,z5,z29]),(0,[z0,z2,z582,z3,z4,z5,z6]),(0,[z464,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z583,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z38]),(0,[z71,z0,z2,z12,z4,z5,z6]),(0,[z0,z3,z25,z4,z5,z6,z90]),(1,[z121,z0,z2,z35,z5,z6]),(0,[z508,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z584]),(0,[z0,z2,z3,z585,z4,z5,z6])],[(0,[z40,z0,z2,z3,z4,z5,z6]),(0,[z66,z0,z22,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z418,z5,z6])],[(0,[z39,z2,z3,z4,z126,z5,z6]),(0,[z0,z2,z3,z101,z4,z5,z56]),(0,[z194,z0,z2,z3,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z70,z5])],[(1,[z0,z2,z3,z4,z5,z402]),(0,[z0,z2,z3,z4,z586,z5,z6]),(0,[z0,z2,z3,z587,z4,z5,z6])],[(0,[z0,z2,z3,z4,z184,z5,z6]),(0,[z0,z2,z3,z50,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z588])],[(0,[z589,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z590]),(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z591,z3,z4,z5,z6])],[(0,[z151,z0,z2,z3,z4,z5,z415]),(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z72,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z593])],[(0,[z0,z2,z3,z4,z261,z5,z6]),(1,[z0,z2,z3,z171,z5,z6]),(1,[z0,z2,z3,z505,z5,z6])],[(0,[z39,z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z97,z5,z6])],[(1,[z0,z2,z3,z4,z5,z381])],[(0,[z66,z592,z0,z2,z3,z5,z6]),(0,[z95,z0,z120,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z6,z90])],[(0,[z522,z0,z2,z3,z35,z5,z6])],[(0,[z26,z0,z2,z3,z4,z477,z6])],[(0,[z66,z133,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z35,z19,z5,z6]),(0,[z0,z2,z3,z4,z5,z594,z6])]],
   [[(0,[z0,z2,z3,z4,z595,z5,z6]),(1,[z0,z2,z3,z4,z5,z415]),(0,[z0,z2,z3,z596,z4,z5,z6])],[(0,[z597,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z126,z5,z92,z6])],[(0,[z114,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z598,z4,z5,z6])],[(0,[z0,z2,z3,z96,z4,z5,z6]),(0,[z66,z95,z0,z2,z3,z5,z6]),(0,[z0,z3,z84,z4,z119,z5,z6])],[(0,[z131,z133,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z599,z5,z6]),(0,[z600,z0,z2,z3,z4,z5,z6]),(0,[z121,z0,z22,z2,z3,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z0,z2,z3,z601,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z602,z6])],[(0,[z603,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z5,z56]),(0,[z0,z120,z2,z52,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z48,z29]),(0,[z400,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z48,z6])],[(0,[z0,z2,z3,z4,z5,z565,z6]),(0,[z0,z205,z57,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z604,z5,z6])],[],[(0,[z0,z22,z2,z28,z3,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z53]),(0,[z0,z2,z54,z3,z5,z6,z93])],[(0,[z0,z2,z3,z4,z5,z605,z6]),(0,[z0,z2,z3,z59,z4,z5,z6])],[(0,[z606,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z113,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z232,z6]),(0,[z26,z0,z2,z3,z505,z5,z6])],[(0,[z0,z2,z3,z607,z4,z5,z6]),(0,[z75,z2,z3,z4,z5,z6,z56]),(0,[z0,z2,z3,z4,z5,z6,z608]),(0,[z0,z3,z4,z5,z60,z6,z90]),(0,[z609,z0,z2,z3,z4,z5,z6])],[(0,[z610,z0,z2,z3,z4,z5,z6])],[(0,[z131,z0,z2,z3,z35,z5,z6]),(0,[z2,z28,z3,z64,z4,z5,z6]),(0,[z611,z0,z2,z3,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z60]),(0,[z0,z313,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z612,z3,z4,z5,z6]),(0,[z0,z2,z3,z599,z4,z5,z6]),(0,[z0,z12,z3,z25,z4,z5,z6]),(0,[z0,z2,z3,z162,z5,z48,z6]),(0,[z0,z2,z3,z4,z5,z613,z6]),(0,[z0,z2,z54,z3,z55,z5,z6])],[(0,[z131,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z2,z3,z4,z5,z6]),(1,[z66,z0,z111,z3,z5,z6]),(0,[z0,z2,z3,z4,z614,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z412])],[(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z30,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z348,z6]),(0,[z0,z2,z615,z3,z4,z5,z6]),(0,[z148,z0,z414,z3,z4,z5,z6]),(0,[z95,z0,z22,z2,z3,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z6]),(0,[z223,z86,z2,z3,z4,z5,z6]),(1,[z616,z2,z3,z4,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z56]),(1,[z0,z2,z149,z4,z5,z6]),(0,[z0,z617,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z98,z5,z6]),(0,[z618,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z619,z5,z6]),(0,[z0,z2,z3,z4,z5,z620,z6]),(0,[z0,z2,z323,z3,z25,z5,z6]),(0,[z0,z2,z3,z98,z35,z5,z6])],[(0,[z109,z0,z22,z2,z3,z5,z6])],[(0,[z66,z121,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z357,z6])],[(0,[z0,z9,z2,z111,z3,z5,z6]),(0,[z0,z2,z3,z4,z164,z5,z29]),(0,[z0,z2,z3,z35,z5,z53,z6]),(0,[z0,z86,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z35,z5,z29]),(0,[z66,z0,z120,z2,z3,z5,z6]),(0,[z0,z43,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z621,z4,z5,z6])],[(0,[z0,z111,z3,z84,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z124,z56]),(0,[z95,z0,z2,z3,z4,z5,z90]),(0,[z0,z2,z3,z4,z5,z622,z6]),(0,[z0,z2,z3,z4,z70,z5,z6])],[(0,[z0,z2,z3,z623,z4,z5,z6]),(0,[z40,z2,z3,z101,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z35,z5,z624,z6]),(0,[z0,z2,z3,z4,z5,z485,z6]),(0,[z0,z2,z4,z5,z53,z6,z27])],[(0,[z0,z2,z3,z125,z4,z5,z6])],[(0,[z115,z2,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z625,z4,z5,z6]),(0,[z148,z0,z2,z3,z35,z5,z6]),(1,[z464,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z139,z5,z6]),(0,[z0,z2,z113,z3,z13,z5,z6]),(0,[z0,z2,z3,z13,z5,z124,z6]),(0,[z0,z2,z3,z4,z493,z5,z6])],[(0,[z2,z3,z101,z4,z126,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z6]),(1,[z66,z0,z2,z3,z5,z29]),(0,[z0,z2,z3,z626,z4,z5,z6]),(0,[z0,z2,z3,z4,z627,z5,z6]),(0,[z0,z2,z3,z5,z6,z247,z90]),(0,[z26,z0,z2,z52,z4,z5,z6])],[(0,[z0,z2,z3,z67,z4,z5,z56]),(0,[z0,z2,z3,z4,z203,z19,z5]),(0,[z0,z2,z3,z4,z5,z628,z6])]],
   [[(0,[z66,z0,z2,z3,z5,z117,z6])],[(0,[z0,z2,z28,z3,z35,z5,z6])],[(0,[z187,z40,z0,z3,z4,z5,z6]),(0,[z148,z66,z0,z2,z3,z5,z6]),(0,[z75,z0,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z5,z60,z6]),(0,[z66,z0,z2,z3,z119,z5,z6]),(0,[z0,z22,z2,z3,z50,z5,z6])],[(0,[z0,z2,z3,z629,z35,z5,z6]),(0,[z33,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z630,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z631])],[],[(0,[z0,z2,z54,z3,z4,z5,z56]),(0,[z0,z2,z3,z98,z13,z5,z6]),(0,[z0,z2,z3,z629,z4,z5,z6]),(0,[z26,z616,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z22,z2,z3,z70,z5,z6]),(0,[z632,z0,z2,z3,z4,z5,z6])],[(0,[z441,z0,z2,z3,z4,z5,z29]),(0,[z438,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z111,z3,z13,z5,z6]),(0,[z0,z2,z72,z28,z4,z5,z6]),(0,[z633,z0,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z13,z5,z29]),(0,[z0,z2,z3,z634,z4,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z272]),(0,[z0,z2,z3,z635,z4,z5,z6]),(0,[z0,z2,z3,z189,z13,z5,z6])],[(0,[z0,z22,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z5,z29,z90])],[(0,[z66,z109,z0,z2,z3,z5,z6]),(0,[z148,z0,z2,z3,z4,z5,z221]),(0,[z0,z2,z3,z4,z5,z56,z56]),(0,[z0,z2,z3,z4,z5,z56,z432]),(0,[z0,z2,z3,z67,z4,z122,z6])],[(0,[z0,z2,z3,z636,z4,z5,z6]),(0,[z148,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z637,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z56,z519]),(0,[z26,z0,z2,z3,z4,z5,z29]),(0,[z66,z0,z2,z52,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z495])],[(0,[z0,z2,z3,z35,z35,z5,z6])],[(1,[z339,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z192,z6]),(0,[z0,z2,z3,z4,z5,z447,z29]),(0,[z0,z2,z12,z3,z4,z5,z6]),(0,[z0,z2,z72,z3,z396,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z638])]],
   [[(1,[z256,z2,z3,z4,z5,z6])],[(0,[z639,z0,z2,z3,z4,z5,z6]),(0,[z535,z0,z2,z3,z4,z5,z6]),(0,[z39,z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z640,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z60,z6])],[(0,[z133,z0,z2,z28,z4,z5,z6]),(0,[z0,z2,z28,z3,z13,z5,z6]),(1,[z2,z3,z4,z5,z29,z56]),(0,[z0,z85,z22,z2,z3,z5,z6]),(1,[z0,z2,z3,z4,z500,z6])],[(0,[z0,z2,z3,z4,z641,z5,z6]),(0,[z388,z0,z2,z3,z4,z5,z56]),(0,[z0,z57,z3,z4,z5,z48,z6]),(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z642,z4,z5,z6])],[(0,[z40,z0,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z20,z5,z29]),(0,[z33,z0,z2,z3,z13,z5,z6]),(0,[z33,z0,z2,z3,z4,z5,z93])],[(0,[z0,z2,z3,z4,z5,z6,z90]),(0,[z0,z643,z2,z3,z4,z5,z6])],[(0,[z644,z0,z2,z3,z4,z5,z6]),(0,[z151,z0,z2,z3,z4,z63,z6]),(0,[z0,z205,z22,z2,z3,z5,z6])],[(0,[z645,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z126,z5,z29]),(0,[z0,z2,z3,z291,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z646,z6]),(0,[z0,z2,z3,z4,z5,z6,z647])],[(0,[z114,z133,z2,z3,z4,z5,z6]),(0,[z148,z0,z2,z3,z82,z5,z6]),(0,[z0,z2,z3,z4,z196,z5,z6]),(0,[z0,z2,z3,z4,z19,z5,z6]),(0,[z47,z0,z2,z3,z35,z5,z6])],[(0,[z0,z2,z3,z4,z5,z648,z6]),(0,[z0,z2,z3,z50,z4,z5,z93])],[(0,[z649,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z273,z5,z6]),(1,[z95,z0,z3,z4,z5,z90])],[(0,[z0,z2,z3,z4,z5,z650,z6]),(0,[z0,z2,z3,z651,z4,z5,z6]),(0,[z652,z0,z2,z3,z4,z5,z6])],[(0,[z0,z120,z57,z3,z4,z5,z6]),(0,[z653,z0,z2,z3,z4,z5,z6])],[],[(0,[z549,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z127]),(0,[z0,z2,z3,z4,z5,z48,z56]),(0,[z223,z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z654,z5,z6]),(0,[z0,z2,z113,z4,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z655,z6]),(0,[z0,z2,z3,z4,z5,z6,z656])],[(0,[z0,z2,z3,z35,z13,z5,z6]),(0,[z0,z2,z657,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z64,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z658,z6]),(0,[z659,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z660,z4,z5,z6])],[(0,[z0,z2,z3,z661,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z175,z6])],[(0,[z0,z2,z3,z64,z4,z5,z6]),(0,[z0,z2,z3,z4,z662,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z29]),(0,[z71,z0,z2,z3,z35,z5,z6]),(0,[z0,z22,z2,z3,z5,z6,z90]),(0,[z0,z2,z3,z13,z5,z48,z6])],[(0,[z0,z663,z2,z3,z4,z5,z6]),(0,[z114,z0,z2,z3,z35,z5,z6])],[(0,[z30,z2,z3,z64,z4,z5,z6]),(1,[z133,z2,z3,z4,z5,z56]),(0,[z0,z664,z2,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z665,z6]),(0,[z0,z2,z3,z4,z70,z5,z27]),(0,[z0,z666,z2,z3,z4,z5,z6])],[(0,[z0,z2,z72,z64,z4,z5,z6]),(0,[z40,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z311,z6]),(0,[z66,z0,z2,z3,z5,z29,z6]),(0,[z0,z22,z2,z3,z19,z5,z6]),(1,[z0,z2,z3,z421,z5,z6]),(0,[z26,z0,z2,z3,z4,z500,z6]),(0,[z0,z2,z3,z4,z667,z5,z6])],[(0,[z0,z2,z316,z3,z4,z5,z56]),(0,[z71,z0,z3,z25,z4,z5,z6]),(0,[z0,z2,z3,z3,z35,z5,z6]),(0,[z0,z2,z668,z3,z4,z5,z6])],[],[(0,[z0,z2,z414,z3,z4,z5,z6]),(0,[z71,z66,z0,z2,z3,z5,z6])],[(0,[z47,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z72,z3,z35,z5,z6])],[(0,[z669,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z287,z13,z5,z6]),(0,[z0,z2,z3,z670,z4,z5,z6])],[(0,[z0,z2,z72,z3,z4,z5,z6])],[(0,[z0,z671,z2,z3,z4,z5,z6])],[(0,[z115,z0,z2,z3,z4,z5,z38]),(0,[z672,z0,z2,z3,z4,z5,z6]),(1,[z0,z227,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z396,z5,z6])],[(0,[z30,z0,z2,z3,z178,z5,z6]),(0,[z0,z2,z3,z4,z164,z5,z56]),(0,[z673,z0,z2,z3,z4,z5,z6])],[(0,[z133,z0,z2,z64,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z395]),(0,[z0,z2,z509,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z674,z6]),(0,[z0,z313,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z53,z6])],[(1,[z0,z2,z3,z4,z5,z56])],[(1,[z0,z2,z3,z4,z5,z475]),(0,[z0,z2,z3,z13,z164,z5,z6]),(0,[z0,z2,z3,z675,z4,z5,z6]),(0,[z71,z0,z2,z25,z4,z5,z6]),(0,[z66,z0,z147,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z533,z6])],[(0,[z133,z0,z2,z3,z35,z5,z6]),(0,[z0,z120,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z624,z6])],[(0,[z114,z0,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z35,z5,z29,z6]),(0,[z0,z2,z3,z25,z35,z5,z6])],[(1,[z66,z0,z2,z3,z5,z56]),(0,[z0,z2,z3,z13,z5,z6,z431]),(0,[z121,z0,z2,z35,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z676])],[(0,[z0,z2,z3,z25,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z6])],[(0,[z77,z0,z2,z3,z4,z5,z6]),(0,[z0,z120,z3,z25,z4,z5,z6]),(0,[z0,z2,z3,z3,z13,z5,z6])],[(0,[z0,z2,z3,z4,z5,z63,z29]),(0,[z0,z2,z3,z4,z5,z677,z6]),(0,[z0,z2,z3,z4,z5,z678,z6]),(0,[z0,z2,z52,z3,z107,z5,z6])],[(0,[z0,z2,z679,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z680,z5,z6])],[(0,[z0,z2,z3,z4,z164,z122,z6]),(0,[z0,z2,z3,z4,z681,z5,z6]),(0,[z0,z682,z2,z3,z4,z5,z6])],[(0,[z683,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z684,z6]),(0,[z0,z2,z3,z4,z5,z315,z6]),(0,[z269,z0,z22,z2,z3,z5,z6])],[(0,[z0,z22,z2,z3,z5,z53,z6])],[(0,[z440,z0,z2,z3,z4,z5,z6]),(0,[z0,z516,z2,z3,z4,z5,z29]),(0,[z66,z0,z2,z3,z5,z6,z100]),(0,[z0,z2,z3,z685,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z686,z6]),(0,[z0,z2,z3,z4,z70,z6,z100])]],
   [[(0,[z0,z85,z111,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z456]),(0,[z616,z0,z2,z3,z4,z5,z6]),(0,[z0,z687,z2,z3,z4,z5,z6])],[(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z0,z689,z2,z3,z4,z5,z6])],[(0,[z690,z0,z2,z3,z4,z5,z6]),(0,[z691,z0,z2,z3,z4,z5,z6]),(0,[z40,z0,z2,z3,z4,z5,z565]),(0,[z0,z2,z3,z5,z60,z6,z58])],[(0,[z131,z0,z2,z3,z13,z5,z6])],[(0,[z133,z0,z2,z3,z13,z5,z6]),(0,[z26,z0,z2,z3,z4,z5,z56]),(1,[z66,z0,z22,z3,z5,z6]),(0,[z66,z0,z2,z3,z55,z5,z6]),(0,[z0,z120,z2,z3,z13,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z100])],[(0,[z0,z2,z3,z4,z692,z5,z6]),(0,[z0,z2,z3,z25,z13,z5,z6]),(0,[z618,z0,z2,z3,z13,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z78]),(0,[z0,z2,z3,z693,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z694,z6])],[(0,[z0,z111,z3,z4,z5,z48,z6])],[],[(1,[z0,z2,z3,z4,z5,z272]),(1,[z0,z2,z3,z186,z5,z6])],[(0,[z0,z2,z3,z4,z5,z284,z6]),(0,[z66,z0,z2,z3,z5,z92,z6])],[(0,[z0,z22,z2,z42,z3,z5,z6])],[(0,[z148,z0,z2,z3,z4,z164,z6]),(0,[z695,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z20,z5,z56]),(0,[z66,z0,z2,z3,z84,z5,z6]),(0,[z0,z2,z257,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z5,z93]),(0,[z0,z2,z3,z4,z696,z5,z6])],[(0,[z131,z0,z2,z3,z159,z5,z6]),(0,[z0,z697,z2,z3,z4,z5,z6])],[(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z66,z114,z0,z2,z3,z5,z6]),(0,[z121,z0,z2,z3,z4,z5,z6])],[(0,[z133,z0,z2,z3,z4,z5,z240]),(0,[z71,z0,z57,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z456,z6]),(1,[z0,z2,z3,z50,z5,z124])],[(1,[z66,z109,z0,z3,z5,z6]),(0,[z0,z204,z2,z3,z4,z5,z6]),(0,[z459,z0,z2,z3,z4,z5,z56]),(0,[z95,z0,z2,z52,z3,z4,z5]),(0,[z0,z2,z3,z13,z20,z5,z6]),(0,[z699,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z12,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z700]),(1,[z0,z2,z3,z4,z5,z179])],[(0,[z0,z2,z28,z3,z599,z5,z6]),(0,[z47,z0,z2,z3,z4,z48,z6])],[(0,[z701,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z13,z126,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z128]),(0,[z0,z2,z113,z3,z4,z5,z29]),(0,[z223,z0,z2,z72,z4,z5,z6]),(0,[z0,z2,z3,z50,z5,z92,z6])],[(0,[z0,z2,z3,z4,z5,z702,z6]),(0,[z0,z2,z3,z484,z25,z4,z5]),(0,[z0,z2,z3,z35,z55,z5,z6]),(0,[z223,z0,z2,z4,z5,z122,z6])],[(0,[z131,z109,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z119,z5,z6]),(0,[z0,z22,z2,z3,z35,z5,z6])],[(0,[z0,z2,z3,z13,z61,z5,z6])],[(0,[z0,z2,z3,z4,z5,z703,z6])],[],[(0,[z0,z2,z3,z4,z5,z122,z29]),(0,[z0,z2,z3,z4,z13,z5,z6]),(0,[z0,z2,z3,z35,z5,z92,z6])],[],[(0,[z0,z2,z3,z98,z4,z5,z29]),(0,[z66,z0,z2,z3,z5,z6,z27]),(0,[z66,z0,z3,z4,z119,z5,z6])],[(0,[z151,z2,z3,z64,z4,z5,z6]),(1,[z0,z2,z323,z3,z5,z6]),(0,[z95,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z228,z4,z5,z6]),(0,[z704,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z111,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z61,z5,z29]),(0,[z0,z2,z3,z4,z705,z5,z6])],[(0,[z109,z0,z2,z3,z4,z5,z6])],[(0,[z40,z0,z2,z3,z4,z5,z310]),(0,[z0,z2,z3,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z30,z2,z64,z4,z140,z6]),(0,[z0,z707,z3,z4,z5,z6]),(0,[z114,z2,z3,z4,z5,z708]),(0,[z0,z2,z3,z5,z709,z29]),(0,[z0,z2,z3,z4,z5,z710]),(0,[z346,z120,z2,z3,z4,z5])],[(0,[z0,z711,z3,z4,z5,z6]),(0,[z39,z2,z3,z126,z5,z6]),(0,[z0,z57,z12,z13,z5,z6]),(0,[z0,z2,z3,z368,z264,z6])],[(0,[z0,z712,z3,z4,z5,z6]),(0,[z148,z2,z3,z35,z63,z6]),(0,[z0,z2,z3,z484,z4,z5]),(0,[z0,z2,z3,z713,z5,z6]),(0,[z0,z2,z3,z4,z5,z714]),(0,[z223,z0,z2,z13,z122,z6]),(0,[z0,z2,z3,z68,z5,z6])],[(0,[z66,z0,z250,z3,z5,z6]),(0,[z66,z0,z2,z715,z5,z6]),(0,[z0,z716,z257,z3,z5,z6]),(0,[z0,z717,z2,z3,z5,z6])],[(0,[z66,z0,z3,z365,z5,z6]),(0,[z0,z718,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z719]),(0,[z0,z2,z3,z720,z5,z6]),(0,[z0,z2,z3,z721,z5,z6])],[(0,[z0,z2,z3,z722,z5,z6])],[(0,[z269,z2,z3,z4,z5,z56]),(0,[z0,z2,z34,z5,z122,z6]),(0,[z0,z2,z3,z723,z5,z6]),(0,[z0,z724,z3,z13,z5,z6]),(0,[z0,z2,z3,z725,z5,z6]),(0,[z0,z2,z54,z3,z5,z179])],[(0,[z0,z2,z149,z261,z5,z6]),(0,[z0,z2,z726,z4,z5,z6]),(0,[z0,z3,z4,z5,z727,z6]),(0,[z0,z2,z3,z5,z6,z728]),(0,[z0,z2,z3,z729,z5,z6])],[(0,[z2,z3,z64,z4,z5,z56]),(0,[z66,z0,z2,z730,z5,z6]),(0,[z0,z2,z3,z4,z731,z6])],[(0,[z275,z0,z111,z3,z5,z6]),(0,[z0,z2,z3,z96,z5,z402]),(0,[z0,z2,z3,z13,z163,z6]),(0,[z66,z133,z2,z28,z5,z6]),(0,[z2,z3,z4,z184,z164,z56]),(0,[z2,z3,z596,z4,z5,z56]),(0,[z212,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z142,z5,z29]),(0,[z89,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z732,z5,z6]),(0,[z0,z22,z2,z3,z5,z475]),(0,[z0,z341,z3,z4,z5,z565]),(0,[z0,z2,z3,z4,z144,z29]),(0,[z733,z0,z2,z3,z5,z6])],[(0,[z0,z734,z2,z3,z5,z6]),(0,[z148,z414,z3,z4,z5,z56]),(0,[z0,z2,z3,z735,z5,z6]),(0,[z736,z0,z2,z3,z4,z5]),(0,[z71,z0,z25,z4,z144,z6])],[(0,[z0,z2,z3,z737,z4,z6]),(0,[z738,z0,z2,z3,z5,z6]),(0,[z0,z414,z3,z35,z5,z6])],[(0,[z0,z2,z3,z739,z5,z6]),(0,[z0,z2,z3,z4,z5,z412]),(0,[z66,z0,z3,z119,z5,z29]),(0,[z66,z740,z2,z3,z5,z6]),(0,[z616,z22,z2,z3,z5,z6])],[(0,[z0,z414,z3,z4,z5,z6]),(0,[z0,z227,z3,z178,z5,z6]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z0,z2,z3,z742,z5,z6]),(0,[z2,z414,z3,z4,z5,z56]),(0,[z0,z2,z3,z261,z5,z29]),(0,[z148,z2,z3,z4,z743,z6]),(0,[z263,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z35,z5,z744])],[(0,[z0,z2,z3,z4,z5,z453]),(0,[z148,z66,z2,z3,z5,z56]),(0,[z0,z2,z35,z745,z5,z6]),(0,[z0,z2,z3,z746,z5,z6])]],
   [[(0,[z0,z9,z2,z3,z5,z56]),(0,[z0,z2,z3,z13,z140,z6]),(0,[z151,z2,z3,z4,z164,z415]),(0,[z0,z2,z3,z265,z5,z29]),(0,[z0,z2,z54,z3,z55,z6])],[(0,[z187,z40,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z102,z519]),(0,[z0,z2,z3,z4,z5,z747]),(0,[z0,z2,z3,z748,z5,z6]),(0,[z0,z2,z35,z13,z5,z6]),(0,[z749,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z178,z5,z56]),(0,[z148,z2,z3,z4,z63,z221]),(0,[z66,z75,z2,z3,z5,z56]),(0,[z750,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z178,z5,z475]),(0,[z148,z2,z3,z13,z63,z6]),(0,[z0,z2,z3,z5,z56,z247]),(0,[z0,z2,z3,z162,z5,z29]),(0,[z0,z2,z3,z4,z29,z751])],[(0,[z0,z2,z3,z752,z5,z6]),(0,[z0,z2,z72,z396,z20,z6])],[(0,[z0,z753,z3,z4,z5,z6]),(0,[z148,z2,z3,z35,z5,z56]),(0,[z0,z2,z3,z754,z5,z6]),(0,[z515,z0,z3,z4,z5,z90])],[(0,[z109,z0,z3,z139,z5,z6]),(0,[z275,z0,z2,z3,z5,z29]),(0,[z0,z2,z3,z4,z755,z6]),(0,[z307,z0,z25,z4,z5,z6]),(0,[z66,z69,z2,z3,z5,z6]),(0,[z2,z3,z4,z425,z328,z5])],[(0,[z0,z2,z3,z756,z5,z6]),(0,[z187,z0,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z757]),(0,[z0,z2,z3,z4,z5,z758]),(0,[z464,z22,z2,z3,z5,z6]),(0,[z759,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z760,z5,z6])],[(0,[z0,z2,z3,z35,z5,z6]),(0,[z66,z2,z3,z164,z5,z56]),(0,[z2,z3,z13,z164,z5,z56]),(0,[z761,z0,z3,z13,z5,z6]),(0,[z0,z2,z3,z370,z4,z70])],[(0,[z0,z2,z3,z4,z5,z762]),(0,[z30,z2,z64,z4,z5,z6]),(0,[z0,z2,z195,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z763])],[(0,[z0,z2,z34,z64,z5,z6]),(0,[z0,z2,z24,z3,z5,z29]),(0,[z764,z2,z3,z4,z5,z6])],[(0,[z0,z765,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z766]),(0,[z0,z2,z76,z3,z5,z395]),(0,[z0,z2,z3,z4,z5,z767])],[(0,[z0,z414,z3,z4,z5,z221])],[(0,[z2,z3,z4,z619,z5,z56]),(0,[z0,z2,z3,z4,z6,z751]),(0,[z0,z2,z3,z4,z5,z768]),(0,[z0,z2,z76,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z769])],[(0,[z66,z0,z2,z3,z5,z6]),(0,[z0,z227,z3,z96,z5,z6]),(0,[z66,z540,z0,z3,z5,z6]),(0,[z151,z2,z3,z4,z164,z56]),(0,[z2,z3,z4,z5,z677,z56]),(0,[z0,z2,z3,z4,z5,z770]),(0,[z0,z2,z54,z3,z771,z6])],[(0,[z0,z2,z3,z4,z5,z772]),(0,[z0,z2,z3,z773,z5,z6]),(0,[z0,z2,z52,z34,z5,z6]),(0,[z0,z22,z2,z3,z774,z5]),(0,[z0,z2,z3,z775,z5,z6])]],
   [[(0,[z9,z2,z111,z3,z5,z56]),(0,[z131,z109,z3,z4,z5,z56]),(0,[z0,z2,z3,z776,z5,z56]),(0,[z256,z2,z3,z4,z144,z6]),(0,[z749,z0,z3,z13,z5,z6]),(0,[z424,z0,z2,z35,z5,z6])],[(0,[z148,z2,z3,z4,z164,z56]),(0,[z66,z0,z3,z420,z5,z6]),(0,[z0,z2,z54,z3,z493,z6])],[(0,[z111,z3,z84,z4,z5,z56]),(0,[z0,z2,z3,z777,z5,z6]),(0,[z778,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z5,z6,z779]),(0,[z298,z2,z3,z4,z5,z192])],[(0,[z0,z2,z3,z91,z5,z56]),(0,[z69,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z780,z5,z6]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z782])],[(0,[z0,z2,z3,z5,z62,z56]),(0,[z0,z2,z3,z67,z4,z184]),(0,[z2,z3,z4,z783,z5,z6]),(0,[z2,z3,z4,z784,z5,z6]),(0,[z298,z2,z52,z3,z4,z5])],[(0,[z572,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z785,z5,z6]),(0,[z0,z2,z3,z35,z5,z221]),(0,[z148,z2,z3,z13,z5,z56]),(0,[z0,z2,z3,z786,z5,z6]),(0,[z26,z0,z43,z4,z5,z27]),(0,[z787,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z788]),(0,[z0,z341,z3,z4,z5,z310]),(0,[z0,z2,z3,z82,z5,z412]),(0,[z0,z2,z3,z5,z789,z6]),(0,[z26,z0,z2,z4,z5,z158]),(0,[z256,z2,z3,z4,z5,z790])],[(0,[z40,z2,z3,z101,z5,z56]),(0,[z0,z2,z3,z4,z5,z221]),(0,[z0,z414,z3,z82,z5,z6]),(0,[z791,z22,z2,z3,z5,z6]),(0,[z0,z444,z22,z3,z5,z6]),(0,[z0,z2,z3,z265,z500,z6])],[(0,[z0,z2,z3,z13,z5,z6]),(0,[z0,z204,z149,z4,z5,z6]),(0,[z0,z2,z3,z98,z92,z29])],[(0,[z0,z2,z3,z273,z144,z6])],[(0,[z2,z64,z4,z63,z122,z6]),(0,[z133,z2,z28,z35,z5,z6]),(0,[z0,z2,z3,z792,z5,z6])],[(0,[z66,z0,z2,z3,z5,z221]),(0,[z0,z2,z3,z225,z5,z56]),(0,[z0,z2,z3,z359,z5,z124])],[(0,[z114,z2,z3,z4,z5,z315]),(0,[z0,z2,z3,z793,z5,z6]),(0,[z71,z0,z794,z4,z5,z6]),(0,[z0,z22,z2,z3,z500,z6]),(0,[z0,z2,z3,z35,z5,z357])],[(0,[z0,z2,z3,z96,z5,z29]),(0,[z496,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z34,z5,z29]),(0,[z0,z2,z72,z35,z20,z6])],[(0,[z214,z2,z3,z126,z5,z6]),(1,[z414,z3,z4,z5,z56]),(0,[z0,z313,z2,z3,z5,z29]),(0,[z374,z0,z2,z3,z418,z6]),(0,[z0,z2,z3,z5,z6,z795])]],
   [[(0,[z131,z2,z3,z4,z5,z38]),(0,[z0,z2,z796,z3,z5,z6]),(0,[z0,z489,z3,z4,z140,z6]),(0,[z0,z797,z2,z3,z5,z6]),(0,[z0,z204,z3,z4,z5,z29]),(0,[z0,z2,z3,z798,z5,z6]),(0,[z0,z3,z84,z799,z5,z6])],[(0,[z298,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z240]),(0,[z0,z2,z3,z4,z5,z800]),(0,[z0,z257,z3,z4,z5,z6]),(0,[z704,z0,z25,z4,z5,z6]),(0,[z2,z3,z4,z203,z784,z5]),(0,[z0,z2,z3,z4,z5,z801])],[(0,[z0,z2,z3,z159,z5,z6]),(0,[z194,z2,z3,z4,z5,z6]),(0,[z639,z2,z3,z4,z5,z56]),(0,[z570,z2,z3,z4,z5,z29])],[(0,[z0,z2,z3,z802,z5,z6]),(0,[z545,z0,z3,z4,z48,z6]),(0,[z0,z2,z3,z4,z5,z240]),(0,[z66,z0,z2,z3,z5,z357]),(0,[z33,z0,z2,z3,z5,z93])],[(0,[z0,z2,z3,z803,z5,z6]),(0,[z0,z361,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z456]),(0,[z804,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z805])],[(0,[z0,z2,z3,z4,z5,z806]),(0,[z0,z2,z3,z125,z5,z56]),(0,[z0,z85,z3,z4,z463,z6]),(0,[z0,z2,z3,z5,z807,z6]),(0,[z0,z2,z3,z13,z5,z808]),(0,[z451,z2,z3,z252,z5,z6])],[(0,[z0,z2,z3,z4,z5,z456]),(0,[z66,z0,z3,z799,z5,z6])],[(0,[z131,z2,z3,z35,z5,z56]),(0,[z66,z0,z2,z3,z5,z240]),(0,[z0,z2,z3,z5,z170,z6])],[(0,[z2,z3,z4,z5,z192,z56]),(0,[z0,z2,z3,z4,z5,z809]),(0,[z0,z376,z2,z3,z325,z6]),(0,[z307,z0,z2,z4,z122,z6]),(0,[z0,z2,z3,z4,z810,z6]),(0,[z223,z0,z2,z4,z122,z381])],[(0,[z0,z2,z3,z4,z163,z402]),(0,[z0,z2,z3,z811,z5,z6]),(0,[z39,z2,z3,z126,z5,z453]),(0,[z0,z2,z3,z812,z5,z56]),(0,[z0,z2,z3,z228,z5,z29]),(0,[z0,z2,z3,z4,z5,z813]),(0,[z0,z2,z3,z107,z5,z29]),(0,[z0,z22,z2,z3,z5,z11]),(0,[z66,z0,z558,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z814]),(0,[z0,z2,z815,z3,z5,z6]),(0,[z66,z0,z2,z3,z5,z456])],[(0,[z0,z2,z3,z159,z5,z94]),(0,[z2,z195,z4,z5,z63,z6]),(0,[z2,z3,z4,z5,z29,z403]),(0,[z0,z2,z3,z816,z5,z6]),(0,[z0,z85,z3,z4,z727,z6]),(0,[z0,z3,z4,z5,z6,z817]),(0,[z0,z2,z3,z4,z5,z818])],[(0,[z133,z2,z28,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z819]),(0,[z0,z2,z3,z273,z175,z6]),(0,[z0,z536,z3,z4,z5,z60])],[(0,[z0,z2,z13,z5,z6,z542]),(0,[z0,z820,z2,z3,z5,z6]),(0,[z0,z2,z3,z821,z5,z6])],[(0,[z0,z2,z623,z13,z5,z6]),(0,[z234,z822,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z6,z823]),(0,[z0,z2,z3,z13,z5,z357]),(0,[z824,z2,z3,z4,z5,z6])],[(0,[z0,z825,z2,z3,z5,z6]),(0,[z133,z22,z2,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z826]),(0,[z66,z0,z2,z3,z827,z6]),(0,[z0,z22,z2,z3,z828,z6]),(0,[z0,z2,z72,z13,z20,z6]),(0,[z0,z2,z35,z224,z5,z6]),(0,[z0,z2,z3,z5,z6,z829])]],
   [[(0,[z0,z2,z3,z4,z140,z402]),(0,[z2,z3,z4,z5,z646,z56]),(0,[z0,z2,z3,z142,z5,z56]),(0,[z0,z2,z3,z4,z175,z11]),(0,[z830,z2,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z831])],[(0,[z0,z2,z3,z4,z144,z56])],[(0,[z0,z2,z832,z4,z5,z6]),(0,[z0,z2,z3,z4,z833,z6]),(0,[z0,z341,z3,z4,z5,z29]),(0,[z0,z834,z3,z4,z5,z6]),(0,[z2,z195,z4,z5,z6,z56]),(0,[z0,z2,z3,z82,z5,z221]),(0,[z166,z0,z2,z3,z5,z6]),(0,[z275,z0,z3,z19,z5,z6]),(0,[z275,z0,z3,z196,z5,z6])],[(0,[z0,z22,z2,z3,z5,z38]),(0,[z114,z2,z3,z4,z5,z348])],[(0,[z2,z3,z651,z4,z5,z56]),(0,[z835,z0,z489,z3,z5,z6]),(0,[z0,z414,z3,z4,z5,z412]),(0,[z66,z0,z486,z3,z5,z6]),(0,[z836,z0,z2,z3,z5,z6]),(0,[z66,z0,z3,z119,z5,z56]),(0,[z0,z22,z2,z3,z5,z837]),(0,[z223,z86,z2,z4,z122,z6])],[(0,[z0,z2,z3,z261,z5,z56]),(0,[z263,z2,z3,z4,z5,z56])],[(0,[z0,z111,z3,z139,z5,z6]),(0,[z133,z2,z28,z4,z5,z240]),(0,[z0,z2,z3,z4,z5,z565]),(0,[z2,z3,z4,z7,z5,z56]),(0,[z0,z2,z3,z61,z62,z100])],[(0,[z2,z3,z4,z5,z655,z56]),(0,[z0,z2,z3,z265,z5,z56]),(0,[z838,z2,z3,z4,z5,z6]),(0,[z0,z22,z3,z14,z5,z6]),(0,[z0,z2,z3,z5,z6,z839])],[(0,[z131,z2,z3,z13,z5,z56]),(0,[z0,z2,z3,z4,z5,z469]),(0,[z0,z840,z2,z3,z5,z6])],[(0,[z2,z3,z64,z35,z5,z56]),(0,[z0,z2,z72,z4,z517,z6]),(0,[z0,z2,z195,z4,z63,z6]),(0,[z841,z2,z3,z4,z5,z6])],[(0,[z66,z535,z0,z3,z5,z6]),(0,[z66,z2,z3,z64,z5,z56]),(0,[z0,z842,z3,z4,z5,z6]),(0,[z0,z2,z3,z162,z5,z56]),(0,[z0,z22,z2,z3,z5,z395]),(0,[z0,z22,z183,z3,z5,z6]),(0,[z0,z2,z3,z843,z5,z6]),(0,[z0,z2,z3,z5,z124,z844])],[(0,[z111,z3,z623,z4,z5,z6]),(0,[z2,z3,z4,z662,z5,z56]),(0,[z0,z2,z3,z845,z5,z6]),(0,[z0,z2,z3,z846,z5,z6]),(0,[z616,z2,z3,z265,z5,z6])],[(0,[z75,z2,z3,z4,z5,z56]),(0,[z0,z22,z2,z3,z5,z56]),(0,[z15,z0,z3,z4,z48,z6]),(0,[z360,z0,z2,z3,z5,z533]),(0,[z66,z194,z2,z3,z5,z6])],[(0,[z275,z0,z2,z3,z5,z56])],[(0,[z0,z847,z3,z4,z5,z6]),(0,[z0,z2,z3,z848,z5,z6]),(0,[z2,z72,z64,z4,z5,z56]),(0,[z0,z2,z3,z35,z5,z412]),(0,[z151,z2,z3,z4,z743,z6]),(0,[z0,z2,z3,z4,z5,z849]),(0,[z0,z2,z3,z850,z5,z6])],[(0,[z269,z2,z3,z126,z5,z6]),(0,[z0,z2,z3,z851,z5,z6]),(0,[z66,z0,z3,z471,z5,z6]),(0,[z33,z0,z2,z3,z5,z174]),(0,[z0,z2,z3,z4,z477,z6])]],
   [[(0,[z66,z133,z111,z3,z5,z6]),(0,[z0,z2,z3,z35,z5,z453]),(0,[z95,z0,z3,z4,z5,z559])],[(0,[z0,z2,z24,z3,z5,z56]),(0,[z0,z2,z3,z4,z852,z29]),(0,[z0,z2,z3,z59,z5,z6]),(0,[z0,z2,z3,z853,z5,z6])],[(0,[z0,z2,z3,z4,z854,z6]),(0,[z0,z855,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z856]),(0,[z66,z0,z3,z479,z5,z6]),(0,[z0,z2,z3,z4,z175,z56]),(0,[z857,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z858]),(0,[z234,z0,z120,z3,z4,z5]),(0,[z0,z2,z3,z859,z5,z6]),(0,[z86,z22,z2,z3,z5,z6]),(0,[z275,z95,z0,z3,z5,z6]),(0,[z0,z860,z3,z4,z5,z6])],[(0,[z0,z2,z3,z861,z5,z6]),(0,[z66,z0,z2,z3,z5,z412]),(0,[z2,z3,z4,z425,z5,z6]),(0,[z632,z2,z3,z4,z164,z6])],[(0,[z0,z2,z3,z4,z5,z862]),(0,[z0,z2,z640,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z863])],[(0,[z0,z2,z3,z864,z5,z6]),(0,[z66,z0,z2,z3,z5,z453]),(0,[z301,z0,z2,z3,z5,z373]),(0,[z865,z0,z2,z3,z5,z6]),(0,[z298,z2,z3,z4,z70,z5]),(0,[z0,z509,z3,z35,z5,z6])],[(0,[z133,z2,z3,z4,z5,z866]),(0,[z151,z2,z195,z4,z5,z6]),(0,[z223,z0,z2,z4,z122,z29]),(0,[z618,z0,z2,z3,z5,z93])],[(0,[z0,z2,z3,z241,z5,z29]),(0,[z0,z509,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z867,z6])],[(0,[z578,z0,z2,z4,z122,z6]),(0,[z0,z2,z35,z260,z5,z6]),(0,[z0,z205,z2,z3,z5,z29]),(0,[z868,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z869,z5,z6]),(0,[z0,z2,z3,z4,z5,z870]),(0,[z0,z716,z2,z3,z5,z6])],[(0,[z0,z2,z871,z3,z5,z6]),(0,[z0,z734,z489,z3,z5,z6]),(0,[z30,z2,z64,z35,z5,z6]),(0,[z2,z3,z64,z13,z5,z56]),(0,[z0,z872,z3,z4,z5,z6]),(0,[z0,z22,z509,z3,z5,z6]),(0,[z0,z2,z3,z189,z5,z232])],[(0,[z0,z2,z3,z4,z5,z873]),(0,[z0,z2,z3,z4,z874,z6]),(0,[z2,z3,z675,z4,z5,z56]),(0,[z69,z2,z3,z4,z5,z56]),(0,[z0,z2,z35,z157,z5,z6])],[(0,[z875,z2,z3,z4,z5,z6]),(0,[z275,z0,z22,z3,z5,z6]),(0,[z95,z346,z2,z3,z4,z5]),(0,[z876,z2,z3,z4,z5,z6]),(0,[z0,z257,z3,z68,z5,z6]),(0,[z2,z3,z67,z4,z70,z425])],[(0,[z2,z3,z35,z5,z29,z56]),(0,[z0,z2,z3,z171,z5,z6]),(0,[z66,z95,z0,z3,z5,z90]),(0,[z0,z2,z3,z505,z5,z6]),(0,[z26,z0,z2,z35,z5,z27])],[(0,[z0,z2,z3,z4,z163,z29]),(0,[z0,z2,z745,z4,z5,z6])],[(0,[z0,z2,z3,z877,z5,z6]),(0,[z0,z2,z3,z13,z5,z412]),(0,[z878,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z35,z5,z770]),(0,[z0,z361,z3,z68,z5,z6]),(0,[z0,z2,z3,z4,z5,z381]),(0,[z26,z0,z2,z4,z5,z27])]],
   [[(0,[z0,z414,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z879]),(0,[z0,z22,z2,z72,z20,z6]),(0,[z880,z2,z3,z4,z203,z5])],[(0,[z0,z2,z3,z13,z5,z453]),(0,[z148,z2,z149,z4,z63,z6]),(0,[z22,z2,z3,z425,z5,z6]),(0,[z0,z3,z4,z5,z881,z6])],[(0,[z66,z0,z3,z154,z5,z6]),(0,[z0,z2,z3,z882,z5,z6]),(0,[z26,z0,z2,z283,z4,z5]),(0,[z346,z2,z3,z35,z5,z6]),(1,[z0,z2,z3,z4,z883])],[(0,[z0,z22,z2,z3,z5,z272]),(0,[z0,z2,z3,z4,z5,z310])],[(0,[z66,z2,z111,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z866]),(0,[z346,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z164,z122,z56]),(0,[z0,z2,z3,z884,z5,z6])],[(0,[z0,z2,z3,z885,z4,z6]),(0,[z2,z3,z4,z5,z315,z56]),(0,[z0,z2,z3,z96,z5,z56]),(0,[z0,z2,z3,z4,z140,z29]),(0,[z0,z2,z3,z34,z5,z56])],[(0,[z0,z2,z3,z96,z5,z475]),(0,[z23,z0,z2,z4,z122,z6]),(0,[z300,z2,z3,z4,z5,z56]),(0,[z0,z313,z2,z3,z5,z56]),(0,[z66,z256,z2,z3,z5,z6]),(0,[z0,z2,z42,z13,z5,z6])],[(0,[z275,z109,z0,z3,z5,z6]),(0,[z66,z0,z2,z3,z5,z310]),(0,[z0,z204,z3,z4,z5,z56]),(0,[z886,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z421,z5,z78])],[(0,[z0,z2,z3,z599,z5,z6]),(0,[z148,z2,z3,z4,z63,z29]),(0,[z0,z2,z113,z13,z5,z56]),(0,[z0,z2,z3,z4,z5,z887]),(0,[z0,z85,z3,z4,z19,z29]),(0,[z464,z2,z3,z4,z5,z888])],[(0,[z85,z111,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z889]),(0,[z0,z22,z2,z3,z5,z890])],[(0,[z0,z2,z3,z35,z5,z327]),(0,[z0,z2,z3,z4,z5,z891]),(0,[z0,z2,z3,z745,z5,z6])],[(0,[z66,z0,z9,z3,z5,z6]),(0,[z30,z2,z64,z13,z5,z6]),(0,[z892,z0,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z179]),(0,[z95,z0,z3,z4,z420,z5])],[(0,[z0,z489,z3,z4,z163,z6]),(0,[z0,z2,z3,z4,z5,z327]),(0,[z0,z2,z141,z13,z5,z6]),(0,[z2,z3,z4,z5,z56,z158]),(0,[z129,z0,z2,z3,z5,z93])],[(0,[z66,z0,z489,z3,z5,z6]),(0,[z0,z893,z3,z4,z5,z6]),(0,[z0,z2,z3,z291,z5,z128]),(0,[z0,z22,z2,z3,z5,z894])],[(0,[z0,z2,z3,z4,z5,z895]),(0,[z133,z2,z46,z4,z5,z6])],[(0,[z57,z111,z3,z4,z5,z56]),(0,[z111,z3,z4,z5,z48,z56]),(0,[z0,z2,z3,z4,z5,z896]),(0,[z0,z2,z3,z4,z897,z56]),(0,[z0,z2,z3,z105,z4,z97])]],
   [[(0,[z0,z2,z3,z898,z4,z5]),(0,[z66,z0,z2,z3,z5,z327]),(0,[z2,z3,z4,z899,z5,z6]),(0,[z0,z2,z3,z4,z900,z6]),(0,[z0,z2,z3,z228,z5,z56]),(0,[z0,z2,z3,z107,z5,z56]),(0,[z0,z2,z3,z4,z5,z901])],[(0,[z0,z902,z3,z4,z5,z6]),(0,[z40,z2,z3,z899,z5,z6]),(0,[z0,z2,z3,z5,z6,z903]),(0,[z2,z3,z4,z207,z5,z29]),(0,[z263,z2,z3,z273,z5,z6]),(0,[z0,z2,z3,z4,z144,z11]),(0,[z0,z3,z640,z4,z48,z6]),(0,[z298,z2,z3,z4,z5,z60])],[(0,[z904,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z905,z6]),(0,[z0,z2,z906,z4,z5,z6]),(0,[z298,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z907]),(0,[z0,z257,z3,z35,z5,z6])],[(0,[z0,z2,z3,z908,z5,z6]),(0,[z0,z2,z3,z909,z5,z6]),(0,[z194,z2,z3,z35,z5,z6]),(0,[z0,z3,z283,z4,z5,z90]),(0,[z346,z2,z3,z13,z5,z6])],[(0,[z148,z2,z149,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z910])],[(0,[z66,z0,z111,z3,z5,z6]),(0,[z2,z3,z899,z126,z5,z6]),(1,[z2,z3,z4,z743,z6]),(0,[z263,z2,z3,z4,z5,z11]),(0,[z116,z0,z2,z35,z5,z6]),(0,[z0,z911,z3,z4,z5,z6]),(0,[z0,z361,z3,z35,z5,z6]),(0,[z86,z2,z3,z4,z5,z912])],[(0,[z0,z2,z3,z139,z5,z315]),(0,[z0,z2,z3,z913,z5,z6]),(0,[z114,z22,z2,z3,z5,z29]),(0,[z0,z2,z914,z3,z5,z6]),(0,[z88,z0,z2,z3,z5,z93])],[(0,[z0,z2,z149,z4,z5,z6]),(0,[z0,z2,z3,z915,z5,z6])],[(0,[z0,z2,z136,z13,z5,z6]),(0,[z0,z2,z3,z916,z5,z6]),(0,[z917,z22,z2,z3,z5,z6])],[(0,[z918,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z13,z5,z221]),(0,[z0,z919,z3,z4,z5,z6])],[(0,[z2,z920,z64,z4,z5,z6]),(0,[z133,z2,z28,z599,z5,z6]),(0,[z0,z2,z3,z921,z5,z6]),(0,[z522,z2,z3,z304,z5,z6]),(0,[z464,z2,z3,z4,z5,z922])],[(0,[z0,z2,z3,z4,z923,z6]),(1,[z2,z3,z899,z5,z6]),(0,[z135,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z5,z6,z924]),(0,[z0,z2,z3,z4,z925,z6]),(0,[z0,z257,z3,z4,z20,z6])],[(0,[z0,z2,z3,z4,z5,z926]),(0,[z0,z2,z3,z927,z5,z6]),(0,[z0,z2,z3,z928,z5,z6]),(0,[z0,z57,z546,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z29]),(0,[z738,z0,z227,z3,z5,z6]),(0,[z0,z2,z929,z4,z5,z6])],[(0,[z930,z0,z3,z4,z5,z6]),(0,[z71,z0,z25,z4,z5,z6]),(0,[z2,z3,z4,z425,z5,z27])]],
   [[(0,[z0,z2,z3,z4,z931,z5]),(0,[z0,z2,z3,z4,z122,z78]),(0,[z0,z2,z3,z4,z487,z100])],[(0,[z616,z2,z3,z4,z5,z348]),(0,[z464,z2,z3,z4,z5,z78])],[(0,[z66,z131,z109,z3,z5,z6]),(0,[z234,z0,z509,z3,z4,z5]),(0,[z223,z0,z2,z421,z122,z6]),(0,[z0,z43,z3,z265,z5,z6])],[(0,[z115,z9,z111,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z932]),(0,[z185,z2,z3,z4,z5,z29]),(0,[z298,z2,z3,z13,z5,z6]),(0,[z298,z2,z3,z4,z5,z100]),(0,[z0,z257,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z933]),(0,[z0,z2,z281,z4,z20,z6]),(0,[z0,z509,z3,z4,z5,z27])],[(0,[z0,z2,z3,z5,z934,z6]),(0,[z194,z2,z3,z13,z5,z6]),(0,[z2,z3,z13,z5,z935,z6])],[(0,[z0,z2,z3,z13,z5,z240]),(0,[z936,z0,z2,z3,z5,z6])],[(0,[z2,z3,z4,z5,z56,z220]),(0,[z47,z0,z3,z162,z48,z6]),(0,[z0,z361,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z831]),(0,[z0,z2,z3,z271,z92,z6]),(0,[z0,z2,z3,z937,z5,z6])],[(0,[z0,z938,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z565]),(0,[z95,z0,z22,z3,z5,z90])],[(0,[z2,z3,z4,z156,z5,z56]),(0,[z0,z2,z3,z4,z5,z939]),(0,[z2,z3,z4,z706,z5,z56]),(0,[z0,z2,z3,z13,z5,z456]),(0,[z181,z0,z3,z4,z48,z6]),(0,[z275,z47,z0,z3,z5,z6])],[(0,[z0,z2,z3,z35,z5,z469]),(0,[z0,z2,z3,z940,z5,z6]),(0,[z8,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z941,z5])],[(0,[z0,z2,z3,z139,z5,z94]),(0,[z520,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z942,z5,z6]),(0,[z223,z464,z2,z4,z122,z6]),(0,[z0,z2,z3,z68,z5,z381])],[(0,[z0,z2,z3,z943,z5,z6])],[(0,[z0,z489,z3,z4,z5,z6]),(0,[z235,z2,z3,z287,z5,z6]),(0,[z0,z944,z3,z35,z5,z6])],[(0,[z66,z0,z2,z3,z5,z565]),(0,[z75,z2,z3,z35,z5,z56]),(0,[z0,z2,z3,z945,z5,z6]),(0,[z95,z0,z509,z3,z4,z5]),(0,[z0,z509,z3,z4,z477,z6]),(0,[z946,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z947,z4,z5]),(0,[z223,z0,z2,z4,z122,z56]),(0,[z0,z948,z2,z3,z5,z6]),(0,[z0,z2,z3,z629,z5,z624]),(0,[z0,z944,z3,z4,z5,z6]),(0,[z949,z2,z3,z4,z5,z6])],[(0,[z133,z2,z3,z4,z5,z402]),(0,[z2,z3,z4,z5,z866,z56]),(0,[z66,z0,z2,z3,z5,z469]),(0,[z0,z2,z3,z950,z5,z56]),(0,[z0,z2,z3,z4,z951,z6]),(0,[z822,z2,z3,z4,z5,z6]),(0,[z346,z2,z3,z4,z5,z27])]],
   [[(0,[z0,z2,z3,z4,z5,z952]),(0,[z0,z2,z3,z953,z5,z6]),(0,[z66,z0,z227,z3,z5,z6]),(0,[z0,z205,z2,z3,z5,z56]),(0,[z66,z263,z2,z3,z5,z6]),(0,[z0,z2,z954,z4,z5,z6]),(0,[z0,z2,z3,z955,z5,z6]),(0,[z0,z2,z3,z35,z477,z6]),(0,[z0,z956,z3,z4,z5,z6])],[(0,[z0,z227,z3,z4,z163,z6]),(0,[z133,z2,z28,z4,z5,z29]),(0,[z0,z2,z149,z82,z5,z6]),(0,[z0,z2,z3,z5,z6,z957])],[(0,[z0,z9,z341,z3,z5,z6]),(0,[z66,z0,z414,z3,z5,z6]),(0,[z0,z2,z3,z4,z958,z6]),(0,[z959,z0,z2,z3,z5,z6]),(0,[z0,z960,z2,z3,z5,z6]),(0,[z961,z0,z2,z3,z5,z6])],[(0,[z66,z111,z3,z4,z5,z56]),(0,[z234,z0,z3,z4,z5,z90]),(0,[z234,z0,z2,z24,z3,z5]),(0,[z66,z0,z2,z726,z5,z6])],[(0,[z256,z2,z3,z4,z5,z6]),(0,[z131,z2,z3,z159,z5,z56]),(0,[z0,z2,z3,z4,z962,z6]),(0,[z0,z2,z963,z4,z5,z6]),(0,[z0,z2,z3,z964,z5,z6]),(0,[z0,z2,z3,z965,z5,z6]),(0,[z0,z2,z72,z4,z20,z29]),(0,[z0,z22,z2,z3,z5,z966])],[(0,[z0,z2,z3,z4,z163,z56]),(0,[z0,z2,z3,z967,z5,z6]),(0,[z0,z2,z3,z968,z5,z6]),(1,[z830,z2,z3,z4,z5]),(0,[z0,z2,z4,z20,z969,z6]),(0,[z0,z2,z3,z970,z5,z6])],[(0,[z115,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z163,z475]),(0,[z39,z2,z3,z126,z5,z327]),(0,[z2,z3,z4,z5,z29,z56]),(0,[z2,z3,z4,z5,z49,z56]),(0,[z371,z147,z2,z3,z5,z6]),(0,[z66,z0,z2,z3,z958,z6]),(0,[z66,z346,z2,z3,z5,z6]),(0,[z66,z0,z2,z3,z477,z6]),(0,[z0,z2,z3,z4,z500,z6]),(0,[z0,z2,z3,z4,z61,z100])],[(0,[z0,z2,z3,z4,z971,z6]),(0,[z0,z2,z3,z972,z5,z6]),(0,[z0,z2,z3,z5,z56,z779]),(0,[z0,z2,z3,z5,z6,z973]),(0,[z0,z2,z3,z218,z5,z6]),(0,[z0,z2,z3,z974,z5,z6])],[(0,[z0,z227,z3,z4,z140,z6]),(0,[z0,z2,z3,z13,z5,z565]),(0,[z0,z2,z3,z82,z5,z29]),(0,[z66,z0,z2,z3,z484,z5]),(0,[z0,z22,z57,z12,z5,z6]),(0,[z0,z2,z3,z13,z941,z5])],[(0,[z0,z2,z3,z4,z5,z975]),(0,[z0,z2,z3,z976,z5,z6]),(0,[z275,z0,z205,z3,z5,z6]),(0,[z121,z0,z2,z35,z5,z6]),(0,[z346,z2,z3,z4,z477,z6])],[(0,[z66,z0,z3,z562,z5,z6]),(0,[z0,z2,z3,z35,z5,z402]),(0,[z133,z2,z3,z4,z5,z415]),(0,[z0,z2,z3,z13,z5,z469]),(0,[z0,z2,z3,z4,z977,z6]),(0,[z66,z0,z2,z3,z61,z100]),(0,[z0,z85,z3,z4,z203,z19]),(0,[z293,z0,z2,z4,z122,z6]),(0,[z0,z2,z3,z978,z5,z6])],[(0,[z0,z2,z3,z4,z5,z979]),(0,[z0,z2,z3,z5,z29,z980]),(0,[z0,z2,z3,z359,z5,z284]),(0,[z263,z2,z3,z4,z5,z981]),(0,[z71,z0,z25,z4,z5,z456]),(0,[z982,z2,z3,z4,z5,z6]),(0,[z120,z2,z3,z4,z425,z5])],[(0,[z10,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z402]),(0,[z0,z2,z3,z4,z140,z56]),(0,[z0,z2,z34,z35,z5,z6]),(0,[z0,z2,z3,z983,z5,z6])],[(0,[z0,z2,z3,z4,z140,z475]),(0,[z984,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z985,z5,z6]),(0,[z0,z2,z3,z4,z5,z986]),(0,[z75,z2,z3,z13,z5,z56]),(0,[z399,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z987,z5,z6]),(0,[z95,z0,z3,z4,z5,z90])],[(0,[z0,z2,z988,z4,z5,z6]),(0,[z0,z85,z3,z4,z19,z56]),(0,[z2,z3,z4,z197,z5,z56])]],
   [[(0,[z0,z2,z3,z989,z5,z6]),(0,[z66,z0,z2,z3,z5,z402]),(0,[z0,z2,z3,z990,z5,z6]),(0,[z66,z0,z2,z3,z5,z870]),(0,[z0,z22,z361,z3,z5,z6]),(0,[z0,z2,z3,z35,z5,z381]),(1,[z0,z2,z3,z771,z6]),(0,[z0,z2,z3,z4,z5,z991])],[(0,[z0,z2,z3,z992,z5,z6]),(0,[z0,z2,z3,z4,z5,z993]),(0,[z0,z2,z3,z4,z356,z100]),(0,[z0,z2,z3,z13,z477,z6]),(0,[z0,z2,z3,z35,z5,z879])],[(0,[z33,z0,z2,z3,z5,z373]),(0,[z346,z509,z3,z4,z5,z6]),(0,[z994,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z995])],[(0,[z187,z0,z3,z126,z5,z6]),(0,[z22,z2,z3,z5,z29,z56]),(0,[z0,z2,z3,z98,z92,z56]),(0,[z0,z2,z3,z996,z5,z6]),(0,[z997,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z35,z5,z310]),(0,[z0,z2,z3,z998,z5,z6]),(0,[z880,z2,z3,z4,z5,z6])],[(0,[z999,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z1000,z5,z6]),(0,[z0,z2,z3,z35,z5,z415]),(0,[z66,z0,z333,z3,z5,z6]),(0,[z66,z434,z0,z3,z5,z6]),(0,[z0,z2,z3,z396,z5,z29]),(0,[z0,z2,z3,z5,z6,z980]),(0,[z0,z2,z113,z34,z5,z6])],[(0,[z698,z2,z3,z4,z5,z56]),(0,[z459,z2,z64,z4,z5,z6]),(0,[z0,z2,z3,z1001,z5,z6]),(0,[z66,z0,z2,z3,z5,z381]),(0,[z1002,z2,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z831,z27]),(0,[z0,z2,z3,z5,z844,z93]),(0,[z2,z3,z4,z425,z5,z93])],[(0,[z603,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z415]),(0,[z0,z2,z3,z13,z5,z863])],[(0,[z39,z2,z3,z126,z5,z29]),(0,[z0,z2,z3,z4,z828,z6]),(0,[z0,z3,z13,z5,z6,z1003])],[(0,[z0,z2,z3,z68,z5,z29]),(0,[z0,z2,z3,z1004,z5,z6]),(0,[z26,z0,z22,z2,z5,z27]),(0,[z0,z2,z3,z421,z5,z6]),(0,[z110,z2,z3,z21,z5,z6])],[(0,[z0,z509,z3,z13,z5,z6])],[(0,[z66,z0,z2,z3,z5,z415]),(0,[z441,z0,z3,z4,z5,z559]),(0,[z234,z0,z2,z3,z35,z5]),(0,[z0,z2,z1005,z3,z5,z6])],[(0,[z71,z0,z323,z25,z5,z6])],[(0,[z904,z115,z3,z4,z5,z6]),(0,[z308,z2,z3,z4,z63,z6]),(0,[z0,z2,z149,z4,z5,z412]),(0,[z71,z66,z0,z25,z5,z6]),(0,[z0,z3,z799,z119,z5,z6]),(0,[z0,z2,z3,z4,z5,z837])],[(0,[z0,z2,z3,z4,z5,z1006]),(0,[z0,z414,z149,z4,z5,z6]),(0,[z1007,z2,z3,z4,z5,z6]),(0,[z0,z2,z52,z107,z5,z53])],[(0,[z0,z2,z3,z1008,z5,z6]),(0,[z0,z2,z3,z35,z5,z895])]],
   [[(0,[z1009,z0,z2,z3,z5,z6]),(0,[z2,z3,z105,z4,z5,z56]),(0,[z89,z0,z2,z3,z5,z29]),(0,[z0,z2,z745,z13,z5,z6]),(0,[z346,z2,z3,z4,z5,z447]),(0,[z0,z1010,z2,z3,z5,z6])],[(0,[z0,z227,z3,z4,z5,z6]),(0,[z535,z187,z0,z3,z5,z6]),(0,[z114,z2,z3,z4,z5,z412]),(0,[z0,z22,z2,z3,z1011,z6]),(0,[z0,z2,z3,z13,z5,z381]),(0,[z26,z0,z2,z13,z5,z27]),(0,[z0,z2,z591,z13,z5,z6])],[(0,[z114,z414,z3,z4,z5,z6]),(0,[z66,z86,z2,z3,z5,z6]),(0,[z1012,z0,z2,z3,z13,z5])],[(0,[z0,z2,z3,z737,z4,z29]),(0,[z0,z57,z2,z34,z5,z6]),(0,[z1013,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1014]),(0,[z0,z2,z3,z1015,z5,z6]),(0,[z1016,z22,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z13,z5,z310]),(0,[z0,z414,z3,z4,z5,z29]),(0,[z0,z1017,z3,z4,z5,z6]),(0,[z1018,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1019,z6]),(0,[z0,z2,z3,z4,z5,z475]),(0,[z0,z2,z3,z1020,z5,z6]),(0,[z0,z2,z3,z1021,z5,z6])],[(0,[z0,z1022,z3,z4,z5,z6]),(0,[z0,z2,z54,z3,z55,z29]),(0,[z0,z22,z2,z3,z144,z6]),(0,[z275,z0,z3,z5,z60,z6]),(0,[z616,z2,z3,z35,z5,z6])],[(0,[z0,z2,z149,z35,z5,z6]),(0,[z0,z2,z35,z13,z5,z29]),(0,[z0,z2,z3,z1023,z5,z6]),(0,[z0,z2,z76,z3,z203,z5])],[(0,[z616,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z195,z5,z6]),(0,[z0,z2,z3,z4,z1024,z5]),(0,[z0,z257,z3,z4,z5,z381])],[(0,[z66,z109,z592,z3,z5,z6]),(0,[z520,z2,z3,z4,z63,z6]),(0,[z1012,z0,z2,z3,z4,z5])],[(0,[z0,z2,z3,z1025,z5,z6]),(0,[z0,z2,z503,z4,z20,z6])],[(0,[z0,z341,z3,z4,z5,z56]),(0,[z0,z2,z3,z1026,z5,z6]),(0,[z0,z2,z3,z171,z5,z456]),(0,[z0,z361,z3,z4,z5,z381])],[(0,[z0,z2,z3,z1027,z5,z6]),(0,[z0,z57,z2,z225,z5,z6]),(0,[z219,z0,z2,z3,z117,z6]),(0,[z66,z0,z552,z3,z5,z6]),(0,[z86,z2,z3,z4,z5,z78]),(0,[z0,z2,z3,z50,z5,z594])],[(0,[z0,z2,z3,z1028,z5,z6]),(0,[z0,z2,z3,z13,z5,z327]),(0,[z0,z2,z3,z1029,z5,z6]),(0,[z256,z57,z3,z4,z5,z6]),(0,[z0,z1030,z3,z4,z5,z6])],[(0,[z115,z22,z111,z3,z5,z6]),(0,[z0,z2,z3,z1031,z5,z6]),(0,[z0,z2,z3,z4,z5,z1032]),(0,[z148,z2,z3,z4,z123,z6]),(0,[z0,z2,z3,z35,z5,z29]),(0,[z0,z2,z554,z13,z5,z6]),(0,[z1033,z2,z3,z4,z5,z6])]],
   [[(0,[z30,z2,z64,z4,z5,z29]),(0,[z308,z2,z3,z4,z5,z56]),(0,[z71,z0,z25,z35,z5,z6]),(0,[z0,z2,z3,z4,z5,z1034]),(0,[z0,z2,z3,z771,z5,z6])],[(0,[z1035,z2,z3,z4,z5,z6])],[(0,[z2,z250,z3,z4,z5,z56]),(0,[z0,z22,z2,z3,z67,z70]),(0,[z0,z2,z3,z4,z5,z1036]),(0,[z0,z2,z3,z98,z92,z179])],[(0,[z0,z9,z3,z84,z5,z6]),(0,[z0,z2,z3,z4,z5,z1037]),(0,[z464,z2,z3,z4,z5,z6]),(0,[z1038,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z139,z5,z6]),(0,[z0,z2,z1039,z3,z5,z6]),(0,[z66,z0,z3,z342,z5,z6]),(0,[z0,z2,z3,z13,z5,z907])],[(0,[z66,z0,z2,z3,z5,z29]),(0,[z0,z1040,z2,z3,z5,z6])],[(0,[z147,z2,z3,z4,z5,z56]),(0,[z243,z0,z2,z4,z5,z158]),(0,[z0,z2,z3,z4,z5,z1041]),(0,[z1042,z2,z3,z4,z5,z6])],[(0,[z227,z3,z64,z4,z5,z6]),(0,[z353,z2,z3,z4,z5,z29]),(1,[z0,z2,z4,z969,z6])],[(0,[z0,z2,z149,z4,z5,z221]),(0,[z343,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z1043,z5,z6]),(0,[z0,z2,z3,z4,z5,z1044]),(0,[z66,z0,z22,z3,z5,z6]),(0,[z166,z0,z2,z267,z5,z6])],[(0,[z0,z2,z149,z13,z5,z6]),(0,[z2,z3,z4,z5,z262,z56]),(0,[z0,z22,z2,z3,z175,z6])],[(0,[z0,z2,z3,z1045,z5,z6]),(0,[z86,z2,z72,z4,z5,z6])],[(0,[z0,z1046,z3,z4,z5,z6]),(0,[z0,z2,z195,z261,z5,z6]),(0,[z0,z2,z72,z4,z20,z56]),(0,[z66,z298,z2,z3,z5,z6]),(0,[z1047,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z774,z5]),(0,[z1048,z0,z2,z3,z5,z6]),(0,[z86,z2,z4,z5,z122,z6]),(0,[z0,z2,z3,z4,z271,z100])],[(0,[z0,z2,z3,z4,z5,z272]),(0,[z0,z2,z3,z1049,z4,z5]),(0,[z0,z2,z3,z186,z5,z6]),(0,[z66,z0,z2,z3,z5,z1044]),(0,[z0,z2,z3,z1050,z5,z6]),(0,[z95,z194,z3,z4,z5,z90]),(0,[z0,z1051,z3,z4,z5,z6]),(0,[z0,z2,z3,z98,z771,z6])],[(1,[z66,z111,z3,z5,z56]),(0,[z0,z489,z3,z35,z5,z6]),(0,[z0,z1052,z3,z4,z5,z56]),(0,[z0,z2,z3,z1053,z5,z6])],[(0,[z30,z489,z64,z4,z5,z6]),(0,[z0,z22,z341,z3,z5,z6]),(0,[z0,z205,z3,z14,z5,z6]),(0,[z0,z2,z3,z771,z92,z6])],[(0,[z0,z2,z1054,z4,z5,z6]),(0,[z0,z2,z3,z82,z5,z56]),(0,[z830,z2,z3,z25,z4,z5])]],
   [[(0,[z0,z2,z3,z13,z5,z29]),(0,[z0,z2,z3,z1055,z5,z6])],[(0,[z71,z0,z25,z13,z5,z6]),(0,[z69,z22,z2,z3,z5,z6]),(0,[z0,z2,z4,z5,z53,z831])],[(0,[z0,z1056,z2,z3,z5,z6]),(0,[z0,z2,z3,z241,z5,z56]),(0,[z0,z2,z3,z1057,z5,z6]),(0,[z0,z2,z3,z50,z5,z124])],[(0,[z66,z109,z0,z3,z5,z6]),(0,[z673,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1058])],[(0,[z438,z0,z2,z3,z5,z206]),(0,[z791,z2,z3,z4,z5,z6]),(0,[z0,z313,z3,z416,z5,z6]),(0,[z0,z2,z3,z4,z5,z179]),(0,[z0,z2,z54,z3,z513,z6])],[(0,[z0,z2,z3,z4,z5,z1059]),(0,[z39,z2,z3,z304,z5,z6]),(0,[z256,z2,z3,z35,z5,z6]),(0,[z0,z22,z257,z3,z5,z6]),(0,[z0,z85,z3,z19,z170,z6]),(0,[z0,z2,z3,z505,z477,z6])],[(0,[z339,z0,z2,z3,z5,z6]),(0,[z458,z2,z64,z4,z5,z6]),(0,[z66,z0,z2,z1060,z5,z6])],[(0,[z115,z111,z3,z35,z5,z6]),(0,[z66,z133,z2,z3,z5,z56]),(0,[z0,z1061,z3,z4,z5,z6]),(0,[z151,z22,z2,z3,z164,z6]),(0,[z223,z66,z0,z2,z122,z6]),(0,[z0,z2,z3,z35,z500,z6]),(0,[z0,z2,z3,z35,z61,z100]),(0,[z0,z2,z3,z5,z1062,z6]),(0,[z26,z346,z2,z4,z5,z27]),(0,[z26,z0,z2,z4,z477,z27])],[(0,[z22,z2,z177,z3,z5,z56]),(0,[z298,z2,z3,z4,z5,z29]),(0,[z0,z257,z3,z4,z5,z29]),(0,[z0,z22,z2,z3,z5,z1063]),(0,[z0,z2,z72,z4,z969,z6]),(0,[z2,z3,z4,z425,z5,z53])],[(0,[z0,z2,z3,z159,z5,z29]),(0,[z109,z0,z3,z34,z5,z6]),(0,[z490,z2,z3,z4,z5,z56]),(0,[z194,z2,z3,z4,z5,z29]),(0,[z256,z3,z25,z4,z5,z6]),(0,[z0,z794,z25,z4,z5,z6]),(0,[z0,z1064,z2,z3,z5,z6])],[(0,[z47,z0,z22,z3,z48,z6])],[(0,[z0,z2,z3,z4,z5,z1065]),(0,[z0,z22,z204,z3,z5,z6]),(0,[z0,z361,z3,z4,z5,z29])],[(0,[z166,z0,z111,z3,z5,z6]),(0,[z0,z2,z3,z396,z5,z56]),(0,[z0,z2,z3,z4,z5,z1066]),(0,[z0,z509,z3,z4,z5,z53])],[(0,[z0,z2,z3,z4,z5,z1067]),(0,[z0,z22,z2,z3,z5,z315]),(0,[z0,z2,z3,z4,z5,z1068]),(0,[z2,z3,z4,z5,z56,z351]),(0,[z66,z0,z2,z3,z500,z6])],[(0,[z0,z489,z3,z13,z5,z6]),(0,[z30,z2,z64,z4,z5,z402]),(0,[z0,z2,z3,z4,z5,z1069]),(0,[z1070,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z170,z29]),(0,[z95,z0,z3,z4,z5,z817]),(0,[z0,z509,z3,z505,z5,z6])],[(0,[z0,z2,z3,z4,z1071,z6]),(0,[z0,z2,z3,z1072,z5,z6]),(0,[z133,z2,z28,z186,z5,z6]),(0,[z0,z2,z3,z4,z5,z1073]),(0,[z71,z0,z484,z25,z4,z5]),(0,[z0,z2,z323,z3,z5,z6]),(0,[z0,z2,z3,z1074,z5,z6]),(0,[z95,z0,z3,z35,z5,z90]),(0,[z1075,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z1076,z6]),(0,[z0,z2,z3,z68,z5,z56]),(0,[z0,z85,z3,z4,z19,z395])],[(0,[z1009,z0,z414,z3,z5,z6]),(0,[z0,z2,z3,z273,z5,z6]),(0,[z618,z0,z2,z3,z5,z431]),(0,[z0,z2,z3,z1077,z5,z6])],[(0,[z2,z28,z920,z4,z5,z6]),(0,[z148,z2,z3,z4,z63,z56]),(0,[z0,z2,z3,z1078,z5,z6]),(1,[z2,z3,z4,z5,z708]),(0,[z1079,z2,z3,z4,z5,z6]),(0,[z223,z0,z361,z4,z122,z6])],[(0,[z131,z2,z3,z139,z5,z56]),(0,[z26,z0,z2,z4,z5,z831])],[(0,[z226,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1080])],[(0,[z133,z2,z64,z4,z5,z56]),(0,[z0,z2,z3,z5,z56,z903]),(0,[z0,z2,z3,z4,z5,z11]),(0,[z0,z120,z509,z3,z4,z5]),(0,[z26,z0,z2,z505,z5,z27]),(0,[z0,z2,z3,z467,z4,z70])],[(0,[z633,z2,z3,z4,z5,z56]),(0,[z256,z2,z3,z13,z5,z6]),(0,[z0,z22,z2,z52,z5,z53]),(0,[z0,z85,z76,z3,z19,z6])],[(0,[z0,z2,z3,z4,z5,z1081]),(0,[z133,z227,z3,z4,z5,z6])],[(0,[z115,z111,z3,z13,z5,z6]),(0,[z592,z2,z3,z4,z5,z56]),(0,[z532,z0,z3,z4,z5,z90]),(0,[z0,z2,z3,z5,z6,z1082]),(0,[z0,z2,z3,z13,z500,z6]),(0,[z0,z2,z3,z13,z61,z100]),(0,[z346,z2,z3,z4,z5,z53])],[(0,[z428,z2,z3,z4,z63,z6]),(0,[z1083,z0,z2,z3,z5,z6]),(0,[z166,z0,z2,z3,z5,z29]),(0,[z66,z1084,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z78]),(0,[z0,z2,z3,z1085,z5,z6]),(0,[z0,z2,z3,z4,z5,z1086]),(0,[z0,z1087,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z844])],[(0,[z0,z2,z3,z1088,z5,z6]),(0,[z71,z0,z2,z225,z5,z6]),(0,[z0,z2,z3,z325,z92,z6]),(0,[z0,z2,z3,z4,z70,z627]),(0,[z0,z2,z3,z1089,z4,z5]),(0,[z346,z2,z3,z505,z5,z6])],[(0,[z0,z2,z3,z1090,z5,z6]),(0,[z133,z2,z3,z4,z5,z56]),(0,[z1091,z2,z3,z4,z5,z6]),(0,[z1092,z2,z3,z4,z5,z6]),(0,[z0,z205,z2,z42,z5,z6]),(0,[z121,z0,z2,z745,z5,z6]),(0,[z0,z2,z3,z98,z485,z6]),(0,[z2,z3,z4,z1093,z5,z6])],[(0,[z2,z317,z3,z4,z5,z56]),(0,[z0,z414,z3,z4,z5,z56]),(0,[z0,z2,z3,z5,z29,z58]),(0,[z0,z2,z3,z4,z771,z6])],[(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z204,z195,z4,z5,z6]),(0,[z234,z0,z2,z323,z3,z5]),(0,[z0,z2,z3,z70,z5,z62])],[(0,[z0,z2,z3,z13,z5,z402]),(0,[z0,z2,z54,z3,z55,z56]),(0,[z95,z0,z3,z5,z247,z90]),(0,[z464,z2,z3,z68,z5,z6]),(0,[z616,z2,z3,z4,z477,z6])],[(0,[z0,z2,z3,z4,z5,z38]),(0,[z0,z2,z3,z4,z743,z6]),(0,[z2,z216,z3,z4,z5,z56]),(0,[z0,z2,z35,z13,z5,z56]),(0,[z103,z592,z2,z3,z5,z6]),(0,[z0,z2,z200,z35,z5,z6]),(0,[z0,z2,z3,z4,z883,z6])]],
   [[(0,[z440,z111,z3,z4,z5,z6]),(0,[z2,z3,z64,z4,z5,z94]),(0,[z0,z43,z3,z4,z5,z6]),(0,[z66,z0,z3,z5,z6,z647]),(0,[z95,z0,z3,z13,z5,z90]),(0,[z0,z2,z1094,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1095]),(0,[z282,z2,z3,z4,z5,z56]),(0,[z47,z0,z3,z4,z48,z6])],[(0,[z0,z227,z3,z35,z5,z6]),(0,[z0,z2,z3,z1096,z5,z6]),(0,[z0,z2,z3,z4,z1097,z6]),(0,[z0,z2,z3,z752,z5,z56]),(0,[z0,z2,z3,z4,z5,z1098]),(0,[z0,z22,z43,z3,z5,z6])],[(0,[z66,z115,z111,z3,z5,z6]),(0,[z30,z227,z64,z4,z5,z6]),(0,[z0,z22,z2,z3,z5,z348]),(0,[z600,z0,z2,z35,z5,z6]),(0,[z75,z2,z3,z4,z5,z708]),(0,[z256,z2,z3,z4,z5,z456]),(0,[z263,z2,z3,z4,z144,z6]),(0,[z66,z2,z3,z425,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1099]),(0,[z0,z2,z3,z5,z124,z206]),(0,[z0,z22,z3,z229,z5,z6]),(0,[z0,z2,z3,z35,z5,z395])],[(0,[z0,z2,z54,z3,z188,z6]),(0,[z0,z2,z3,z5,z239,z93])],[(0,[z0,z2,z3,z35,z5,z56]),(0,[z0,z2,z3,z4,z477,z29]),(0,[z0,z2,z3,z1100,z5,z6]),(0,[z0,z2,z3,z5,z6,z58]),(0,[z0,z2,z3,z4,z5,z395])],[(0,[z0,z2,z3,z4,z1101,z6]),(0,[z0,z2,z3,z35,z5,z475]),(0,[z30,z2,z64,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1102]),(0,[z0,z2,z3,z4,z5,z1103]),(0,[z0,z1104,z3,z4,z5,z6]),(0,[z616,z509,z3,z4,z5,z6])],[(0,[z30,z2,z64,z4,z5,z475]),(0,[z129,z0,z2,z3,z5,z432]),(0,[z377,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z59,z5,z29]),(0,[z1105,z2,z3,z4,z5,z6]),(0,[z66,z0,z2,z1106,z5,z6]),(0,[z66,z464,z2,z3,z5,z6]),(0,[z0,z474,z22,z3,z5,z6]),(0,[z0,z2,z3,z1107,z5,z6])],[(0,[z0,z2,z3,z13,z5,z415]),(0,[z2,z3,z4,z102,z164,z56]),(0,[z2,z333,z3,z4,z5,z56]),(0,[z0,z2,z3,z1108,z5,z6])],[(0,[z1109,z0,z3,z4,z5,z6]),(0,[z66,z0,z2,z3,z5,z395]),(0,[z275,z0,z3,z119,z5,z6]),(0,[z0,z2,z3,z4,z5,z1110])],[(0,[z2,z3,z4,z425,z5,z29]),(0,[z1111,z0,z2,z3,z5,z6]),(0,[z69,z2,z3,z67,z4,z70])],[(0,[z428,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z1112]),(0,[z0,z2,z76,z3,z5,z6]),(0,[z1113,z2,z3,z4,z5,z6]),(0,[z0,z1114,z2,z3,z5,z6])],[(0,[z66,z0,z2,z3,z5,z475]),(0,[z2,z3,z35,z164,z5,z56]),(0,[z0,z2,z3,z273,z5,z456]),(0,[z0,z2,z3,z1115,z5,z6])],[(0,[z285,z2,z28,z4,z5,z6]),(0,[z263,z22,z2,z3,z5,z6]),(0,[z66,z0,z330,z3,z5,z6]),(0,[z1116,z2,z3,z4,z5,z6])],[(0,[z86,z2,z3,z4,z5,z6]),(0,[z0,z509,z3,z4,z5,z29]),(0,[z0,z22,z3,z84,z5,z6])]],
   [[],[(0,[z0,z2,z149,z998,z5,z6]),(0,[z0,z872,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z1117])],[(0,[z1118,z0,z2,z3,z5,z6]),(0,[z0,z2,z4,z969,z122,z6])],[(0,[z0,z2,z3,z4,z5,z1119]),(0,[z0,z227,z3,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z1120]),(0,[z0,z1121,z3,z4,z5,z6]),(0,[z0,z2,z3,z35,z5,z1036]),(0,[z0,z257,z3,z421,z5,z6])],[(0,[z66,z111,z3,z5,z6,z56]),(0,[z0,z2,z3,z171,z5,z29]),(0,[z0,z2,z3,z505,z5,z29]),(0,[z464,z2,z3,z35,z5,z6]),(0,[z0,z2,z3,z4,z500,z27])],[(0,[z904,z111,z3,z4,z5,z6]),(0,[z644,z2,z64,z4,z5,z6]),(0,[z0,z2,z238,z35,z5,z6]),(0,[z0,z2,z3,z5,z789,z56]),(0,[z263,z2,z3,z4,z175,z6]),(0,[z71,z0,z25,z171,z5,z6]),(0,[z0,z2,z3,z13,z5,z395]),(0,[z0,z1122,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z1123,z6])],[(0,[z0,z2,z1106,z4,z5,z6]),(0,[z878,z0,z2,z3,z5,z29]),(0,[z66,z0,z687,z3,z5,z6]),(0,[z0,z2,z3,z4,z1124,z6])],[(0,[z2,z3,z920,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z56]),(0,[z0,z2,z3,z4,z61,z378]),(0,[z0,z2,z1125,z3,z5,z6])],[(0,[z109,z0,z24,z3,z5,z6]),(0,[z0,z2,z3,z13,z5,z475]),(0,[z0,z1126,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1127]),(0,[z0,z2,z3,z1128,z5,z6])],[(0,[z0,z111,z3,z34,z5,z6]),(0,[z1129,z0,z2,z3,z5,z6]),(0,[z0,z2,z13,z5,z6,z676]),(0,[z0,z2,z3,z5,z1130,z6])],[(0,[z2,z3,z64,z4,z163,z6]),(0,[z0,z2,z3,z4,z1131,z5]),(0,[z71,z256,z25,z4,z5,z6]),(0,[z66,z0,z509,z3,z5,z6]),(0,[z0,z2,z446,z13,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1132]),(0,[z0,z22,z2,z3,z163,z6]),(0,[z0,z2,z3,z4,z5,z1133]),(0,[z0,z2,z3,z1134,z5,z6]),(0,[z459,z0,z2,z4,z5,z27]),(0,[z346,z2,z3,z4,z5,z29]),(0,[z256,z2,z3,z4,z5,z849]),(0,[z0,z2,z3,z4,z5,z981]),(0,[z0,z2,z1135,z3,z5,z6]),(0,[z1136,z0,z2,z3,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1138,z5,z6]),(0,[z616,z2,z3,z13,z5,z6]),(0,[z211,z0,z2,z3,z5,z174])],[(0,[z1139,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1140]),(0,[z0,z2,z3,z4,z1141,z5])],[(0,[z0,z2,z3,z35,z5,z272]),(0,[z0,z2,z3,z1142,z5,z6]),(0,[z2,z64,z4,z5,z122,z56]),(0,[z0,z2,z3,z4,z969,z6])],[(0,[z0,z489,z3,z4,z5,z402]),(0,[z40,z341,z3,z101,z5,z6]),(0,[z0,z2,z3,z1143,z5,z6]),(0,[z47,z0,z3,z241,z48,z6]),(0,[z0,z2,z3,z106,z55,z6]),(0,[z0,z2,z3,z1144,z5,z6]),(0,[z0,z2,z3,z4,z36,z100])],[(0,[z298,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z599,z5,z29]),(0,[z0,z257,z3,z4,z5,z56]),(0,[z0,z1145,z3,z4,z5,z6]),(0,[z0,z57,z3,z4,z5,z11]),(0,[z0,z2,z72,z34,z5,z6]),(0,[z0,z2,z3,z4,z1146,z6])]],
   [[(0,[z194,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z72,z20,z6]),(0,[z1147,z0,z3,z4,z5,z6]),(0,[z1148,z0,z257,z3,z5,z6]),(0,[z0,z2,z3,z67,z4,z413])],[(0,[z111,z3,z4,z5,z311,z56]),(0,[z0,z2,z3,z4,z5,z1149])],[(0,[z0,z22,z2,z3,z140,z6]),(0,[z0,z2,z3,z4,z5,z1150]),(0,[z0,z1151,z3,z4,z5,z6]),(0,[z0,z2,z3,z168,z92,z6]),(0,[z0,z2,z3,z4,z5,z1152]),(0,[z0,z2,z3,z4,z5,z1153])],[(0,[z66,z0,z2,z3,z5,z272]),(0,[z0,z2,z1154,z4,z5,z6]),(0,[z2,z177,z3,z4,z5,z56]),(0,[z258,z2,z3,z4,z5,z56]),(0,[z263,z2,z3,z4,z5,z1155]),(0,[z66,z0,z2,z3,z1146,z6])],[(0,[z0,z2,z3,z178,z163,z6]),(0,[z0,z1156,z2,z3,z5,z6]),(0,[z0,z1157,z3,z4,z5,z6]),(0,[z1158,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z125,z5,z6])],[(0,[z0,z1159,z3,z4,z5,z6]),(0,[z66,z0,z615,z3,z5,z6]),(0,[z0,z2,z3,z155,z4,z184]),(0,[z0,z2,z3,z4,z5,z890]),(0,[z464,z2,z3,z13,z5,z6]),(0,[z0,z2,z3,z35,z5,z179]),(0,[z1160,z0,z3,z4,z5,z6])],[(0,[z0,z2,z3,z1161,z5,z6]),(0,[z0,z1162,z3,z4,z5,z6]),(0,[z0,z2,z3,z1163,z5,z6]),(0,[z0,z2,z3,z50,z5,z624])],[(0,[z1164,z0,z2,z3,z5,z6]),(0,[z0,z85,z3,z4,z450,z6]),(0,[z0,z2,z3,z4,z900,z29]),(0,[z0,z2,z3,z5,z1165,z6]),(0,[z223,z0,z257,z4,z122,z6]),(0,[z1166,z0,z2,z3,z4,z5]),(0,[z0,z509,z3,z4,z500,z6])],[(0,[z0,z2,z1167,z4,z5,z6])],[(0,[z0,z2,z3,z4,z1168,z6]),(0,[z0,z204,z3,z261,z5,z6]),(0,[z0,z2,z3,z4,z5,z894]),(0,[z0,z2,z3,z1169,z5,z6]),(0,[z0,z2,z13,z5,z694,z6])],[(0,[z2,z111,z3,z4,z5,z240]),(0,[z0,z1170,z3,z4,z5,z6]),(0,[z256,z2,z3,z171,z5,z6]),(0,[z0,z2,z3,z4,z500,z53])],[(0,[z0,z2,z3,z178,z140,z6]),(0,[z0,z2,z149,z921,z5,z6]),(0,[z66,z0,z120,z3,z5,z60]),(0,[z66,z0,z2,z3,z5,z179])],[(0,[z339,z2,z111,z3,z5,z56]),(0,[z66,z0,z111,z3,z5,z29]),(0,[z0,z2,z3,z4,z5,z1171]),(0,[z0,z257,z3,z4,z122,z6])],[(0,[z275,z0,z57,z3,z5,z6]),(0,[z1016,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1172,z5,z6]),(0,[z0,z2,z3,z1173,z5,z6]),(0,[z464,z257,z3,z4,z5,z6])],[(0,[z0,z2,z3,z13,z5,z272]),(0,[z0,z1174,z3,z4,z5,z6]),(0,[z0,z2,z248,z13,z5,z6]),(0,[z0,z2,z149,z4,z5,z29]),(0,[z0,z1175,z2,z3,z4,z5]),(0,[z26,z0,z2,z4,z500,z27]),(0,[z2,z3,z4,z425,z61,z5])],[]],
   [[(0,[z0,z1176,z2,z3,z5,z6]),(0,[z166,z0,z2,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z1177]),(0,[z464,z361,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1178]),(0,[z2,z3,z4,z5,z56,z443]),(0,[z0,z2,z3,z4,z5,z1179]),(0,[z66,z0,z3,z538,z5,z6])],[(0,[z111,z3,z25,z4,z5,z56]),(0,[z39,z2,z3,z126,z5,z56]),(0,[z187,z0,z22,z3,z5,z6]),(0,[z114,z2,z3,z4,z5,z29])],[(0,[z71,z0,z2,z34,z5,z6]),(0,[z1180,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z1181,z5,z6]),(0,[z346,z2,z3,z4,z500,z6])],[(0,[z1182,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z96,z163,z6]),(0,[z2,z64,z4,z5,z163,z6]),(0,[z66,z0,z663,z3,z5,z6]),(0,[z459,z0,z2,z4,z5,z411]),(0,[z917,z2,z3,z4,z5,z6]),(0,[z71,z234,z0,z25,z4,z5]),(0,[z0,z2,z3,z1183,z5,z6]),(0,[z0,z2,z3,z50,z5,z844])],[(0,[z148,z2,z195,z4,z63,z6]),(0,[z1184,z0,z43,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1185])],[(0,[z66,z131,z2,z3,z5,z56]),(0,[z2,z3,z4,z5,z528,z56]),(0,[z2,z3,z409,z4,z5,z56]),(0,[z71,z0,z25,z4,z5,z29]),(0,[z0,z2,z3,z35,z5,z11]),(0,[z0,z2,z3,z13,z5,z179])],[(0,[z0,z2,z3,z4,z5,z1186]),(0,[z0,z2,z3,z1187,z5,z6]),(0,[z1188,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z314,z5,z93])],[(0,[z1189,z0,z2,z3,z5,z6]),(0,[z148,z22,z2,z3,z5,z56]),(0,[z0,z1190,z2,z3,z5,z6]),(0,[z2,z3,z4,z164,z5,z415])],[(0,[z0,z2,z3,z1191,z5,z6]),(0,[z2,z3,z4,z5,z743,z6])],[(0,[z0,z2,z3,z1192,z5,z6]),(0,[z89,z0,z2,z3,z5,z56]),(0,[z0,z3,z25,z4,z5,z11]),(0,[z0,z22,z2,z3,z203,z5]),(0,[z86,z2,z3,z68,z5,z6])],[(0,[z0,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z96,z140,z6]),(0,[z2,z3,z4,z184,z164,z6]),(0,[z0,z2,z3,z4,z5,z1193]),(0,[z223,z0,z2,z4,z122,z78])],[(0,[z133,z2,z3,z35,z5,z56]),(0,[z66,z0,z2,z3,z5,z11]),(0,[z86,z2,z3,z4,z5,z719]),(0,[z1194,z0,z2,z3,z5,z6])],[(0,[z0,z2,z3,z851,z5,z56]),(0,[z0,z2,z3,z4,z477,z56])],[(0,[z701,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z5,z1081]),(0,[z0,z2,z3,z799,z5,z6]),(0,[z0,z2,z3,z1195,z5,z6])],[(0,[z0,z2,z3,z59,z5,z56]),(0,[z0,z205,z2,z225,z5,z6]),(0,[z66,z0,z577,z3,z5,z6]),(0,[z95,z89,z0,z3,z5,z90])]],
   [[(0,[z0,z2,z3,z35,z5,z38]),(0,[z0,z2,z3,z940,z5,z29]),(0,[z1196,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1197])],[(0,[z66,z111,z3,z64,z5,z6]),(0,[z0,z2,z1198,z3,z5,z6]),(0,[z187,z0,z3,z101,z5,z6]),(0,[z0,z2,z3,z4,z1199,z5]),(0,[z0,z1200,z2,z3,z5,z6]),(0,[z1075,z2,z3,z13,z5,z6]),(0,[z0,z43,z3,z35,z5,z6]),(0,[z0,z2,z3,z421,z5,z381])],[(0,[z0,z9,z2,z3,z5,z6]),(0,[z2,z3,z4,z425,z5,z56]),(0,[z47,z0,z3,z35,z48,z6]),(0,[z0,z2,z3,z4,z727,z6])],[(0,[z0,z489,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z1201]),(0,[z0,z2,z3,z1202,z5,z6]),(0,[z2,z3,z426,z4,z5,z56]),(0,[z0,z2,z3,z1203,z5,z6]),(0,[z0,z22,z2,z3,z5,z1204]),(0,[z0,z2,z283,z13,z5,z6]),(0,[z0,z2,z3,z4,z5,z1205]),(0,[z0,z2,z3,z1206,z5,z6])],[(0,[z0,z22,z2,z3,z5,z94]),(0,[z0,z2,z3,z178,z5,z6]),(1,[z2,z920,z4,z5,z6]),(0,[z71,z263,z25,z4,z5,z6]),(0,[z0,z2,z52,z35,z5,z53])],[(0,[z0,z1207,z2,z3,z5,z6]),(0,[z66,z2,z3,z5,z29,z56]),(0,[z0,z2,z3,z4,z5,z1208]),(0,[z1084,z2,z3,z4,z5,z6])],[(0,[z66,z0,z2,z3,z5,z38]),(0,[z0,z2,z390,z13,z5,z6]),(0,[z0,z2,z1209,z4,z5,z6]),(0,[z2,z3,z4,z328,z5,z56]),(0,[z0,z509,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z1210,z6]),(0,[z0,z313,z57,z3,z5,z6]),(0,[z2,z3,z13,z425,z5,z6]),(0,[z0,z2,z52,z4,z5,z53])],[(1,[z2,z64,z4,z163,z6]),(0,[z0,z2,z3,z13,z5,z11]),(0,[z1211,z2,z3,z4,z5,z6]),(0,[z0,z2,z35,z564,z5,z6])],[(0,[z0,z111,z24,z3,z5,z6]),(0,[z30,z22,z2,z64,z5,z6]),(0,[z148,z2,z195,z4,z5,z56])],[(0,[z187,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z899,z5,z6]),(0,[z0,z120,z3,z4,z5,z193]),(0,[z66,z0,z2,z3,z5,z1098]),(0,[z0,z2,z3,z98,z117,z6])],[(0,[z0,z2,z3,z1212,z5,z6]),(0,[z166,z109,z0,z3,z5,z6]),(0,[z0,z1213,z3,z4,z5,z6]),(0,[z0,z2,z34,z5,z6,z27]),(0,[z1214,z2,z3,z4,z5,z6])],[(0,[z0,z2,z195,z4,z5,z6]),(0,[z0,z2,z3,z171,z5,z56]),(0,[z0,z2,z3,z505,z5,z56]),(0,[z256,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z1215,z5]),(0,[z0,z2,z3,z4,z962,z29]),(0,[z66,z0,z2,z3,z5,z1099]),(0,[z0,z2,z3,z13,z5,z1086])],[(0,[z0,z2,z3,z1216,z5,z6])],[(0,[z115,z111,z3,z4,z5,z29]),(0,[z428,z0,z2,z4,z122,z6]),(0,[z133,z2,z3,z13,z5,z56]),(0,[z0,z1217,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z29,z708]),(0,[z0,z2,z3,z4,z500,z29]),(0,[z1218,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z883,z61])],[(0,[z0,z2,z3,z218,z5,z29]),(0,[z234,z830,z2,z3,z4,z5])],[(0,[z0,z2,z455,z4,z5,z447]),(1,[z2,z3,z4,z784,z5]),(0,[z0,z2,z3,z1219,z5,z6]),(0,[z616,z2,z3,z505,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z966]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1220]),(0,[z151,z2,z3,z4,z164,z6]),(0,[z121,z0,z2,z35,z5,z29]),(0,[z71,z0,z24,z25,z5,z6]),(0,[z0,z22,z2,z3,z5,z357]),(0,[z86,z2,z3,z35,z5,z6])],[(0,[z0,z2,z3,z13,z5,z38]),(0,[z2,z3,z4,z5,z993,z56]),(0,[z0,z2,z3,z1221,z5,z6]),(0,[z23,z2,z64,z4,z5,z6]),(0,[z0,z2,z3,z4,z102,z100]),(0,[z0,z2,z3,z4,z5,z1222]),(0,[z0,z2,z3,z4,z5,z1223]),(0,[z0,z2,z3,z4,z5,z1224]),(0,[z0,z2,z3,z4,z20,z395]),(0,[z0,z2,z3,z4,z883,z100])],[(0,[z346,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z776,z5,z6]),(0,[z0,z43,z3,z13,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1225]),(0,[z0,z22,z2,z149,z5,z6]),(0,[z22,z2,z3,z164,z5,z56]),(0,[z0,z2,z3,z1226,z5,z6]),(0,[z0,z3,z4,z799,z5,z6]),(0,[z233,z0,z22,z3,z5,z6]),(0,[z47,z0,z3,z13,z48,z6]),(0,[z0,z3,z13,z5,z881,z6])],[(0,[z1227,z2,z3,z4,z5,z6])],[(0,[z502,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1228]),(0,[z66,z0,z2,z3,z5,z1222]),(0,[z0,z2,z52,z13,z5,z53]),(0,[z166,z0,z3,z538,z5,z6])],[(0,[z109,z0,z3,z241,z5,z6]),(0,[z0,z1229,z204,z3,z5,z6]),(0,[z71,z0,z25,z273,z5,z6]),(0,[z0,z2,z3,z91,z5,z6]),(0,[z0,z1230,z3,z4,z5,z6])],[(0,[z0,z2,z290,z13,z5,z6]),(0,[z2,z3,z4,z5,z6,z708]),(0,[z740,z2,z3,z4,z5,z6]),(0,[z0,z2,z113,z13,z5,z6]),(0,[z0,z2,z3,z5,z62,z6])],[],[(0,[z0,z2,z1231,z3,z5,z6]),(0,[z231,z0,z2,z3,z5,z495]),(0,[z0,z2,z3,z5,z1232,z6]),(0,[z0,z361,z3,z421,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1233]),(0,[z133,z2,z266,z4,z5,z6]),(0,[z40,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z1234,z5,z6]),(0,[z0,z2,z3,z4,z5,z1235]),(0,[z86,z2,z3,z4,z20,z6]),(0,[z0,z1236,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1237]),(0,[z0,z2,z3,z1238,z5,z6]),(0,[z234,z0,z2,z3,z13,z5]),(0,[z464,z2,z3,z4,z5,z381]),(0,[z0,z1239,z3,z4,z5,z6]),(0,[z26,z0,z509,z4,z5,z27])],[(0,[z0,z2,z3,z4,z5,z1240]),(0,[z445,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z1241,z5]),(0,[z1242,z2,z3,z4,z5,z6])],[(0,[z0,z2,z1243,z4,z5,z6]),(0,[z0,z2,z429,z4,z20,z6]),(0,[z2,z3,z4,z5,z708,z56]),(0,[z0,z2,z3,z4,z5,z912]),(0,[z0,z2,z3,z67,z13,z70])],[(0,[z39,z147,z2,z3,z5,z6]),(0,[z0,z2,z3,z225,z5,z6])],[(0,[z0,z2,z3,z1244,z5,z6]),(0,[z0,z2,z52,z4,z5,z329])]],
   [[(0,[z0,z2,z3,z1245,z5,z6]),(0,[z0,z2,z3,z421,z5,z29]),(0,[z66,z0,z361,z3,z5,z6]),(0,[z0,z2,z3,z1246,z5,z6])],[(0,[z148,z2,z3,z261,z63,z6]),(0,[z0,z2,z3,z1247,z4,z5]),(0,[z66,z1007,z2,z3,z5,z6]),(0,[z400,z0,z2,z225,z5,z6]),(0,[z86,z2,z3,z13,z5,z6]),(0,[z1147,z0,z3,z35,z5,z6])],[(0,[z0,z830,z2,z3,z4,z5])],[(0,[z547,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z159,z5,z56]),(0,[z234,z0,z2,z3,z4,z5]),(1,[z86,z2,z4,z122,z6])],[(0,[z2,z366,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z1248,z6]),(0,[z423,z0,z22,z3,z5,z6]),(0,[z0,z2,z3,z1249,z5,z6])],[(0,[z0,z1250,z2,z3,z5,z6]),(0,[z0,z2,z195,z82,z5,z6]),(0,[z0,z2,z149,z4,z5,z56]),(0,[z0,z361,z3,z4,z5,z56]),(0,[z0,z2,z3,z55,z481,z6]),(0,[z0,z2,z3,z4,z382,z100])],[(0,[z0,z1251,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z170,z395]),(0,[z1252,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z62,z100])],[(0,[z0,z2,z3,z4,z5,z1253]),(0,[z0,z1254,z3,z4,z5,z6]),(0,[z375,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z1255,z4,z5]),(0,[z0,z2,z3,z670,z5,z93])],[(0,[z0,z227,z3,z4,z5,z29]),(0,[z148,z22,z2,z3,z63,z6]),(0,[z0,z2,z3,z5,z170,z56])],[(0,[z0,z2,z3,z4,z5,z1256]),(0,[z0,z2,z3,z5,z709,z6]),(0,[z0,z2,z323,z3,z484,z5]),(0,[z0,z3,z4,z19,z727,z6]),(0,[z86,z257,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1257])],[(0,[z0,z22,z3,z132,z5,z6]),(0,[z269,z22,z2,z3,z5,z56]),(0,[z0,z2,z3,z484,z35,z5]),(0,[z0,z2,z3,z1258,z5,z6])],[(0,[z0,z2,z3,z812,z5,z6]),(0,[z407,z2,z3,z4,z5,z56]),(0,[z0,z2,z104,z13,z5,z6]),(0,[z0,z2,z679,z35,z5,z6]),(0,[z0,z2,z4,z5,z6,z831])],[(0,[z0,z2,z3,z4,z5,z1259]),(0,[z0,z2,z3,z4,z5,z1260]),(0,[z0,z2,z3,z4,z5,z708]),(0,[z0,z57,z3,z4,z175,z6]),(0,[z0,z313,z3,z84,z5,z6]),(0,[z86,z361,z3,z4,z5,z6]),(0,[z0,z2,z72,z91,z20,z6])],[(0,[z0,z1261,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1262]),(0,[z71,z0,z25,z4,z5,z56]),(0,[z0,z2,z3,z4,z1011,z6]),(0,[z0,z2,z3,z5,z1263,z6])],[(0,[z0,z2,z3,z50,z5,z128]),(0,[z1184,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z13,z1141,z5]),(0,[z0,z2,z386,z35,z5,z6])],[(0,[z0,z2,z3,z1264,z5,z6]),(0,[z0,z2,z3,z1265,z5,z6]),(0,[z2,z3,z195,z4,z63,z6]),(0,[z0,z2,z3,z505,z500,z6])]],
   [[(0,[z2,z3,z101,z899,z5,z6]),(0,[z616,z2,z3,z4,z5,z29])],[(0,[z2,z3,z4,z480,z5,z56]),(0,[z451,z2,z3,z101,z5,z6]),(0,[z0,z22,z2,z3,z5,z412]),(0,[z0,z2,z52,z4,z5,z831])],[(0,[z0,z2,z3,z4,z1266,z6]),(0,[z66,z0,z871,z3,z5,z6]),(0,[z2,z3,z4,z743,z63,z6]),(0,[z0,z2,z3,z142,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1267]),(0,[z0,z22,z2,z3,z5,z453]),(0,[z114,z2,z3,z35,z5,z29]),(0,[z0,z2,z3,z4,z144,z6]),(0,[z0,z2,z3,z1268,z5,z6]),(0,[z2,z3,z4,z784,z19,z5]),(0,[z0,z2,z3,z5,z6,z1269])],[(0,[z0,z2,z28,z34,z5,z6]),(0,[z148,z2,z3,z261,z5,z56]),(0,[z66,z695,z0,z3,z5,z6]),(0,[z0,z2,z3,z1270,z5,z6]),(0,[z0,z354,z3,z4,z19,z6])],[(0,[z0,z2,z3,z4,z5,z1271]),(0,[z66,z1272,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z1273,z6])],[(0,[z0,z2,z3,z1274,z5,z6]),(0,[z210,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z5,z1275,z6]),(0,[z0,z2,z3,z4,z1276,z5]),(0,[z66,z0,z2,z3,z1266,z6]),(0,[z66,z0,z3,z119,z5,z6]),(0,[z1148,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z1277,z5,z6])],[(0,[z263,z2,z3,z4,z5,z6]),(0,[z1278,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z261,z5,z6]),(0,[z2,z3,z492,z4,z5,z56]),(0,[z2,z3,z405,z4,z5,z56]),(0,[z0,z2,z3,z50,z5,z533]),(0,[z0,z2,z3,z1279,z5,z6]),(0,[z0,z2,z3,z4,z1280,z6])],[(0,[z0,z2,z3,z1281,z5,z6]),(0,[z0,z43,z3,z4,z477,z6])],[(0,[z0,z2,z3,z1282,z5,z6]),(0,[z66,z0,z2,z195,z5,z6]),(0,[z0,z2,z3,z265,z5,z6]),(0,[z0,z2,z3,z1283,z5,z6])],[(0,[z0,z2,z3,z1284,z5,z6]),(0,[z0,z489,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z790]),(0,[z464,z2,z3,z4,z5,z29]),(0,[z66,z699,z0,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z1285]),(0,[z0,z2,z3,z4,z5,z1286]),(0,[z0,z2,z3,z106,z160,z6]),(0,[z1287,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z139,z5,z29]),(0,[z0,z489,z3,z4,z5,z475]),(0,[z0,z2,z3,z171,z5,z11]),(0,[z0,z2,z3,z4,z5,z1288]),(0,[z0,z2,z3,z4,z81,z100])],[(0,[z1289,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z162,z5,z6]),(0,[z0,z2,z3,z35,z5,z1193]),(0,[z0,z2,z3,z35,z67,z70]),(0,[z0,z820,z509,z3,z5,z6]),(0,[z0,z1290,z3,z4,z5,z6])],[],[(0,[z0,z1291,z3,z4,z5,z6]),(0,[z0,z1292,z3,z4,z5,z6]),(0,[z276,z2,z3,z4,z5,z29]),(0,[z66,z47,z0,z3,z48,z6])],[(0,[z0,z1293,z3,z4,z5,z6]),(0,[z66,z0,z22,z3,z5,z29]),(0,[z0,z2,z3,z1043,z5,z29]),(0,[z275,z0,z2,z3,z5,z6]),(0,[z0,z2,z534,z4,z5,z53])]],
   [[(0,[z0,z2,z3,z4,z5,z1294]),(0,[z251,z0,z2,z3,z481,z6]),(0,[z0,z2,z3,z1295,z5,z6])],[(0,[z0,z2,z195,z4,z5,z412]),(0,[z66,z616,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z769]),(0,[z0,z2,z3,z1296,z5,z6]),(0,[z0,z1297,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z70,z883])],[(0,[z0,z414,z195,z4,z5,z6]),(0,[z2,z3,z195,z4,z5,z56]),(0,[z256,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z67,z70]),(0,[z0,z2,z3,z4,z5,z817])],[(0,[z0,z2,z3,z186,z5,z29]),(0,[z148,z204,z3,z4,z63,z6]),(0,[z0,z2,z3,z35,z175,z6]),(0,[z1298,z2,z3,z4,z5,z6]),(0,[z0,z2,z24,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1299])],[(0,[z115,z111,z3,z4,z5,z56]),(0,[z131,z2,z3,z4,z5,z240]),(0,[z0,z1300,z3,z4,z5,z6]),(0,[z0,z2,z3,z1301,z5,z6]),(0,[z114,z2,z3,z13,z5,z29])],[(0,[z0,z2,z3,z218,z5,z56]),(0,[z0,z2,z3,z4,z175,z6]),(0,[z0,z2,z3,z1302,z5,z6])],[(0,[z0,z111,z3,z241,z5,z6]),(0,[z0,z227,z3,z4,z5,z402]),(0,[z30,z2,z64,z178,z5,z6]),(0,[z40,z2,z3,z101,z5,z565]),(0,[z2,z3,z4,z1303,z5,z6]),(0,[z0,z43,z3,z505,z5,z6])],[(0,[z0,z2,z3,z1304,z5,z6]),(0,[z121,z0,z2,z35,z5,z56]),(0,[z0,z2,z455,z4,z5,z53]),(0,[z0,z3,z25,z4,z175,z6]),(0,[z33,z0,z2,z3,z5,z495]),(0,[z1047,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z1305,z6])],[(0,[z2,z3,z13,z5,z29,z56]),(0,[z0,z2,z3,z1306,z5,z6]),(0,[z0,z2,z3,z4,z5,z1307]),(0,[z508,z0,z2,z3,z493,z6]),(0,[z616,z2,z3,z4,z500,z6]),(0,[z0,z2,z3,z4,z5,z844])],[(0,[z2,z3,z4,z164,z5,z56]),(0,[z66,z0,z2,z3,z175,z6]),(0,[z699,z0,z3,z4,z48,z6]),(0,[z0,z2,z1308,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1309]),(0,[z66,z109,z0,z3,z5,z29]),(0,[z187,z0,z3,z35,z5,z6]),(0,[z0,z2,z3,z5,z6,z1310])],[(0,[z0,z2,z3,z4,z5,z1311]),(0,[z66,z0,z177,z3,z5,z6]),(0,[z0,z2,z460,z13,z5,z6])],[(0,[z0,z204,z3,z4,z5,z412]),(0,[z0,z2,z195,z35,z5,z6]),(0,[z0,z22,z2,z3,z5,z221]),(0,[z539,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z1312,z5,z6]),(0,[z0,z2,z3,z4,z5,z888])],[(0,[z339,z0,z2,z3,z5,z29]),(0,[z69,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z817,z90]),(0,[z346,z43,z3,z4,z5,z6]),(0,[z0,z3,z4,z1313,z5,z6]),(0,[z0,z1314,z3,z4,z5,z6])],[(0,[z66,z0,z341,z3,z5,z6]),(0,[z440,z0,z3,z4,z5,z127])],[(0,[z0,z2,z1315,z4,z5,z6]),(0,[z234,z0,z22,z2,z3,z5]),(0,[z0,z2,z3,z1316,z5,z6])]],
   [[(0,[z1317,z0,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1318]),(0,[z0,z2,z3,z4,z5,z1319])],[(0,[z151,z2,z3,z35,z164,z6]),(0,[z0,z2,z3,z996,z5,z56])],[(0,[z0,z2,z3,z5,z6,z1320]),(0,[z0,z2,z3,z98,z92,z6]),(0,[z33,z0,z2,z3,z5,z844])],[(0,[z0,z2,z3,z1321,z5,z6]),(0,[z0,z2,z3,z4,z5,z1155]),(0,[z66,z0,z3,z660,z5,z6])],[(0,[z459,z2,z64,z4,z5,z56]),(0,[z0,z2,z3,z13,z175,z6]),(0,[z0,z2,z3,z4,z5,z1063]),(0,[z0,z2,z3,z4,z5,z1322]),(0,[z2,z3,z4,z1323,z5,z6])],[(0,[z66,z147,z2,z3,z5,z56]),(0,[z66,z0,z257,z3,z5,z6]),(0,[z0,z2,z3,z13,z5,z1205]),(0,[z1324,z0,z2,z3,z5,z6])],[(0,[z148,z204,z3,z4,z5,z56]),(0,[z2,z3,z4,z5,z56,z559]),(0,[z0,z2,z323,z3,z5,z29]),(0,[z26,z66,z0,z2,z5,z27]),(0,[z0,z2,z3,z1325,z5,z6]),(0,[z0,z2,z1060,z4,z5,z6]),(0,[z194,z22,z2,z3,z5,z6]),(0,[z0,z22,z3,z799,z5,z6])],[(0,[z0,z2,z3,z96,z5,z6]),(0,[z0,z2,z3,z4,z1326,z6]),(0,[z0,z22,z2,z3,z5,z240]),(0,[z0,z204,z3,z35,z5,z6]),(0,[z0,z2,z3,z34,z5,z6]),(0,[z0,z2,z3,z4,z5,z1327]),(0,[z86,z2,z3,z4,z5,z381])],[(0,[z0,z2,z3,z4,z1328,z5]),(0,[z0,z2,z195,z4,z164,z6]),(0,[z0,z2,z3,z273,z5,z29]),(0,[z0,z313,z2,z3,z5,z6]),(0,[z1329,z2,z3,z4,z5,z6]),(0,[z0,z2,z113,z745,z5,z6]),(0,[z865,z0,z361,z3,z5,z6]),(0,[z0,z1330,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z315]),(0,[z0,z204,z3,z4,z5,z6]),(0,[z0,z2,z3,z599,z5,z56]),(0,[z0,z2,z267,z35,z5,z6]),(0,[z0,z2,z13,z190,z5,z6]),(0,[z0,z2,z497,z4,z5,z53])],[(0,[z0,z871,z111,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1331]),(0,[z0,z22,z2,z3,z5,z456]),(0,[z0,z2,z3,z1332,z5,z6])],[(0,[z115,z111,z3,z4,z5,z272]),(0,[z187,z0,z3,z13,z5,z6]),(0,[z66,z0,z204,z3,z5,z6]),(0,[z0,z22,z2,z3,z5,z1333])],[(0,[z2,z64,z4,z5,z329,z56]),(1,[z2,z195,z4,z63,z6]),(0,[z0,z2,z195,z4,z5,z221])],[(0,[z0,z2,z3,z1334,z5,z6]),(0,[z131,z22,z2,z3,z5,z56]),(0,[z0,z2,z195,z13,z5,z6]),(0,[z71,z0,z25,z4,z5,z11]),(0,[z71,z0,z22,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z1335]),(0,[z0,z2,z3,z1336,z5,z6])],[(0,[z95,z298,z3,z4,z5,z90])],[(0,[z0,z2,z3,z4,z5,z1337]),(0,[z0,z1338,z2,z3,z5,z6]),(0,[z0,z227,z3,z4,z5,z56]),(0,[z66,z0,z643,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z922]),(0,[z0,z2,z3,z4,z883,z5])]],
   [[(0,[z0,z227,z3,z4,z5,z475]),(0,[z0,z2,z3,z4,z1339,z6]),(0,[z1188,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1340,z6]),(0,[z0,z1341,z43,z3,z5,z6])],[(0,[z2,z3,z4,z5,z447,z56]),(0,[z0,z1342,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z897,z6]),(0,[z0,z2,z3,z4,z175,z456])],[(0,[z0,z2,z3,z4,z5,z1343]),(0,[z151,z2,z3,z13,z164,z6]),(0,[z0,z2,z3,z228,z5,z6]),(0,[z0,z2,z3,z107,z5,z6]),(0,[z0,z2,z3,z189,z5,z124])],[(0,[z1344,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1345]),(0,[z0,z2,z3,z4,z5,z1346]),(0,[z40,z2,z3,z101,z5,z310]),(0,[z0,z2,z3,z4,z203,z5]),(0,[z1347,z0,z2,z3,z5,z6]),(0,[z704,z0,z2,z4,z5,z27])],[(0,[z0,z2,z28,z4,z163,z6]),(0,[z0,z2,z3,z4,z5,z1348])],[(0,[z0,z2,z3,z5,z29,z247]),(0,[z464,z2,z3,z421,z5,z6]),(0,[z0,z2,z3,z4,z5,z78]),(0,[z0,z2,z3,z585,z5,z124])],[(0,[z66,z0,z111,z3,z5,z56]),(0,[z0,z1229,z2,z3,z5,z6]),(0,[z66,z0,z2,z52,z5,z53])],[(0,[z0,z204,z3,z4,z5,z221]),(0,[z616,z2,z3,z4,z5,z56]),(0,[z0,z43,z3,z4,z5,z29]),(0,[z0,z2,z3,z98,z92,z357])],[(0,[z0,z204,z3,z13,z5,z6]),(0,[z0,z2,z195,z803,z5,z6]),(0,[z47,z0,z3,z4,z48,z29]),(0,[z0,z2,z3,z67,z4,z70])],[(0,[z0,z2,z3,z1096,z5,z29]),(0,[z0,z2,z3,z4,z1097,z29])],[(0,[z0,z2,z3,z1349,z5,z6]),(0,[z0,z22,z2,z3,z5,z565]),(0,[z66,z0,z313,z3,z5,z6])],[(0,[z0,z341,z3,z4,z5,z6]),(0,[z133,z2,z324,z4,z5,z6]),(0,[z277,z2,z3,z4,z5,z56]),(0,[z66,z0,z2,z3,z1248,z6]),(0,[z0,z2,z433,z13,z5,z6])],[(0,[z2,z111,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1350]),(0,[z151,z2,z3,z4,z480,z6]),(0,[z1351,z0,z2,z3,z5,z6]),(0,[z0,z22,z3,z5,z6,z551])],[(0,[z0,z2,z3,z4,z5,z94]),(0,[z0,z2,z3,z261,z5,z412])],[(0,[z0,z414,z3,z261,z5,z6]),(0,[z256,z2,z3,z273,z5,z6])],[(0,[z0,z2,z3,z4,z5,z348]),(0,[z0,z2,z3,z1352,z5,z6]),(0,[z0,z22,z414,z3,z5,z6]),(1,[z2,z195,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1353]),(0,[z0,z2,z3,z4,z1354,z5]),(0,[z0,z2,z3,z5,z6,z247])]],
   [[(0,[z275,z0,z3,z25,z5,z6]),(0,[z0,z2,z3,z4,z5,z1355]),(0,[z549,z2,z177,z3,z5,z6])],[(0,[z464,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z5,z1356])],[(0,[z0,z2,z3,z4,z5,z1357]),(0,[z0,z2,z3,z139,z5,z56]),(0,[z256,z2,z3,z4,z5,z11]),(0,[z2,z3,z4,z5,z935,z6]),(0,[z0,z2,z3,z5,z92,z179]),(0,[z1358,z0,z2,z3,z5,z6])],[(0,[z0,z204,z3,z82,z5,z6]),(0,[z0,z2,z76,z3,z5,z29]),(1,[z0,z3,z799,z5,z6]),(0,[z0,z22,z2,z3,z477,z6]),(0,[z2,z3,z4,z425,z5,z124])],[(0,[z2,z3,z4,z5,z1068,z56]),(0,[z0,z2,z3,z35,z144,z6])],[(0,[z0,z2,z3,z1359,z5,z6]),(0,[z0,z2,z3,z1360,z5,z6]),(0,[z0,z2,z3,z4,z5,z1361]),(0,[z0,z2,z3,z1362,z5,z6]),(0,[z95,z0,z2,z3,z4,z500])],[(0,[z0,z2,z1363,z3,z5,z6]),(0,[z0,z22,z3,z84,z5,z29]),(0,[z86,z2,z3,z4,z5,z29])],[(1,[z0,z3,z4,z727,z6]),(0,[z0,z2,z3,z67,z4,z883])],[(0,[z545,z2,z3,z4,z5,z56]),(0,[z187,z0,z3,z4,z5,z565]),(0,[z263,z2,z3,z35,z5,z6])],[(0,[z0,z1207,z414,z3,z5,z6]),(0,[z0,z22,z3,z5,z6,z488]),(0,[z1364,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z1365,z5,z6]),(0,[z364,z0,z2,z35,z5,z6])],[(0,[z133,z2,z3,z4,z163,z6]),(0,[z0,z2,z3,z186,z5,z56]),(0,[z0,z2,z3,z4,z852,z6]),(0,[z1366,z0,z204,z3,z5,z6]),(0,[z66,z0,z2,z3,z144,z6]),(0,[z0,z2,z3,z4,z1367,z6]),(0,[z66,z0,z2,z3,z5,z1267])],[(0,[z339,z115,z111,z3,z5,z6]),(0,[z0,z2,z3,z5,z62,z29]),(0,[z0,z2,z1368,z3,z5,z6]),(0,[z0,z22,z153,z3,z5,z6])],[(0,[z0,z2,z3,z1369,z5,z6]),(0,[z0,z1370,z3,z4,z5,z6]),(0,[z0,z1052,z3,z4,z5,z6]),(0,[z0,z2,z3,z273,z5,z11]),(0,[z0,z2,z1371,z3,z5,z6])],[(0,[z0,z2,z3,z5,z56,z58]),(0,[z2,z3,z4,z5,z29,z44]),(0,[z1372,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1373]),(0,[z0,z2,z3,z368,z92,z6]),(0,[z0,z2,z3,z4,z5,z1374])],[(0,[z115,z111,z3,z4,z5,z38]),(0,[z0,z2,z3,z5,z1375,z6]),(0,[z40,z2,z3,z101,z5,z29]),(0,[z1376,z2,z3,z4,z5,z6]),(0,[z66,z515,z0,z3,z5,z6]),(0,[z0,z2,z3,z1377,z5,z6]),(0,[z223,z0,z2,z35,z122,z6])],[(0,[z0,z2,z1378,z4,z5,z6]),(0,[z0,z2,z3,z1379,z5,z6]),(0,[z1380,z2,z3,z4,z5,z6]),(0,[z0,z43,z3,z4,z500,z6])]],
   [[(0,[z66,z109,z111,z3,z5,z6]),(0,[z1381,z0,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z951,z56]),(0,[z0,z2,z316,z4,z5,z329]),(0,[z2,z3,z4,z5,z1382,z6]),(0,[z223,z0,z2,z4,z122,z6])],[(0,[z66,z109,z0,z3,z5,z56]),(0,[z0,z2,z64,z4,z163,z6]),(0,[z0,z2,z3,z950,z5,z6]),(0,[z151,z2,z3,z4,z164,z469])],[(0,[z835,z0,z2,z3,z5,z6]),(0,[z133,z2,z28,z4,z5,z348]),(0,[z0,z2,z3,z1383,z5,z6]),(0,[z0,z2,z3,z1384,z5,z6]),(0,[z0,z205,z2,z3,z5,z6]),(0,[z95,z2,z3,z4,z425,z5]),(0,[z26,z616,z2,z4,z5,z27])],[(0,[z0,z2,z3,z4,z5,z1385]),(0,[z69,z2,z3,z4,z5,z412]),(0,[z2,z3,z4,z164,z743,z6]),(0,[z1272,z2,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z5,z381]),(0,[z0,z2,z225,z13,z5,z6]),(0,[z0,z2,z52,z218,z5,z53])],[(0,[z339,z0,z2,z3,z5,z56]),(0,[z0,z2,z3,z4,z5,z1386]),(0,[z0,z724,z3,z4,z5,z6]),(0,[z133,z22,z2,z28,z5,z6]),(0,[z110,z2,z3,z126,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1387]),(0,[z0,z2,z3,z965,z5,z56]),(0,[z0,z2,z3,z1143,z5,z29]),(0,[z0,z2,z3,z13,z144,z6]),(0,[z0,z2,z3,z1388,z5,z6]),(0,[z0,z2,z3,z55,z771,z6])],[],[(0,[z0,z2,z3,z4,z163,z6]),(0,[z0,z22,z2,z3,z5,z310]),(0,[z0,z2,z3,z4,z500,z56]),(0,[z0,z2,z3,z4,z1389,z5]),(0,[z66,z0,z682,z3,z5,z6])],[(0,[z22,z2,z3,z64,z5,z56]),(0,[z0,z2,z3,z4,z5,z1390]),(0,[z0,z2,z3,z261,z5,z221]),(0,[z440,z0,z3,z4,z5,z90]),(0,[z0,z2,z3,z171,z175,z6]),(0,[z346,z22,z2,z3,z5,z6])],[(0,[z148,z2,z3,z4,z5,z1068]),(0,[z263,z2,z3,z13,z5,z6]),(0,[z0,z313,z3,z25,z5,z6])],[(0,[z442,z0,z22,z3,z5,z6]),(0,[z0,z120,z2,z3,z4,z500])],[(0,[z131,z111,z3,z4,z5,z56]),(0,[z0,z2,z1391,z3,z5,z6]),(0,[z66,z0,z2,z3,z163,z6]),(0,[z0,z2,z3,z125,z5,z29])],[(0,[z0,z2,z3,z1392,z5,z6]),(0,[z0,z2,z3,z35,z140,z6]),(0,[z0,z1159,z3,z4,z5,z29]),(0,[z0,z2,z1393,z4,z5,z6]),(0,[z0,z2,z3,z4,z1394,z5])],[(0,[z0,z22,z489,z3,z5,z6]),(0,[z633,z2,z3,z101,z5,z6]),(0,[z0,z2,z323,z3,z5,z56]),(0,[z0,z2,z3,z295,z485,z6])],[(0,[z0,z2,z3,z4,z140,z6]),(0,[z0,z2,z3,z4,z1395,z6]),(0,[z166,z0,z313,z3,z5,z6]),(0,[z69,z2,z3,z35,z5,z6])],[(0,[z1396,z0,z2,z3,z5,z6]),(0,[z592,z2,z3,z101,z5,z6]),(0,[z0,z2,z3,z273,z5,z56]),(0,[z0,z2,z3,z1397,z5,z6])]],
   [[(0,[z0,z22,z2,z3,z5,z327]),(0,[z0,z948,z361,z3,z5,z6]),(0,[z0,z2,z3,z68,z5,z78])],[(0,[z1398,z0,z2,z3,z4,z6]),(0,[z148,z2,z3,z4,z63,z6]),(0,[z0,z85,z3,z4,z19,z6])],[(0,[z66,z0,z2,z3,z140,z6]),(0,[z66,z0,z664,z3,z5,z6]),(0,[z0,z2,z3,z4,z144,z456]),(0,[z0,z2,z3,z5,z1399,z6]),(0,[z66,z0,z85,z3,z19,z6])],[],[(0,[z66,z114,z111,z3,z5,z6]),(0,[z0,z3,z4,z727,z48,z6]),(0,[z1400,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z525,z93])],[(0,[z0,z2,z3,z1401,z5,z6]),(0,[z187,z0,z3,z4,z5,z310]),(0,[z0,z2,z1402,z4,z5,z6]),(0,[z269,z535,z2,z3,z5,z6]),(0,[z0,z2,z3,z1403,z5,z6])],[(0,[z148,z2,z3,z4,z5,z415]),(0,[z263,z2,z3,z4,z5,z456]),(0,[z761,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1003])],[(0,[z0,z1250,z227,z3,z5,z6]),(0,[z0,z2,z1404,z3,z5,z6]),(0,[z0,z1405,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1406]),(0,[z1407,z0,z2,z3,z5,z6]),(0,[z298,z22,z2,z3,z5,z6]),(0,[z0,z2,z3,z1408,z5,z6]),(0,[z0,z1409,z3,z4,z5,z6])],[(0,[z30,z2,z64,z96,z5,z6]),(0,[z0,z2,z3,z5,z6,z1410]),(0,[z66,z0,z2,z1393,z5,z6]),(0,[z0,z1341,z2,z3,z5,z6])],[(0,[z0,z2,z3,z35,z5,z315]),(0,[z0,z2,z3,z4,z5,z1411]),(0,[z0,z2,z3,z421,z5,z56]),(0,[z0,z3,z794,z4,z5,z6]),(0,[z2,z3,z67,z4,z425,z5])],[(0,[z0,z2,z3,z13,z1394,z5]),(0,[z0,z2,z3,z1412,z5,z6])],[(0,[z0,z1413,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1414])],[(0,[z66,z109,z147,z3,z5,z6]),(0,[z66,z0,z3,z5,z289,z6]),(0,[z0,z2,z3,z4,z5,z744]),(0,[z0,z86,z2,z4,z122,z6]),(0,[z0,z2,z3,z4,z5,z1415])],[(0,[z440,z111,z3,z4,z5,z56]),(0,[z0,z43,z3,z4,z5,z56]),(0,[z0,z2,z3,z1284,z5,z29]),(0,[z0,z2,z3,z1187,z5,z29]),(0,[z0,z1416,z2,z3,z5,z6])],[(0,[z47,z0,z3,z4,z48,z56]),(0,[z121,z0,z2,z225,z5,z6]),(0,[z298,z2,z3,z4,z5,z90]),(0,[z69,z2,z3,z13,z5,z6])]],
   [[(0,[z66,z0,z2,z3,z5,z315]),(0,[z0,z2,z3,z4,z1417,z6]),(0,[z66,z1092,z2,z3,z5,z6])],[(0,[z66,z114,z2,z3,z5,z29]),(0,[z86,z2,z3,z421,z5,z6]),(0,[z994,z0,z509,z3,z5,z6])],[(0,[z22,z2,z111,z3,z5,z56]),(0,[z0,z22,z2,z3,z5,z29]),(0,[z65,z0,z2,z34,z5,z6]),(0,[z0,z2,z54,z3,z418,z6]),(0,[z0,z2,z3,z4,z5,z1418]),(0,[z47,z0,z3,z4,z727,z6]),(0,[z1317,z0,z3,z13,z5,z6]),(0,[z616,z43,z3,z4,z5,z6])],[(0,[z133,z2,z3,z4,z5,z94]),(0,[z666,z2,z3,z4,z5,z29]),(0,[z0,z2,z3,z4,z5,z1285]),(0,[z0,z2,z3,z1419,z5,z6]),(0,[z0,z2,z3,z125,z61,z100])],[(0,[z148,z2,z3,z4,z5,z56]),(0,[z66,z0,z697,z3,z5,z6]),(0,[z0,z2,z3,z1420,z5,z6]),(0,[z0,z2,z3,z35,z203,z5]),(0,[z0,z2,z3,z35,z5,z1346])],[(0,[z0,z2,z3,z4,z5,z1421]),(0,[z0,z2,z3,z1422,z5,z6])],[(0,[z2,z111,z3,z4,z5,z38]),(0,[z0,z2,z794,z4,z5,z6]),(0,[z0,z22,z3,z5,z613,z6]),(0,[z0,z2,z3,z35,z5,z78])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z1423,z2,z3,z4,z5,z6])],[(0,[z282,z111,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z348,z56]),(0,[z2,z3,z35,z425,z5,z6])],[(0,[z0,z9,z2,z3,z5,z29]),(0,[z458,z0,z25,z4,z5,z6]),(0,[z0,z2,z3,z4,z175,z29])],[(0,[z0,z2,z3,z1424,z5,z6]),(0,[z71,z0,z25,z4,z175,z6]),(0,[z66,z0,z2,z3,z203,z5]),(0,[z293,z0,z2,z4,z5,z27])],[(0,[z0,z2,z3,z13,z5,z315]),(0,[z0,z2,z3,z178,z5,z29]),(0,[z0,z2,z3,z4,z5,z1425]),(0,[z148,z2,z3,z82,z63,z6]),(0,[z2,z3,z4,z5,z412,z56]),(0,[z521,z2,z3,z4,z5,z56]),(0,[z223,z0,z2,z68,z122,z6])],[(0,[z30,z66,z2,z64,z5,z6]),(0,[z0,z341,z3,z35,z5,z6]),(0,[z66,z0,z2,z3,z5,z78])],[(0,[z2,z111,z3,z35,z5,z56]),(0,[z66,z592,z2,z3,z5,z56]),(0,[z0,z22,z3,z84,z5,z56]),(0,[z86,z2,z3,z4,z5,z56]),(0,[z1426,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z35,z5,z94]),(0,[z2,z3,z621,z4,z5,z56]),(0,[z1427,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1204]),(0,[z114,z2,z195,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1428]),(0,[z0,z22,z2,z3,z5,z469]),(0,[z0,z2,z3,z1429,z4,z5])]],
   [[(0,[z0,z2,z3,z1430,z5,z6]),(0,[z0,z22,z227,z3,z5,z6]),(0,[z0,z2,z3,z35,z5,z348]),(0,[z187,z0,z3,z4,z5,z29]),(0,[z0,z2,z3,z1431,z5,z6]),(0,[z66,z0,z3,z321,z5,z6]),(0,[z0,z2,z543,z35,z5,z6]),(0,[z0,z2,z3,z4,z20,z78]),(0,[z0,z2,z3,z1432,z5,z6])],[(0,[z0,z1433,z3,z4,z5,z6]),(0,[z0,z2,z3,z1434,z5,z6]),(0,[z2,z3,z4,z5,z29,z152]),(0,[z66,z234,z0,z2,z3,z5]),(0,[z0,z2,z3,z4,z122,z395]),(1,[z0,z2,z745,z5,z6]),(0,[z0,z2,z3,z35,z5,z1355]),(0,[z0,z2,z3,z265,z477,z6])],[(0,[z131,z2,z3,z4,z5,z993]),(0,[z0,z2,z3,z1435,z5,z6]),(0,[z414,z3,z4,z5,z6,z56]),(0,[z0,z2,z195,z4,z5,z29])],[(0,[z0,z2,z3,z4,z5,z808]),(0,[z0,z1436,z3,z4,z5,z6]),(0,[z2,z3,z4,z20,z164,z56]),(0,[z75,z22,z2,z3,z5,z56]),(0,[z0,z2,z730,z4,z5,z6])],[(0,[z0,z2,z3,z159,z5,z315]),(0,[z66,z0,z2,z3,z5,z94]),(0,[z194,z2,z3,z4,z5,z315]),(0,[z2,z3,z555,z4,z5,z56]),(0,[z133,z2,z920,z4,z5,z6]),(0,[z0,z1437,z2,z3,z5,z6]),(0,[z0,z2,z1438,z3,z5,z6])],[(0,[z0,z2,z3,z1439,z5,z6]),(0,[z66,z0,z43,z3,z5,z6]),(0,[z0,z2,z3,z13,z203,z5])],[(0,[z66,z0,z2,z3,z5,z348]),(0,[z66,z151,z2,z3,z164,z6]),(0,[z214,z2,z3,z4,z5,z56]),(0,[z1440,z2,z3,z4,z5,z6])],[(0,[z151,z2,z3,z4,z164,z29]),(0,[z0,z2,z3,z13,z5,z78])],[(0,[z0,z2,z3,z1441,z5,z6]),(0,[z256,z22,z2,z3,z5,z6]),(0,[z0,z22,z2,z3,z484,z5]),(0,[z0,z57,z294,z4,z5,z6]),(0,[z66,z0,z297,z3,z5,z6])],[(0,[z0,z489,z3,z178,z5,z6]),(0,[z520,z2,z64,z4,z5,z6]),(0,[z0,z1442,z3,z4,z5,z6]),(0,[z66,z0,z22,z3,z5,z56]),(0,[z0,z2,z3,z171,z144,z6]),(0,[z0,z2,z52,z369,z4,z5]),(0,[z0,z2,z3,z5,z6,z844])],[(0,[z133,z2,z28,z4,z5,z6]),(0,[z0,z2,z3,z1443,z5,z6]),(0,[z0,z22,z2,z3,z61,z100]),(0,[z86,z2,z3,z4,z122,z6]),(0,[z0,z2,z3,z4,z5,z1444]),(0,[z0,z509,z3,z265,z5,z6])],[(0,[z0,z2,z3,z1445,z5,z6]),(0,[z0,z2,z3,z1446,z5,z6]),(0,[z0,z2,z3,z4,z5,z1447])],[(0,[z66,z0,z2,z3,z5,z1361]),(0,[z66,z0,z3,z37,z5,z6]),(0,[z0,z2,z3,z4,z5,z1448]),(0,[z0,z2,z3,z4,z5,z357])],[(0,[z0,z341,z3,z13,z5,z6]),(0,[z0,z1145,z3,z4,z5,z56]),(0,[z0,z2,z3,z1449,z4,z5]),(0,[z0,z2,z3,z91,z5,z29]),(0,[z263,z2,z3,z171,z5,z6]),(0,[z0,z2,z24,z3,z484,z5]),(0,[z1450,z0,z2,z3,z5,z6]),(0,[z0,z1451,z2,z3,z5,z6]),(0,[z0,z2,z72,z4,z20,z6])],[(0,[z2,z111,z3,z13,z5,z56]),(0,[z40,z2,z177,z3,z5,z6]),(0,[z148,z2,z3,z82,z5,z56]),(0,[z0,z2,z3,z5,z56,z1310]),(0,[z66,z0,z130,z3,z5,z6]),(0,[z0,z2,z113,z13,z5,z29]),(0,[z0,z2,z3,z4,z1452,z6]),(0,[z0,z2,z3,z13,z5,z1350]),(0,[z0,z2,z3,z4,z5,z1453]),(0,[z0,z1454,z2,z3,z5,z6]),(0,[z0,z2,z4,z5,z969,z6])],[(0,[z0,z2,z3,z13,z5,z94]),(0,[z2,z3,z64,z4,z5,z402]),(0,[z256,z2,z3,z4,z175,z6]),(0,[z0,z2,z3,z4,z1455,z6]),(0,[z0,z2,z3,z1456,z5,z6]),(0,[z0,z350,z2,z3,z5,z239]),(0,[z0,z257,z3,z4,z5,z78])]],
   [[(0,[z161,z111,z3,z4,z5,z6]),(0,[z0,z22,z2,z3,z5,z402]),(0,[z0,z2,z3,z203,z5,z170]),(0,[z0,z2,z306,z13,z5,z6])],[(0,[z0,z2,z920,z4,z5,z6]),(0,[z0,z2,z3,z13,z5,z348]),(0,[z0,z2,z3,z82,z5,z6]),(0,[z0,z2,z3,z1457,z5,z6]),(0,[z0,z2,z3,z5,z6,z1458]),(0,[z26,z0,z2,z265,z5,z27]),(0,[z0,z2,z3,z4,z5,z1459])],[(0,[z66,z187,z0,z3,z5,z6]),(0,[z439,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z5,z29,z1460]),(0,[z0,z361,z3,z4,z5,z78])],[(0,[z2,z3,z636,z4,z5,z56]),(0,[z66,z0,z2,z149,z5,z6]),(0,[z66,z1376,z2,z3,z5,z6]),(0,[z66,z0,z2,z3,z1455,z6]),(0,[z1461,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1333]),(0,[z0,z2,z3,z241,z5,z6]),(0,[z0,z2,z3,z1462,z5,z6])],[(0,[z0,z2,z322,z35,z5,z6]),(0,[z1164,z0,z2,z3,z5,z56]),(0,[z0,z2,z3,z225,z5,z29]),(0,[z0,z2,z3,z4,z1463,z6]),(0,[z0,z2,z657,z13,z5,z6]),(0,[z0,z2,z3,z1464,z5,z6])],[(0,[z131,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z1465,z5,z6]),(0,[z0,z1466,z3,z4,z5,z6]),(0,[z30,z2,z920,z4,z5,z6]),(0,[z1467,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1468,z5,z6]),(0,[z0,z2,z3,z4,z5,z1469]),(0,[z346,z2,z3,z265,z5,z6])],[(0,[z148,z2,z3,z4,z63,z412]),(0,[z0,z2,z3,z5,z6,z1470])],[(0,[z0,z2,z3,z4,z827,z6]),(0,[z0,z2,z3,z35,z163,z6]),(0,[z148,z414,z3,z4,z63,z6]),(0,[z166,z0,z2,z34,z5,z6])],[(0,[z0,z489,z3,z96,z5,z6]),(0,[z0,z2,z3,z178,z5,z402]),(0,[z30,z2,z64,z4,z163,z6]),(0,[z39,z2,z3,z899,z5,z6]),(0,[z0,z2,z195,z967,z5,z6])],[(0,[z2,z3,z64,z4,z5,z415]),(0,[z1366,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z484,z13,z5]),(0,[z1002,z22,z2,z3,z5,z6]),(0,[z223,z0,z22,z2,z122,z6]),(0,[z0,z2,z3,z1471,z5,z6]),(0,[z26,z298,z2,z3,z4,z5])],[(0,[z0,z22,z2,z3,z5,z415]),(0,[z0,z1472,z3,z4,z5,z6]),(0,[z223,z0,z2,z4,z969,z6])],[(0,[z0,z2,z3,z5,z6,z1460]),(0,[z40,z2,z3,z287,z5,z6]),(0,[z148,z66,z2,z3,z63,z6]),(0,[z0,z2,z3,z4,z784,z5])],[(0,[z0,z2,z3,z1473,z5,z6])],[(0,[z0,z2,z3,z4,z1474,z6]),(0,[z0,z2,z3,z105,z4,z70]),(0,[z0,z2,z3,z1475,z5,z6]),(0,[z0,z2,z3,z396,z5,z6])],[(0,[z285,z2,z3,z4,z5,z56]),(0,[z0,z2,z3,z4,z328,z378])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 481) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 481).take 481) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 962).take 480) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1442).take 155) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1597)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [481, 481, 480, 155] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 210).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 310).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 415).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 109, 100, 105, 97] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37909

theorem PEqualNP.Outside.L_meta_37909 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074666 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074666 * 2 ^ 32 + 4276681384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37909.solve