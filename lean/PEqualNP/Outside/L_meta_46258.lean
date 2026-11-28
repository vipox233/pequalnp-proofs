import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46258

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277067904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0001085444630d80#64 ++ 0xc4000210a888c61b#64 ++ 0x029118fc4ce71fee#64 ++ 0xfa052231f899ce3f#64 : BitVec 256),
   (0x0021633051296290#64 ++ 0xa80042c660a252c5#64 ++ 0x4561e7307339e3dd#64 ++ 0xf68ac3ce60e673c7#64 : BitVec 256),
   (0x298605c183c0b721#64 ++ 0x30530c0b8307816e#64 ++ 0xb98e07c383c1ffff#64 ++ 0xaf731c0f870783ff#64 : BitVec 256),
   (0x560bb802fc01d805#64 ++ 0xc0ac177005f803b0#64 ++ 0xfe0ff803fc01fc3b#64 ++ 0x9ffc1ff007f803f8#64 : BitVec 256),
   (0x1fd000032a940046#64 ++ 0x003fa00006552800#64 ++ 0x3ff00003fffe0078#64 ++ 0x7e7fe00007fffc00#64 : BitVec 256),
   (0x1ffcd6a800000078#64 ++ 0x003ff9ad50000000#64 ++ 0xdffffffc00000007#64 ++ 0xffbffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000000032a940006 0x0000000006552800 0x22900003fffe0078 0x7a45200007fffc00

def z1 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fee 0xfa052231f899ce3f

def z2 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e3dd 0xf68ac3ce60e673c7

def z3 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z4 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00000007 0xffbffffff8000000

def z5 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1ffff 0xaf731c0f870783ff

def z6 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z7 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff0000073380058 0x7e3fe00000e67000

def z8 : W := mkw 0x562bfb32fd29fa95 0xe8ac57f665fa53f5 0xff6fff33ff39ffff 0xfffedffe67fe73ff

def z9 : W := mkw 0x5fdbb803fe95d847 0xc0bfb77007fd2bb0 0xfffff803fffffc7b 0xfffffff007fffff8

def z10 : W := mkw 0x400128027c014804 0xc080025004f80290 0x000000007c000000 0x0000000000f80000

def z11 : W := mkw 0x1ff446ab2a94007e 0x003fe88d56552800 0x3ff007fffffe007c 0x7e7fe00ffffffc00

def z12 : W := mkw 0x0000000000000000 0x0000000000000000 0x029000004ce60068 0x7a0520000099cc00

def z13 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9e07c3cfe7ffff 0xff773c0f879fcfff

def z14 : W := mkw 0x1fd890032a940046 0x003fb12006552800 0xfffff803fffe007b 0xfffffff007fffc00

def z15 : W := mkw 0x0000001400220080 0x0400000028004401 0x0010003c00260000 0x4000200078004c00

def z16 : W := mkw 0x0001080044010800 0xc000021000880210 0x020118004c011c2a 0x9a04023000980238

def z17 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x4761ff307f39ffff 0xfe8ec3fe60fe73ff

def z18 : W := mkw 0x1fd108576ef70dc6 0xc43fa210aeddee1b 0x3a9118ffcce71fee 0xfa752231ff99ce3f

def z19 : W := mkw 0x1650000228140046 0x002ca00004502800 0x021000000c060000 0x0004200000180c00

def z20 : W := mkw 0x0001200050014000 0x8000024000a00280 0x4561e0007339e059 0xf68ac3c000e673c0

def z21 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0x6601f803fc01fc38 0x10cc03f007f803f8

def z22 : W := mkw 0x09f446a800000078 0x0013e88d50000000 0x01f007fc00000004 0x6003e00ff8000000

def z23 : W := mkw 0x40032802fc01d805 0xc080065005f803b0 0x20000003fc01fc38 0x0040000007f803f8

def z24 : W := mkw 0x00012954556b6f80 0xec000252a8aad6df 0x000000007ffffff8 0x0000000000ffffff

def z25 : W := mkw 0x0000084404420d00 0x440000108808841a 0x029018cc0cc61c22 0x0805203198198c38

def z26 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc00ffffc00000007 0x81801ffff8000000

def z27 : W := mkw 0x1fd108576ef70dc6 0xc43fa210aeddee1b 0x3ff118ffffff1ffe 0xfe7fe231fffffe3f

def z28 : W := mkw 0x0000000000000000 0x0000000000000000 0x029118fc00000006 0xfa052231f8000000

def z29 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff118fffffe007e 0xfe7fe231fffffc00

def z30 : W := mkw 0x7f8fbdd7ffe3ffa5 0xf4ff1f7bafffc7ff 0xff9fffffffe7ffff 0xffff3fffffffcfff

def z31 : W := mkw 0x0021632051096210 0xa80042c640a212c4 0x4561e7007319e019 0x968ac3ce00e633c0

def z32 : W := mkw 0x298604c182c09521 0x10530c098305812a 0xb88e00c380c01c22 0x09711c0187018038

def z33 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x000000000001e380 0x00000000000003c7

def z34 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfffffffffffe007f 0xfffffffffffffc00

def z35 : W := mkw 0x3ffed7ebabd4b77f 0x307ffdafd757a96e 0xffffffffffffffff 0xffffffffffffffff

def z36 : W := mkw 0x20020143abd4b707 0x304004028757a96e 0x20000003fffffff8 0x0040000007ffffff

def z37 : W := mkw 0x1ffddefc44630df8 0xc43ffbbdf888c61b 0xdffffffc4ce71fef 0xffbffffff899ce3f

def z38 : W := mkw 0x1678d22a2814005e 0x002cf1a454502800 0x4671f83c7c3e0000 0x508ce3f078f87c00

def z39 : W := mkw 0x09a567b0512962b0 0xa8134acf60a252c5 0xddefe7f07339e3df 0xffbbdfcfe0e673c7

def z40 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc4ce6006f 0xffbffffff899cc00

def z41 : W := mkw 0x560bb856fc63dd85 0xc4ac1770adf8c7bb 0xfe9ff8fffce7ffff 0xfffd3ff1fff9cfff

def z42 : W := mkw 0x09f446a800000078 0x0013e88d50000000 0x03f11ffc00000006 0xfa07e23ff8000000

def z43 : W := mkw 0x0000010001002200 0x2000000200020044 0x010007000301e3dd 0xa602000e000603c7

def z44 : W := mkw 0x29a767f1d3e9f7b1 0xb8534ecfe3a7d3ef 0xfdefe7f3f3f9ffff 0xfffbdfcfe7e7f3ff

def z45 : W := mkw 0x160a900080009001 0x002c152001000120 0xfe0ff8038001fc3b 0x9ffc1ff0070003f8

def z46 : W := mkw 0x3ffed7e983c0b779 0x307ffdafd307816e 0xffffffff83c1ffff 0xffffffffff0783ff

def z47 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc29ffffc00000007 0xfb853ffff8000000

def z48 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3d600003b3180010 0x047ac00007663000

def z49 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb90e07038300e011 0x05721c0e070601c0

def z50 : W := mkw 0x29870dd5c7e3bfa1 0xf4530e1bab8fc77f 0xbb9f1fffcfe7ffff 0xff773e3fff9fcfff

def z51 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e070383c1fff9 0x05721c0e070783ff

def z52 : W := mkw 0x5ffffeaafc01d87d 0xc0bffffd55f803b0 0xfffffffffc01fc3f 0xfffffffffff803f8

def z53 : W := mkw 0x4009b80054014800 0xc080137000a80290 0x4001f80000000000 0x008003f000000000

def z54 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x01f0000003fe0040 0x6003e0000007fc00

def z55 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0xb80e07c38001ffbf 0x8f701c0f870003ff

def z56 : W := mkw 0x1608900000000000 0x002c112000000000 0xde0ff80000000003 0x9fbc1ff000000000

def z57 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c0e3d5 0x25731c0f870781c7

def z58 : W := mkw 0x00214a7444630d90 0xc4004294e888c61b 0x47f1fffc4ce71fef 0xfe8fe3fff899ce3f

def z59 : W := mkw 0x1679da7c44630dd8 0xc42cf3b4f888c61b 0x46f1f8fc4ce71fee 0xfa8de3f1f899ce3f

def z60 : W := mkw 0x298705d1c3e1b7a1 0xb0530e0ba387c36f 0xb98f07f3c3e1ffff 0xff731e0fe787c3ff

def z61 : W := mkw 0x560bb846fc43dd05 0xc4ac17708df887ba 0xfe9ff8cffcc7fc3b 0x9ffd3ff19ff98ff8

def z62 : W := mkw 0x0000000000000000 0x0000000000000000 0x000118fc00000006 0x80000231f8000000

def z63 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xdffffffc03fe0047 0xffbffffff807fc00

def z64 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x029000fc4ce603ec 0x7a052001f899cc07

def z65 : W := mkw 0x09f567b8512962f8 0xa813eacf70a252c5 0x45f1e7fc7339e3dd 0xf68be3cff8e673c7

def z66 : W := mkw 0x0001001040210080 0x8000020020804201 0x00010030402103cc 0xf200020060804207

def z67 : W := mkw 0x00216b74556b6f90 0xec0042d6e8aad6df 0x47f1fffc7fffffff 0xfe8fe3fff8ffffff

def z68 : W := mkw 0x0001080044010800 0xc000021000880210 0x0001180000011c02 0x8000023000000238

def z69 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xc67ffffc00000007 0xd18cfffff8000000

def z70 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x000118fc00011f86 0x80000231f800023f

def z71 : W := mkw 0x000000032a940006 0x0000000006552800 0x25600003fffe0078 0x764ac00007fffc00

def z72 : W := mkw 0x298404c102c00520 0x105308098205800a 0x008000c000c00000 0x0001000180018000

def z73 : W := mkw 0x000108576ef70d86 0xc4000210aeddee1b 0x229118ffffff1ffe 0xfa452231fffffe3f

def z74 : W := mkw 0x0984048000000020 0x0013080900000000 0x998e07c000000007 0xaf331c0f80000000

def z75 : W := mkw 0x1678d22800000058 0x002cf1a450000000 0x4671f83c00000000 0x508ce3f078000000

def z76 : W := mkw 0x2002014183c0b701 0x304004028307816e 0x2000000383c1fff8 0x00400000070783ff

def z77 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0x218007c383c1fffc 0x2043000f870783ff

def z78 : W := mkw 0x00236330d129f291 0xa80046c661a253e5 0xfd6fe733f339ffff 0xfffadfce67e673ff

def z79 : W := mkw 0x3fffdffdc7e3bff9 0xf47fffbffb8fc77f 0xffffffffcfe7ffff 0xffffffffff9fcfff

def z80 : W := mkw 0x00214b74456b2f90 0xec004296e88ad65f 0x03f11ffc4fff1fee 0xfa07e23ff89ffe3f

def z81 : W := mkw 0x3ffed7e88140b779 0x307ffdafd102816e 0xdffffffc0001ff87 0xffbffffff80003ff

def z82 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x000000007339e3d8 0x0000000000e673c7

def z83 : W := mkw 0x0020422000000010 0x0000408440000000 0x4561e73000000005 0xf68ac3ce60000000

def z84 : W := mkw 0x7faffff3ffe9ffb5 0xf8ff5fffe7ffd3ff 0xffeffff3fff9ffff 0xffffdfffe7fff3ff

def z85 : W := mkw 0x09a1633153a96290 0xa81342c662a752c5 0x7de1e733f3f9e3fd 0xfefbc3ce67e7f3c7

def z86 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4101e7300301e3dd 0xa68203ce600603c7

def z87 : W := mkw 0x0020432001002210 0x2000408640020044 0x4561e7300301e3dd 0xf68ac3ce600603c7

def z88 : W := mkw 0x1679da3c442308d8 0xc42cf3b478884611 0x4671f83c4c260000 0x508ce3f078984c00

def z89 : W := mkw 0x0002000080009001 0x0000040001000120 0xb80e00038001fc3b 0x8f701c00070003f8

def z90 : W := mkw 0x7f8fbdc3ffc1ff25 0xf0ff1f7b87ff83fe 0xff8fffc3ffc1ffff 0xbfff1fff87ff83ff

def z91 : W := mkw 0x1fd108176eb708c6 0xc43fa2102edd6e11 0x3ff1183ffffe0078 0x7e7fe2307ffffc00

def z92 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0x9b9e1fcc00000007 0xaf373c3f98000000

def z93 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0x800e07c00001ff87 0x81001c0f800003ff

def z94 : W := mkw 0x3fd605c3abd4b767 0x307fac0b8757a96e 0xbffe07c3ffffffff 0xff7ffc0f87ffffff

def z95 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ff803b001fc13 0x85f81ff0076003f8

def z96 : W := mkw 0x7f8eb5c3bbc0f725 0x30ff1d6b877781ee 0xfd8ee7c3b3c1ffff 0xaffb1dcf876783ff

def z97 : W := mkw 0x0001200050014000 0x8000024000a00280 0x4401e0007001e019 0x968803c000e003c0

def z98 : W := mkw 0x0020433001282290 0x2800408660025045 0x01600730033803c4 0x6002c00e60067007

def z99 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4461e7307039e385 0xd088c3ce60e073c7

def z100 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbdee07c3f3f9ffff 0xff7bdc0f87e7f3ff

def z101 : W := mkw 0x560a9802ac009805 0x40ac153005580130 0xba0e18038c001c22 0x09741c3007180038

def z102 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xc1fffffc00000007 0xe183fffff8000000

def z103 : W := mkw 0x165000032a940046 0x002ca00006552800 0x26700003fffe0078 0x504ce00007fffc00

def z104 : W := mkw 0x20236371d3e9f791 0xb84046c6e3a7d3ef 0x6561e733f3f9fffd 0xf6cac3ce67e7f3ff

def z105 : W := mkw 0x0001084044410d00 0xc00002108088821a 0x028118c04cc11fee 0xba0502318099823f

def z106 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3de00003b3d80078 0x2e7bc0000767b000

def z107 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3a9000038cc60020 0x0875200007198c00

def z108 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4000e7000000e001 0x008001ce000001c0

def z109 : W := mkw 0x29a667a19388f231 0x38534ccf432711e4 0xfd6ee703b318e011 0x05faddce076631c0

def z110 : W := mkw 0x000000032a940006 0x0000000006552800 0x20000003fffe0078 0x0040000007fffc00

def z111 : W := mkw 0x0020422000000010 0x0000408440000000 0x4001e73000000005 0x808003ce60000000

def z112 : W := mkw 0x298405c103c02720 0x3053080b8207804e 0x018007c003c003c4 0x2003000f80078007

def z113 : W := mkw 0x29f647e983c0b779 0x3053ec8fd307816e 0xb9fe07ff83c1ffff 0xef73fc0fff0783ff

def z114 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003bfde0030 0x0c7fe000077fbc00

def z115 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x000000004ce71fe8 0x000000000099ce3f

def z116 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdd6ee70000000001 0x05baddce00000000

def z117 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xdffffffc7c3e0007 0xffbffffff8f87c00

def z118 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xd98ffffc00000007 0xafb31ffff8000000

def z119 : W := mkw 0x0980000102800000 0x0013000002050000 0x0180000003c00040 0x2003000000078000

def z120 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4001e7300001e385 0x808003ce600003c7

def z121 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x008000c04ce71fee 0xaa0100018099ce3f

def z122 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdd6ffffc00000007 0x85badffff8000000

def z123 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000011c2a 0x8a00000000000238

def z124 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfc0ee003b001fc3b 0x8ff81dc0076003f8

def z125 : W := mkw 0x5609b8027c014804 0xc0ac137004f80290 0x4601f8007c000000 0x108c03f000f80000

def z126 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x009118fc00e71fc6 0xe0012231f801ce3f

def z127 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7003318e011 0x048ac1ce006631c0

def z128 : W := mkw 0x1ffdf7b8512962f8 0xa83ffbef70a252c5 0xdffffffc7339e3df 0xffbffffff8e673c7

def z129 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x47f1e7307fffe3fd 0xfe8fe3ce60ffffc7

def z130 : W := mkw 0x5679fa2a7c01485c 0xc0acf3f454f80290 0x4671f83c7c000000 0x508ce3f078f80000

def z131 : W := mkw 0x1ff163337bbd62d6 0xa83fe2c666f77ac5 0x7ff1e733ffffe3fd 0xfeffe3ce67ffffc7

def z132 : W := mkw 0x5608b00238004004 0x00ac116004700080 0x4400e00030000000 0x008801c000600000

def z133 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xde0ffffc00000007 0x9fbc1ffff8000000

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000c000000006 0xaa01000180000000

def z135 : W := mkw 0x00216b74556b6f90 0xec0042d6e8aad6df 0x4561e7307ffffffd 0xf68ac3ce60ffffff

def z136 : W := mkw 0x1fd108576ef70dc6 0xc43fa210aeddee1b 0x3ff00003ffff1ff8 0x7e7fe00007fffe3f

def z137 : W := mkw 0x3fd60583ab94b267 0x307fac0b07572964 0xbffe0703fffee079 0x7f7ffc0e07fffdc0

def z138 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffff8cc60027 0xffffffffff198c00

def z139 : W := mkw 0x560bb902fd01fa05 0xe0ac177205fa03f4 0xff0fff03ff01ffff 0xbffe1ffe07fe03ff

def z140 : W := mkw 0x0020423000280090 0x0800408460005001 0x0060003000380000 0x4000c00060007000

def z141 : W := mkw 0x1679f238502940d8 0x882cf3e470a05281 0x4671f83c70380000 0x508ce3f078e07000

def z142 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce61c22 0x58052231f899cc38

def z143 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff0000000000000 0x7e3fe00000000000

def z144 : W := mkw 0x1650000228140046 0x002ca00004502800 0x067000007c3e0000 0x500ce00000f87c00

def z145 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4561e73070380005 0xf68ac3ce60e07000

def z146 : W := mkw 0x0000000000000000 0x0000000000000000 0x029018cc00000002 0x0805203198000000

def z147 : W := mkw 0x0001081444230880 0xc400021028884611 0x0211183c4c260000 0x5004223078984c00

def z148 : W := mkw 0x0020422000000010 0x0000408440000000 0x4561e7307338005d 0xf68ac3ce60e67000

def z149 : W := mkw 0x29aed7e983c0b739 0x30535dafd307816e 0xf98fffff83c1ffff 0xaff31fffff0783ff

def z150 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ee003fc01fc39 0x05f81dc007f803f8

def z151 : W := mkw 0x3fd605c183c0b761 0x307fac0b8307816e 0xbffe07c383c1ffff 0xff7ffc0f870783ff

def z152 : W := mkw 0x0001000040010000 0x8000020000800200 0x0001000040010008 0x9200020000800200

def z153 : W := mkw 0x562bf332f929f295 0xa8ac57e665f253e5 0xfd6fe733f339e3dd 0xf7fadfce67e673c7

def z154 : W := mkw 0x1fd001032b942246 0x203fa00206572844 0x3ff00703ffffe3fd 0xfe7fe00e07ffffc7

def z155 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4461e03070380000 0x5088c3c060e07000

def z156 : W := mkw 0x1600000228000004 0x002c000004500000 0x3e000003fc000038 0x1e7c000007f80000

def z157 : W := mkw 0x0001200050014000 0x8000024000a00280 0x4401e00070000000 0x108803c000e00000

def z158 : W := mkw 0x16716332793d62d6 0xa82ce2c664f27ac5 0x4771e7307f3fe3dd 0xf68ee3ce60fe7fc7

def z159 : W := mkw 0x29d605c183d4b763 0x3053ac0b8307a96e 0xb9fe07c383ffffff 0xef73fc0f8707ffff

def z160 : W := mkw 0x1678d22800000058 0x002cf1a450000000 0xde7ff83c00000003 0xdfbcfff078000000

def z161 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x0000000000011f80 0x000000000000023f

def z162 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307338e011 0x548ac3ce60e671c0

def z163 : W := mkw 0x0000004000400500 0x000000008000800a 0x008000c000c11fee 0xaa0100018001823f

def z164 : W := mkw 0x0000084404420d00 0x440000108808841a 0x029018cc4ce61c6a 0x7a0520319899cc38

def z165 : W := mkw 0x565bb802fc15d847 0xc0acb77005f82bb0 0xfe7ff803fc3ffc3b 0xdffcfff007f87ff8

def z166 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000073380058 0x760ac00000e67000

def z167 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x07f118fc7fff1ffe 0xfe0fe231f8fffe3f

def z168 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x009000fc00e71fee 0xea012001f801ce3f

def z169 : W := mkw 0x1ffdd6b8402100f8 0x803ffbad70804201 0xdffffffc402103cf 0xffbffffff8804207

def z170 : W := mkw 0x298604c182c09521 0x10530c098305812a 0xb88e00c380c11fee 0xab711c018701823f

def z171 : W := mkw 0x0001200050014000 0x8000024000a00280 0x4001e0000001e001 0x808003c0000003c0

def z172 : W := mkw 0x3f8605c3abc0b725 0x307f0c0b8757816e 0xbf8e07c3ffc1ffff 0xbf7f1c0f87ff83ff

def z173 : W := mkw 0x09f54efc44630df8 0xc413ea9df888c61b 0x03f11ffc4ce71fee 0xfa07e23ff899ce3f

def z174 : W := mkw 0x2002014183c0b701 0x304004028307816e 0xb80e000383c1fffb 0x8f701c00070783ff

def z175 : W := mkw 0x5ffdfeaa7c01487c 0xc0bffbfd54f80290 0xdffffffc7c000007 0xffbffffff8f80000

def z176 : W := mkw 0x5ffef6aab800d07d 0x00bffded557001a0 0xffffffffb000e017 0xffffffffff6001c0

def z177 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfc0ee003b000e011 0x05f81dc0076001c0

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000001e019 0x86000000000003c0

def z179 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029000004ce71fe8 0x7a0520000099ce3f

def z180 : W := mkw 0x29d405c103d42762 0x3053a80b8207a84e 0x01f007c003fe03c4 0x6003e00f8007fc07

def z181 : W := mkw 0x40032803fe95d807 0xc080065007fd2bb0 0x20000003fffffc78 0x0040000007fffff8

def z182 : W := mkw 0x0020422000000010 0x0000408440000000 0x4560e70000000001 0x048ac1ce00000000

def z183 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x0160000003180000 0x0002c00000063000

def z184 : W := mkw 0x7f8fbd83ff81fa25 0xf0ff1f7b07ff03f4 0xff0fff03ff01fc3b 0x9ffe1ffe07fe03f8

def z185 : W := mkw 0x298605c3abd4b727 0x30530c0b8757a96e 0xb98e07c3ffffffff 0xaf731c0f87ffffff

def z186 : W := mkw 0x1fd404832a940066 0x003fa80906552800 0xbffe07c3fffe007f 0xff7ffc0f87fffc00

def z187 : W := mkw 0x1ffdfffc556b6ff8 0xec3ffbfff8aad6df 0xdffffffc7fffffff 0xffbffffff8ffffff

def z188 : W := mkw 0x560a9802ac009805 0x40ac153005580130 0xbe0e1803fc001c3a 0x1f7c1c3007f80038

def z189 : W := mkw 0x562bfa22fc01d815 0xc0ac57f445f803b0 0xff6fff33fc01fc3f 0xfffedffe67f803f8

def z190 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xba0e1803fc01fc3a 0x09741c3007f803f8

def z191 : W := mkw 0x5fdab003ba94d047 0x00bfb560077529a0 0xfd6ee003b318e011 0x05faddc0076631c0

def z192 : W := mkw 0x000c948800000028 0x0000192910000000 0x800e18cc00000002 0x01001c3198000000

def z193 : W := mkw 0x562bfb32fd29fa95 0xe8ac57f665fa53f5 0xfe0fff33fc01ffbf 0x9ffc1ffe67f803ff

def z194 : W := mkw 0x29870cd5c6e39da1 0xd4530e19ab8dc73b 0xba9f18ffcce71fee 0xfb753e31ff99ce3f

def z195 : W := mkw 0x5fdbb803fe95d847 0xc0bfb77007fd2bb0 0xfe9ff803fcc7fc3b 0x9ffd3ff007f98ff8

def z196 : W := mkw 0x402bfb30d529fa91 0xe88057f661aa53f5 0xc00fff300001ff87 0x81801ffe600003ff

def z197 : W := mkw 0x0001001040210080 0x8000020020804201 0x029118fc402103ce 0xfa052231f8804207

def z198 : W := mkw 0x1ff162337abd40d6 0x883fe2c466f57a81 0x7ff1e033fffe0078 0x7effe3c067fffc00

def z199 : W := mkw 0x0001005440630580 0x84000200a880c60b 0x009100fc40e703cc 0xf2012201f881ce07

def z200 : W := mkw 0x69872dc3ffc1ff25 0xf0d30e5b87ff83fe 0xb98e07c3ffc1ffff 0xaf731c0f87ff83ff

def z201 : W := mkw 0x1650000228140046 0x002ca00004502800 0x3e700003fc3e0038 0x5e7ce00007f87c00

def z202 : W := mkw 0x1ff163337bbd62d6 0xa83fe2c666f77ac5 0x7d61e733f339e3dd 0xf6fac3ce67e673c7

def z203 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x0000000000e603c0 0x000000000001cc07

def z204 : W := mkw 0x1fd000432ad40546 0x003fa0008655a80a 0x3ff000c3ffff1ffe 0xfe7fe00187fffe3f

def z205 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0x9ffe18cc00000002 0x7f3ffc3198000000

def z206 : W := mkw 0x40032800d401d801 0xc080065001a803b0 0x000000000001fc00 0x00000000000003f8

def z207 : W := mkw 0x29870dd5c7e3bfa1 0xf4530e1bab8fc77f 0xb98e07c3cfe7ffff 0xaf731c0f879fcfff

def z208 : W := mkw 0x00032000d001d001 0x8000064001a003a0 0xfc0fe003f001fc3b 0x9ff81fc007e003f8

def z209 : W := mkw 0x0001201050214080 0x8000024020a04281 0x4401e0307021e3dd 0xf68803c060e043c7

def z210 : W := mkw 0x3ffed6e982c09579 0x107ffdadd305812a 0xffffffff80c01c27 0xffffffffff018038

def z211 : W := mkw 0x000201008100b201 0x2000040201020164 0xb90e07038301ffff 0xaf721c0e070603ff

def z212 : W := mkw 0x0002000080009001 0x0000040001000120 0x800e00000001fc03 0x81001c00000003f8

def z213 : W := mkw 0x5609b8027c014804 0xc0ac137004f80290 0xde0ff8007c000003 0x9fbc1ff000f80000

def z214 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4560e7007339e3d9 0x048ac1ce00e673c7

def z215 : W := mkw 0x3ffed7a98380b279 0x307ffdaf53070164 0xffffffff8300e017 0xffffffffff0601c0

def z216 : W := mkw 0x2002004182c09501 0x104004008305812a 0x2000000380c01c20 0x0040000007018038

def z217 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4401e7307001e39d 0x968803ce60e003c7

def z218 : W := mkw 0x29a447f103e827b0 0x3853488fe207d04f 0x01e007f003f803c4 0x6003c00fe007f007

def z219 : W := mkw 0x0000000000000000 0x0000000000000000 0x980e000000000003 0x8f301c0000000000

def z220 : W := mkw 0x09d0005502f605c2 0x0413a000aa05ec0b 0x01f000fc03fe03c4 0x6003e001f807fc07

def z221 : W := mkw 0x5fdbb802fc01d845 0xc0bfb77005f803b0 0xfffff803fc01fc3b 0xfffffff007f803f8

def z222 : W := mkw 0x2982014183c0b701 0x305304028307816e 0x3980000383c1fff8 0x2e730000070783ff

def z223 : W := mkw 0x0980000102800000 0x0013000002050000 0x3980000383c00078 0x2e73000007078000

def z224 : W := mkw 0x1ff16b777fff6fd6 0xec3fe2d6eefffedf 0x7ff1ffffffffffff 0xfeffe3ffffffffff

def z225 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff8fffc01fc3f 0xfffd3ff1fff803f8

def z226 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x000100307339e3dc 0xf200020060e673c7

def z227 : W := mkw 0x400bb854d463dd81 0xc4801770a9a8c7bb 0xc00ff8fc0001ff87 0x81801ff1f80003ff

def z228 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc56ffffc00000007 0xf78adffff8000000

def z229 : W := mkw 0x3fd605c3abd4b767 0x307fac0b8757a96e 0xbb9e07c38fc7ffff 0xaf773c0f871f8fff

def z230 : W := mkw 0x1678d22800000058 0x002cf1a450000000 0x4460e00000000000 0x0088c1c000000000

def z231 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x4771ff3c7f3fe3dd 0xf68ee3fe78fe7fc7

def z232 : W := mkw 0x0000085404620d80 0x44000010a808c41b 0x029018fc0ce61fe6 0x68052031f819cc3f

def z233 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xc00ff8000001fc03 0x81801ff0000003f8

def z234 : W := mkw 0x7f8e9cc3aec09d25 0x50ff1d39875d813a 0xba8e18c38cc01c22 0x09751c3187198038

def z235 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ef00003fcfe0020 0x587de00007f9fc00

def z236 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4461e0307039e019 0xd688c3c060e073c0

def z237 : W := mkw 0x560a9002a8009005 0x00ac152005500120 0xb80e000380000000 0x01701c0007000000

def z238 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xda9ffffc00000007 0x89b53ffff8000000

def z239 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdd6fe73000000005 0xf7badfce60000000

def z240 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x009000fc00e603c4 0x60012001f801cc07

def z241 : W := mkw 0x2000014103c02700 0x304000028207804e 0x0000000003c003c0 0x0000000000078007

def z242 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1d60000000000000 0x043ac00000000000

def z243 : W := mkw 0x09d000032a940046 0x0013a00006552800 0x21f00003fffe0078 0x6043e00007fffc00

def z244 : W := mkw 0x0020433001282290 0x2800408660025045 0x016007300339e3dd 0xe602c00e600673c7

def z245 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0x980e000000000000 0x01301c0000000000

def z246 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x47f1fffc7339e3df 0xfe8fe3fff8e673c7

def z247 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3f700003ff3e0010 0x547ee00007fe7c00

def z248 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000000000000 0x760ac00000000000

def z249 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000073380058 0x0000000000e67000

def z250 : W := mkw 0x560bb842fc41dd05 0xc0ac177085f883ba 0xfe8ff8c3fcc1ffff 0xbffd1ff187f983ff

def z251 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4560e7303338e3d5 0x648ac1ce606671c7

def z252 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc7338005f 0xffbffffff8e67000

def z253 : W := mkw 0x1ffdf7bb7bbd62fe 0xa83ffbef76f77ac5 0xffffffffffffe3ff 0xffffffffffffffc7

def z254 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0x9a9e18cc00000002 0x09353c3198000000

def z255 : W := mkw 0x0001210051016200 0xa000024200a202c4 0x4501e7007301e3dd 0xb68a03ce00e603c7

def z256 : W := mkw 0x0980000102800000 0x0013000002050000 0x3de00003f3f80078 0x7e7bc00007e7f000

def z257 : W := mkw 0x0000000102800000 0x0000000002050000 0x2000000383c00078 0x0040000007078000

def z258 : W := mkw 0x3fd60583ab94b267 0x307fac0b07572964 0xbd6e0703b318e011 0x057adc0e076631c0

def z259 : W := mkw 0x0000000000000000 0x0000000000000000 0x4401e00000000001 0x968803c000000000

def z260 : W := mkw 0x0001081444230880 0xc400021028884611 0x0211183c4c2703cc 0xf204223078984e07

def z261 : W := mkw 0x200201408140b701 0x304004028102816e 0x000000000001ff80 0x00000000000003ff

def z262 : W := mkw 0x0000000102940002 0x0000000002052800 0x0000000003fe0040 0x000000000007fc00

def z263 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xddfee7fc00000005 0x65bbfdcff8000000

def z264 : W := mkw 0x00216374516b6790 0xac0042c6e8a2d6cf 0x45f1e7fc73ffe3dd 0xf68be3cff8e7ffc7

def z265 : W := mkw 0x1ff0422000000050 0x003fe08440000000 0x5ff1e73000000005 0xfebfe3ce60000000

def z266 : W := mkw 0x0001081444230880 0xc400021028884611 0x0001183c00000000 0x0000023078000000

def z267 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffb3180017 0xffffffffff663000

def z268 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe0ff833fc21ffff 0xfffc1ff067f843ff

def z269 : W := mkw 0x5fdbb857fef7ddc7 0xc4bfb770affdefbb 0xfffff8ffffffffff 0xfffffff1ffffffff

def z270 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xf80ff8038001fc3b 0x8ff01ff0070003f8

def z271 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e07c38301ff97 0x85721c0f870603ff

def z272 : W := mkw 0x29a767f1d3e9f7b1 0xb8534ecfe3a7d3ef 0xf98fe7f383c1ffff 0xaff31fcfe70783ff

def z273 : W := mkw 0x698fbdc1d7c1ff21 0xf0d31f7b83af83fe 0xf98fffc383c1ffff 0xaff31fff870783ff

def z274 : W := mkw 0x1fd100136ab500c6 0x803fa20026d56a01 0x3ff10033ffff03fc 0xfe7fe20067fffe07

def z275 : W := mkw 0x000000032a940006 0x0000000006552800 0x20000003b3180010 0x0040000007663000

def z276 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xba9e18cf8cc60022 0x09753c319f198c00

def z277 : W := mkw 0x3ffcd7e903c02778 0x307ff9afd207804e 0xdffffffc03c003c7 0xffbffffff8078007

def z278 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfe0ef803bc00fc33 0x0dfc1df0077801f8

def z279 : W := mkw 0x5609b8167c234884 0xc4ac13702cf84691 0x4611f83c7c260000 0x508c23f078f84c00

def z280 : W := mkw 0x7f8fbcc3fec1dd25 0xd0ff1f7987fd83ba 0xfe8ff8c3fcc1fc3b 0x9ffd1ff187f983f8

def z281 : W := mkw 0x402ffea8d401d839 0xc0805ffd51a803b0 0xc00ffffc0001fc07 0x81801ffff80003f8

def z282 : W := mkw 0x0020622010084010 0x080040c440201080 0x4460e00030180000 0x0088c1c000603000

def z283 : W := mkw 0x1608900228000004 0x002c112004500000 0xfe0ff803fc00003b 0x9ffc1ff007f80000

def z284 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3bf000038ffe0060 0x6877e000071ffc00

def z285 : W := mkw 0x0982000182809001 0x0013040003050120 0xb98e000383c1fc7b 0xaf731c00070783f8

def z286 : W := mkw 0x3fd405c32bd42766 0x307fa80b8657a84e 0x3ff007c3fffe03fc 0x7e7fe00f87fffc07

def z287 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdf6fff0000000003 0x9fbedffe00000000

def z288 : W := mkw 0x1ffddebc442308f8 0xc43ffbbd78884611 0xdffffffc4c260007 0xffbffffff8984c00

def z289 : W := mkw 0x402bfb30d529fa91 0xe88057f661aa53f5 0xc56fff307339ffdf 0xf78adffe60e673ff

def z290 : W := mkw 0x0000001000200080 0x0000000020004001 0x00000030002003c4 0x6000000060004007

def z291 : W := mkw 0x29a667e193c8f731 0x38534ccfc32791ee 0xfdeee7c3b3d9ffff 0xaffbddcf8767b3ff

def z292 : W := mkw 0x29a767b1d3a9f2b1 0xb8534ecf63a753e5 0xfd6fe733f339e3dd 0xf7fadfce67e673c7

def z293 : W := mkw 0x00216b74556b6f90 0xec0042d6e8aad6df 0x4001fffc0001ff87 0x808003fff80003ff

def z294 : W := mkw 0x20070dd4c563bfa1 0xf4400e1ba98ac77f 0x800f1ffc0001ff87 0x81001e3ff80003ff

def z295 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc0cc71fa6 0x88052231f8198e3f

def z296 : W := mkw 0x0001201050294080 0x8800024020a05281 0x0000000070380000 0x0000000000e07000

def z297 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x000000fc00000384 0x00000001f8000007

def z298 : W := mkw 0x1650000228140046 0x002ca00004502800 0x06f000007cfe0068 0x7a0de00000f9fc00

def z299 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfe0ee003fc00e039 0x1ffc1dc007f801c0

def z300 : W := mkw 0x0021423040210090 0x8000428460804201 0x4561e730402103cd 0xf68ac3ce60804207

def z301 : W := mkw 0x0002004080409501 0x000004008100812a 0xb88e00c380c1ffff 0xaf711c01870183ff

def z302 : W := mkw 0x0001285454634d80 0xc4000250a8a8c69b 0x4691f8fc7ce7ffff 0xfe8d23f1f8f9cfff

def z303 : W := mkw 0x00216b74556b6f90 0xec0042d6e8aad6df 0x4291fffc4ce7ffef 0xfa8523fff899cfff

def z304 : W := mkw 0x5ffef6aab800d07d 0x00bffded557001a0 0xfd6ee703b000e011 0x05faddce076001c0

def z305 : W := mkw 0x09f446a800000078 0x0013e88d50000000 0x99fe07fc00000007 0xef33fc0ff8000000

def z306 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0x9a9f18fc00000006 0xfb353e31f8000000

def z307 : W := mkw 0x09f446a800000078 0x0013e88d50000000 0x0160070000000000 0x0002c00e00000000

def z308 : W := mkw 0x29870dc1c7c1bf21 0xf0530e1b838f837e 0xbb8f1fc3cfc1ffff 0xbf771e3f879f83ff

def z309 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4001e7307339e3dd 0x808003ce60e673c7

def z310 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfd6ee703b3180011 0x05faddce07663000

def z311 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xfffffffffc00003f 0xfffffffffff80000

def z312 : W := mkw 0x400bb854d463dd81 0xc4801770a9a8c7bb 0xc29ff8fc4ce7ffef 0xfb853ff1f899cfff

def z313 : W := mkw 0x0984048000000020 0x0013080900000000 0x018007c000000004 0x2003000f80000000

def z314 : W := mkw 0x0021433041292290 0xa800428660825245 0x01610730433903cc 0xf202c20e60867207

def z315 : W := mkw 0x1650000228140046 0x002ca00004502800 0x077000007f3e0058 0x760ee00000fe7c00

def z316 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x016007307339e3dc 0x6002c00e60e673c7

def z317 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffeffcc00000003 0x0dbffdff98000000

def z318 : W := mkw 0x567bfa2afc01d85d 0xc0acf7f455f803b0 0xfe7ff83ffc01fc3b 0xdffcfff07ff803f8

def z319 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7303319e395 0x848ac3ce606633c7

def z320 : W := mkw 0x0000004000400500 0x000000008000800a 0x000000c000011f86 0x800000018000023f

def z321 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xff6ff803ff39fc7b 0xfffedff007fe73f8

def z322 : W := mkw 0x3fd604c3aad49567 0x107fac098755a92a 0xba9e00c38cc61c22 0x09753c0187198c38

def z323 : W := mkw 0x7fdfbdc3ffd5ff67 0xf0ffbf7b87ffabfe 0xffffffc3ffffffff 0xffffffff87ffffff

def z324 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb90e07038301fc3b 0x8f721c0e070603f8

def z325 : W := mkw 0x0000084404420d00 0x440000108808841a 0x029118fc0cc61c26 0xfa052231f8198c38

def z326 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3df00003b3fe0050 0x647be0000767fc00

def z327 : W := mkw 0x0020433001282290 0x2800408660025045 0x0000073000000384 0x0000000e60000007

def z328 : W := mkw 0x298405c103c02720 0x3053080b8207804e 0x018007c003c1e3dd 0xa603000f800783c7

def z329 : W := mkw 0x1600000228000004 0x002c000004500000 0x3c000003b0000010 0x0478000007600000

def z330 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029018cc4ce71fea 0x080520319899ce3f

def z331 : W := mkw 0x29a647f183e8b7b1 0x38534c8fe307d16f 0xb9ee07f383f9ffff 0xef73dc0fe707f3ff

def z332 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc00ee70000000001 0x01801dce00000000

def z333 : W := mkw 0x5fda9803ae949847 0x40bfb530075d2930 0xba9e18038cc61c22 0x09753c3007198c38

def z334 : W := mkw 0x1600000228000004 0x002c000004500000 0x3e900003fce60078 0x7e7d200007f9cc00

def z335 : W := mkw 0x40032856fc63dd85 0xc4800650adf8c7bb 0x229118fffce7fffe 0xfa452231fff9cfff

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x0090000000e60040 0x600120000001cc00

def z337 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7003319e3dd 0xa68ac1ce006633c7

def z338 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe1ff83ffc27fc3b 0xdffc3ff07ff84ff8

def z339 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c01fe6 0x29731c0f8707803f

def z340 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z341 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x07f000007ffe0040 0x700fe00000fffc00

def z342 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff803fce7fc7b 0xfffd3ff007f9cff8

def z343 : W := mkw 0x1600000228000004 0x002c000004500000 0x060000007c000000 0x100c000000f80000

def z344 : W := mkw 0x0050000000140042 0x0000a00000002800 0x00700000003e0000 0x4000e00000007c00

def z345 : W := mkw 0x0000004400420500 0x040000008800840a 0x009000cc00c60000 0x0001200198018c00

def z346 : W := mkw 0x560bb002f801d005 0x80ac176005f003a0 0xfc0fe003f001e019 0x97f81fc007e003c0

def z347 : W := mkw 0x160108026c010804 0xc02c021004d80210 0x3e011803fc011c3a 0x9e7c023007f80238

def z348 : W := mkw 0x09f446fc006205f8 0x0413e88df800c40b 0x01f007fc00e603c4 0x6003e00ff801cc07

def z349 : W := mkw 0x165108566c770dc6 0xc42ca210acd8ee1b 0x06f118fc7cff1fee 0xfa0de231f8f9fe3f

def z350 : W := mkw 0x1650000000000040 0x002ca00000000000 0x0670000000000000 0x500ce00000000000

def z351 : W := mkw 0x002163337bbd6296 0xa80042c666f77ac5 0x6561e733ffffe3fd 0xf6cac3ce67ffffc7

def z352 : W := mkw 0x600fbdc0d541ff21 0xf0c01f7b81aa83fe 0xc00fffc00001ff87 0x81801fff800003ff

def z353 : W := mkw 0x0001081444230880 0xc400021028884611 0x0211183c4c271c2a 0xda04223078984e38

def z354 : W := mkw 0x000108576ef70d86 0xc4000210aeddee1b 0x20000003ffff1ff8 0x0040000007fffe3f

def z355 : W := mkw 0x200201018380b201 0x3040040203070164 0x200000038300e010 0x00400000070601c0

def z356 : W := mkw 0x0001001040210080 0x8000020020804201 0x029100304ce703ec 0xfa0522006099ce07

def z357 : W := mkw 0x1fd0000102940042 0x003fa00002052800 0x1ff0000003fe0040 0x7e3fe0000007fc00

def z358 : W := mkw 0x1608900000000000 0x002c112000000000 0xde9ff8fc00000007 0xffbd3ff1f8000000

def z359 : W := mkw 0x20032151d3e9f781 0xb8400642a3a7d3ef 0x20000003f3f9fff8 0x0040000007e7f3ff

def z360 : W := mkw 0x400bb802fc01d805 0xc080177005f803b0 0xe00ff803fc01fc3b 0x81c01ff007f803f8

def z361 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x056000007339e3d8 0x760ac00000e673c7

def z362 : W := mkw 0x0000004000400500 0x000000008000800a 0x0000000000c11fe8 0x000000000001823f

def z363 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x008118fc00c11fee 0xaa010231f801823f

def z364 : W := mkw 0x1608900000000000 0x002c112000000000 0x4601f80000000000 0x108c03f000000000

def z365 : W := mkw 0x560a9846ac429d05 0x44ac15308d58853a 0xba9e18cf8cc61c22 0x09753c319f198c38

def z366 : W := mkw 0x3fd70dd7eff7bfe7 0xf47fae1bafdfef7f 0xbfff1fffffffffff 0xff7ffe3fffffffff

def z367 : W := mkw 0x560bb856fc63dd85 0xc4ac1770adf8c7bb 0xfe0ff803fce7fffb 0x9ffc1ff007f9cfff

def z368 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfe0ff803b000e013 0x9ffc1ff0076001c0

def z369 : W := mkw 0x0001081444230880 0xc400021028884611 0x029118fc4c260006 0xfa052231f8984c00

def z370 : W := mkw 0x5fdbb803fe95d847 0xc0bfb77007fd2bb0 0xff6ff803ff19fc3b 0x9ffedff007fe33f8

def z371 : W := mkw 0x0000084404420d00 0x440000108808841a 0x000018cc00001c02 0x0000003198000038

def z372 : W := mkw 0x202ed7e88140b739 0x30405dafd102816e 0xc00ffffc0001ff87 0x81801ffff80003ff

def z373 : W := mkw 0x0000004000400500 0x000000008000800a 0x008000c000c003c4 0x2001000180018007

def z374 : W := mkw 0x0008900000000000 0x0000112000000000 0xc00ff80000000003 0x81801ff000000000

def z375 : W := mkw 0x1fd0000228000044 0x003fa00004500000 0x3ff00003fc000038 0x7e7fe00007f80000

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080000000c00068 0x2a01000000018000

def z377 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xc20ff8004c01fc2b 0x9b841ff0009803f8

def z378 : W := mkw 0x0004048000000020 0x0000080900000000 0x800e07c000000007 0x81001c0f80000000

def z379 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x010007007339e3dd 0xa602000e00e673c7

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x07f000007ffe0078 0x7e0fe00000fffc00

def z381 : W := mkw 0x0001080044010800 0xc000021000880210 0x000000004c011c28 0x0000000000980238

def z382 : W := mkw 0x2984058103802220 0x3053080b02070044 0x0100070003000000 0x0002000e00060000

def z383 : W := mkw 0x560a9802ac009805 0x40ac153005580130 0xba0e18038c01fc3b 0x8f741c30071803f8

def z384 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3e900003fcc60038 0x1e7d200007f98c00

def z385 : W := mkw 0x3f8e95c183c0b721 0x307f1d2b8307816e 0xff8fffc383c1ffff 0xbfff1fff870783ff

def z386 : W := mkw 0x5609b8027c014804 0xc0ac137004f80290 0x7e01f803fc000038 0x1efc03f007f80000

def z387 : W := mkw 0x160108566c630d84 0xc42c0210acd8c61b 0x3e9118fffce71ffe 0xfe7d2231fff9ce3f

def z388 : W := mkw 0x5ffffefefc63ddfd 0xc4bffffdfdf8c7bb 0xfffffffffce7ffff 0xfffffffffff9cfff

def z389 : W := mkw 0x1ffcd6fc006205f8 0x043ff9adf800c40b 0xdffffffc00e603c7 0xffbffffff801cc07

def z390 : W := mkw 0x1ffcf7a811086278 0x283ff9ef502210c4 0xdffffffc3318e017 0xffbffffff86631c0

def z391 : W := mkw 0x560898022c000804 0x40ac113004580010 0x020018000c000000 0x0004003000180000

def z392 : W := mkw 0x5ffffea8d401d879 0xc0bffffd51a803b0 0xdffffffc0001fc07 0xffbffffff80003f8

def z393 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb90e07038301e3dd 0xa7721c0e070603c7

def z394 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x000118fc4ce71fee 0x80000231f899ce3f

def z395 : W := mkw 0x0000080404020800 0x4400001008080410 0x0210180c0c060000 0x0004203018180c00

def z396 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfa0ff8038c01fc23 0x89f41ff0071803f8

def z397 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xbffe18cffffe007a 0x7f7ffc319ffffc00

def z398 : W := mkw 0x200605808100b221 0x30400c0b01020164 0x800e07000000e001 0x01001c0e000001c0

def z399 : W := mkw 0x1609980044010800 0xc02c133000880210 0xde0ff8004c011c2b 0x9fbc1ff000980238

def z400 : W := mkw 0x40032802fc01d805 0xc080065005f803b0 0x22011803fc01fc3a 0x9a44023007f803f8

def z401 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3d600003fffe0078 0x047ac00007fffc00

def z402 : W := mkw 0x5fdab003ba94d047 0x00bfb560077529a0 0xfffee003fffee079 0x7ffffdc007fffdc0

def z403 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x000118fc40211fce 0xf2000231f880423f

def z404 : W := mkw 0x0001001040210080 0x8000020020804201 0x0001003040200000 0x5000020060804000

def z405 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000004ce60068 0x000000000099cc00

def z406 : W := mkw 0x0984058001002220 0x2013080b00020044 0x998e07c00301e3df 0xaf331c0f800603c7

def z407 : W := mkw 0x3fd604c3aad49567 0x107fac098755a92a 0xbffe00c3fffe1c7a 0x7f7ffc0187fffc38

def z408 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x009000fc4ce71fec 0x60012001f899ce3f

def z409 : W := mkw 0x3fd605c3abd4b767 0x307fac0b8757a96e 0xbdee07c3b3d9ffff 0xaf7bdc0f8767b3ff

def z410 : W := mkw 0x29a76ff5d7ebffb1 0xfc534edfebafd7ff 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x29f447e903c02778 0x3053e88fd207804e 0x01f007fc03c003c4 0x6003e00ff8078007

def z412 : W := mkw 0x002446a800000038 0x0000488d50000000 0x000007fc00000004 0x0000000ff8000000

def z413 : W := mkw 0x1f8c948000000020 0x003f192900000000 0xdf8fffc000000007 0xbfbf1fff80000000

def z414 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000040200048 0x7200000000804000

def z415 : W := mkw 0x560bb856fc63dd85 0xc4ac1770adf8c7bb 0xfe0ff8fffc01ffbf 0x9ffc1ff1fff803ff

def z416 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4001e7304021e3cd 0xf28003ce608043c7

def z417 : W := mkw 0x298605d583e2b7a1 0x34530c0bab07c56f 0xb99e07ff83e7ffff 0xef733c0fff07cfff

def z418 : W := mkw 0x202767f0d169f7b1 0xb8404ecfe1a2d3ef 0xc00fe7f00001ff87 0x81801fcfe00003ff

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x009000fc00000004 0x60012001f8000000

def z420 : W := mkw 0x0000000228140006 0x0000000004502800 0x000000007c3e0000 0x0000000000f87c00

def z421 : W := mkw 0x1ffdf7b8512962f8 0xa83ffbef70a252c5 0xdd6fe7307339e3dd 0xf7badfce60e673c7

def z422 : W := mkw 0x0984048000000020 0x0013080900000000 0x9b9f1ffc00000007 0xff373e3ff8000000

def z423 : W := mkw 0x2002014183c0b701 0x304004028307816e 0x2100070383c1fffd 0xa642000e070783ff

def z424 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3b9000038fc60078 0x2e772000071f8c00

def z425 : W := mkw 0x0001095445632f80 0xe4000212a88ac65f 0x03911ffc4fe7ffff 0xfe07223ff89fcfff

def z426 : W := mkw 0x5ffffeabfe95d87f 0xc0bffffd57fd2bb0 0xfffffffffffffc7f 0xfffffffffffffff8

def z427 : W := mkw 0x0021637051696790 0xa80042c6e0a2d2cf 0x45e1e7f073f9ffff 0xfe8bc3cfe0e7f3ff

def z428 : W := mkw 0x3ffff7f9d3e9f7f9 0xb87fffeff3a7d3ef 0xfffffffff3f9ffff 0xffffffffffe7f3ff

def z429 : W := mkw 0x1609985444630d80 0xc42c1330a888c61b 0xde9ff8fc4ce71fef 0xffbd3ff1f899ce3f

def z430 : W := mkw 0x5609b8567c634d84 0xc4ac1370acf8c69b 0x4691f8fc7ce71fee 0xfa8d23f1f8f9ce3f

def z431 : W := mkw 0x1fdc9ccc04420d68 0x443fb9399808841a 0x9a9e18cc0cc61c22 0x09353c3198198c38

def z432 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb88e07c380c1ffa7 0x89711c0f870183ff

def z433 : W := mkw 0x0020422000000010 0x0000408440000000 0x0160073000000004 0x6002c00e60000000

def z434 : W := mkw 0x0020433001282290 0x2800408660025045 0x4561e730033803c5 0xf68ac3ce60067007

def z435 : W := mkw 0x29a567f153e967b0 0xb8534acfe2a7d2cf 0x45e1e7f073f9e3dd 0xf68bc3cfe0e7f3c7

def z436 : W := mkw 0x1fd1085444630dc0 0xc43fa210a888c61b 0x1ff118fc4ce71fee 0xfe3fe231f899ce3f

def z437 : W := mkw 0x0028d22800000018 0x000051a450000000 0x4001f83c00000000 0x008003f078000000

def z438 : W := mkw 0x0001011041212280 0xa000020220824245 0x010107304321e3dd 0xf602020e608643c7

def z439 : W := mkw 0x16716232783d40d6 0x882ce2c464f07a81 0x4671e0307c3e0000 0x508ce3c060f87c00

def z440 : W := mkw 0x1ff042232a940056 0x003fe08446552800 0x7ff1e733fffe007d 0xfeffe3ce67fffc00

def z441 : W := mkw 0x7f8e9dc3afc0bf25 0x70ff1d3b875f817e 0xbb8e1fc38fc1ffff 0xaf771c3f871f83ff

def z442 : W := mkw 0x298405d503e227a0 0x3453080baa07c44f 0x019007fc03e603c4 0x6003200ff807cc07

def z443 : W := mkw 0x0002000080009001 0x0000040001000120 0xb80e000380001c22 0x09701c0007000038

def z444 : W := mkw 0x0986048080009021 0x00130c0901000120 0xb98e07c38001fc3f 0xaf731c0f870003f8

def z445 : W := mkw 0x0000011001282280 0x2800000220025045 0x00000000033803c0 0x0000000000067007

def z446 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xffffffff83c0007f 0xffffffffff078000

def z447 : W := mkw 0x7fffffebffc1ff7d 0xf0ffffffd7ff83fe 0xffffffffffc1ffff 0xffffffffffff83ff

def z448 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff000038cc60020 0x7e7fe00007198c00

def z449 : W := mkw 0x0000010001002200 0x2000000200020044 0x01000700030003c4 0x2002000e00060007

def z450 : W := mkw 0x1fd000572af605c6 0x043fa000ae55ec0b 0x3ff000fffffe03fc 0x7e7fe001fffffc07

def z451 : W := mkw 0x1600000228000004 0x002c000004500000 0x3a0000038c000020 0x0874000007180000

def z452 : W := mkw 0x5fffffbafd29fafd 0xe8bfffff75fa53f5 0xffffffffff39ffff 0xfffffffffffe73ff

def z453 : W := mkw 0x1650000228140046 0x002ca00004502800 0x0460000030180000 0x0008c00000603000

def z454 : W := mkw 0x200604c080409521 0x10400c098100812a 0x800e00c000001c02 0x01001c0180000038

def z455 : W := mkw 0x0001200050014000 0x8000024000a00280 0x000000007001e018 0x0000000000e003c0

def z456 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x020118004ce71fea 0x9a0402300099ce3f

def z457 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003b3180010 0x7e7fe00007663000

def z458 : W := mkw 0x0000000000000000 0x0000000000000000 0x0460000070380000 0x5008c00000e07000

def z459 : W := mkw 0x1678d22800000058 0x002cf1a450000000 0x4771ff3c00000005 0xf68ee3fe78000000

def z460 : W := mkw 0x1ff8d22800000058 0x003ff1a450000000 0x5ff1f83c00000000 0x7ebfe3f078000000

def z461 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0x9bfe1ffc00000006 0x6937fc3ff8000000

def z462 : W := mkw 0x760fbdc2fd41ff25 0xf0ec1f7b85fa83fe 0xfe0fffc3fc01ffbf 0x9ffc1fff87f803ff

def z463 : W := mkw 0x5ffffeaafc01d87d 0xc0bffffd55f803b0 0xff6fff03fc01fc3b 0x9ffedffe07f803f8

def z464 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc00e011 0x15fc1ff007f801c0

def z465 : W := mkw 0x1658900800000048 0x002cb12010000000 0x0210180c00000000 0x0004203018000000

def z466 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4561e7303318e015 0xf68ac3ce606631c0

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x0201180000000002 0x9a04023000000000

def z468 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffee70000000001 0x7fbffdce00000000

def z469 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc001c22 0x19fc1ff007f80038

def z470 : W := mkw 0x0000084404420d00 0x440000108808841a 0x029018cc0cc71fee 0xaa05203198198e3f

def z471 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc00011f86 0xfa052231f800023f

def z472 : W := mkw 0x56032802fc01d805 0xc0ac065005f803b0 0x3e000003fc01fc38 0x1e7c000007f803f8

def z473 : W := mkw 0x16020002a8009005 0x002c040005500120 0xbe0e0003fc01fc3b 0x9f7c1c0007f803f8

def z474 : W := mkw 0x0000000000000000 0x0000000000000000 0x029000000cc60020 0x0805200000198c00

def z475 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9f1fff83c1ffff 0xff773e3fff0783ff

def z476 : W := mkw 0x002df7b8512962b8 0xa8005bef70a252c5 0xc00ffffc0001e387 0x81801ffff80003c7

def z477 : W := mkw 0x5629fa327c294894 0xc8ac53f464f85291 0x4661f8307c380000 0x508cc3f060f87000

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800000380000038 0x0e70000007000000

def z479 : W := mkw 0x09f0433103bc22d2 0x2813e08662077845 0x01f0073003fe03c4 0x6003e00e6007fc07

def z480 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdefff8fc00000002 0x59bdfff1f8000000

def z481 : W := mkw 0x5609b8027c014804 0xc0ac137004f80290 0x4601f8007c01e019 0x968c03f000f803c0

def z482 : W := mkw 0x0001005040610580 0x80000200a080c20b 0x008100f040e11fee 0xfa010201e081c23f

def z483 : W := mkw 0x0000000000000000 0x0000000000000000 0x0290000000000000 0x7a05200000000000

def z484 : W := mkw 0x0002000080009001 0x0000040001000120 0xb80e00038000e011 0x05701c00070001c0

def z485 : W := mkw 0x5609b8027c014804 0xc0ac137004f80290 0x4601f8007c011c2a 0x9a8c03f000f80238

def z486 : W := mkw 0x09d0000000000040 0x0013a00000000000 0x01f0000000000000 0x6003e00000000000

def z487 : W := mkw 0x002ddefc44630db8 0xc4005bbdf888c61b 0xc29ffffc4ce71fef 0xfb853ffff899ce3f

def z488 : W := mkw 0x1ffcd7b8012822f8 0x283ff9af70025045 0xdffffffc033803c7 0xffbffffff8067007

def z489 : W := mkw 0x1fd20003aa949047 0x003fa40007552920 0xbffe0003fffffc7b 0xff7ffc0007fffff8

def z490 : W := mkw 0x1600000228000004 0x002c000004500000 0x3f600003ff380078 0x7e7ec00007fe7000

def z491 : W := mkw 0x1ff043332bbc22d6 0x283fe08666577845 0x3ff00733fffe03fc 0x7e7fe00e67fffc07

def z492 : W := mkw 0x3ffed7a98380b279 0x307ffdaf53070164 0xfd6ee7038300e011 0x05faddce070601c0

def z493 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xddeee7c000000007 0xafbbddcf80000000

def z494 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x0090000000c60000 0x0001200000018c00

def z495 : W := mkw 0x0980000000000000 0x0013000000000000 0x1980000000000000 0x2e33000000000000

def z496 : W := mkw 0x0021622050014010 0x800042c440a00280 0x4561e7307001e01d 0xf68ac3ce60e003c0

def z497 : W := mkw 0x0000010001002200 0x2000000200020044 0x056007007339e3dd 0xf60ac00e00e673c7

def z498 : W := mkw 0x09850cd444630da0 0xc4130a19a888c61b 0x9b9f1ffc4ce71fef 0xff373e3ff899ce3f

def z499 : W := mkw 0x00216b74556b6f90 0xec0042d6e8aad6df 0x4561fffc7339ffdf 0xf68ac3fff8e673ff

def z500 : W := mkw 0x560b9856ec639d85 0xc4ac1730add8c73b 0xba9f18ffcce71fee 0xfb753e31ff99ce3f

def z501 : W := mkw 0x560bb800d401d801 0xc0ac177001a803b0 0xde0ff8000001fc03 0x9fbc1ff0000003f8

def z502 : W := mkw 0x0000005400620580 0x04000000a800c40b 0x029118fc00e603c6 0xfa052231f801cc07

def z503 : W := mkw 0x0000210011086200 0x28000042002210c4 0x000000003318e010 0x00000000006631c0

def z504 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x021118fc4c271f86 0xd0042231f8984e3f

def z505 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3a900003cce60068 0x7a7520000799cc00

def z506 : W := mkw 0x5ffedeaaac00987d 0x40bffdbd55580130 0xffffffff8c001c27 0xffffffffff180038

def z507 : W := mkw 0x2002014183c0b701 0x304004028307816e 0x208000c383c1fffe 0xaa410001870783ff

def z508 : W := mkw 0x1ffddea844010878 0xc03ffbbd50880210 0xdffffffc4c011c2f 0xffbffffff8980238

def z509 : W := mkw 0x298604c182c09521 0x10530c098305812a 0xb98e07c380c01c27 0xaf731c0f87018038

def z510 : W := mkw 0x00216a74546b4d90 0xcc0042d4e8a8d69b 0x46f1f8fc7cff1fee 0xfa8de3f1f8f9fe3f

def z511 : W := mkw 0x1600000000000000 0x002c000000000000 0x1e00000000000000 0x1e3c000000000000

def z512 : W := mkw 0x0000000000000000 0x0000000000000000 0x0160000003380040 0x6002c00000067000

def z513 : W := mkw 0x298725d1d3e9f7a1 0xb8530e4ba3a7d3ef 0xb98e07c3f3f9ffff 0xaf731c0f87e7f3ff

def z514 : W := mkw 0x165108166c3708c6 0xc42ca2102cd86e11 0x0671183c7c3e0000 0x500ce23078f87c00

def z515 : W := mkw 0x002df7b8512962b8 0xa8005bef70a252c5 0xc56ffffc7339e3df 0xf78adffff8e673c7

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x021000004c260000 0x5004200000984c00

def z517 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7007338e059 0x768ac1ce00e671c0

def z518 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb88e00c383c1fffa 0x09711c01870783ff

def z519 : W := mkw 0x40020802ac009805 0x4080041005580130 0x200000038c001c20 0x0040000007180038

def z520 : W := mkw 0x09f446a90294007a 0x0013e88d52052800 0x01f007fc03fe0044 0x6003e00ff807fc00

def z521 : W := mkw 0x1fd108036e950846 0xc03fa21006dd2a10 0x3ff11803ffff1c7a 0xfe7fe23007fffe38

def z522 : W := mkw 0x29a647e183c0b731 0x30534c8fc307816e 0xfdefe7f383c1ffff 0xfffbdfcfe70783ff

def z523 : W := mkw 0x1fd120037a954046 0x803fa24006f52a80 0x7ff1e003ffffe079 0xfeffe3c007ffffc0

def z524 : W := mkw 0x562af322b908f215 0x28ac55e6457211e4 0xfd6ee703b318e011 0x05faddce076631c0

def z525 : W := mkw 0x1ffddefc44630df8 0xc43ffbbdf888c61b 0xdffffffc00011f87 0xffbffffff800023f

def z526 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0x47f1fffc00000004 0x708fe3fff8000000

def z527 : W := mkw 0x1621633279296294 0xa82c42c664f252c5 0x7f61e733ff39e3fd 0xfefec3ce67fe73c7

def z528 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb98e070383c0e079 0x2f731c0e070781c0

def z529 : W := mkw 0x0001081044210880 0xc000021020884211 0x020118304c211fee 0xfa0402306098423f

def z530 : W := mkw 0x0984048102800020 0x0013080902050000 0xb98e07c383c0007f 0xaf731c0f87078000

def z531 : W := mkw 0x0980000102800000 0x0013000002050000 0x3b900003cfe60078 0x7e772000079fcc00

def z532 : W := mkw 0x202767f0d169f7b1 0xb8404ecfe1a2d3ef 0xc56fe7f07339ffdf 0xf78adfcfe0e673ff

def z533 : W := mkw 0x298405c103c02720 0x3053080b8207804e 0x018007c003c11fee 0xaa03000f8007823f

def z534 : W := mkw 0x1ff063233b9c6256 0x283fe0c6467738c4 0x7d60e703b318e011 0x04fac1ce076631c0

def z535 : W := mkw 0x298604c182c09521 0x10530c098305812a 0xb88e00c380c1fc3b 0x8f711c01870183f8

def z536 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x020118fc4c011fae 0x9a040231f898023f

def z537 : W := mkw 0x000121137bbd6286 0xa800024226f77ac5 0x20000003ffffe3f8 0x0040000007ffffc7

def z538 : W := mkw 0x1ff16330512962d0 0xa83fe2c660a252c5 0x5ff1e7307339e3dd 0xfebfe3ce60e673c7

def z539 : W := mkw 0x298605c08140b721 0x30530c0b8102816e 0x998e07c00001ff87 0xaf331c0f800003ff

def z540 : W := mkw 0x1ffed6a880009079 0x003ffdad51000120 0xffffffff8001fc3f 0xffffffffff0003f8

def z541 : W := mkw 0x1608900000000000 0x002c112000000000 0xdc0ee00000000001 0x05b81dc000000000

def z542 : W := mkw 0x1679f338512962d8 0xa82cf3e670a252c5 0x4771ff3c7339e3dd 0xf68ee3fe78e673c7

def z543 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001003000000004 0xf200020060000000

def z544 : W := mkw 0x0000000000000000 0x0000000000000000 0x0560000033180010 0x040ac00000663000

def z545 : W := mkw 0x1ffddeff6ef70dfe 0xc43ffbbdfeddee1b 0xffffffffffff1fff 0xfffffffffffffe3f

def z546 : W := mkw 0x1601200278014004 0x802c024004f00280 0x7e01e003fc01e039 0x9efc03c007f803c0

def z547 : W := mkw 0x200605c183c0b721 0x30400c0b8307816e 0xa00e07c383c1ffff 0x81401c0f870783ff

def z548 : W := mkw 0x0001001040210080 0x8000020020804201 0x00000000402103c8 0x0000000000804207

def z549 : W := mkw 0x0000000000000000 0x0000000000000000 0x020000004c000028 0x1a04000000980000

def z550 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4461e030703903cc 0xf288c3c060e07207

def z551 : W := mkw 0x1ff446a800000078 0x003fe88d50000000 0x1ff007fc00000004 0x7e3fe00ff8000000

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x0211183c00000000 0x5004223078000000

def z553 : W := mkw 0x0001081444230880 0xc400021028884611 0x0291183c4ce60068 0x7a0522307899cc00

def z554 : W := mkw 0x1fd8900000000040 0x003fb12000000000 0xdffff80000000003 0xffbffff000000000

def z555 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0x808e07c000c1ffef 0xab011c0f800183ff

def z556 : W := mkw 0x560b9802ec019805 0xc0ac173005d80330 0xba0f1803cc011c2a 0x9b741e3007980238

def z557 : W := mkw 0x40032912fd29fa85 0xe880065225fa53f5 0x20000003ff39fff8 0x0040000007fe73ff

def z558 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4461e0307339e3d8 0x5088c3c060e673c7

def z559 : W := mkw 0x0000010001002200 0x2000000200020044 0x010007000300e011 0x0402000e000601c0

def z560 : W := mkw 0x400a980084009801 0x4080153001080130 0x800e180000001c02 0x01001c3000000038

def z561 : W := mkw 0x1fdd9cdc44630de8 0xc43fbb39b888c61b 0x9a9f18fc4ce71fee 0xfb353e31f899ce3f

def z562 : W := mkw 0x560bb803fe95d807 0xc0ac177007fd2bb0 0xfe0ff803fffffc7b 0x9ffc1ff007fffff8

def z563 : W := mkw 0x562ffeaafc01d83d 0xc0ac5ffd55f803b0 0xfe0ffffffc01fc3f 0x9ffc1ffffff803f8

def z564 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0x818e07c003c1ffc7 0xa1031c0f800783ff

def z565 : W := mkw 0x200405c001402720 0x3040080b8002804e 0x000007c000000384 0x0000000f80000007

def z566 : W := mkw 0x0001080044010800 0xc000021000880210 0x029118004ce71c6a 0xfa0522300099ce38

def z567 : W := mkw 0x09f1633153bd62d2 0xa813e2c662a77ac5 0x45f1e73073ffe3dd 0xf68be3ce60e7ffc7

def z568 : W := mkw 0x00030854c4639d81 0xc4000610a988c73b 0xba9f18ffcce7ffff 0xff753e31ff99cfff

def z569 : W := mkw 0x0981085546e30d80 0xc4130210aa8dc61b 0x3b9118ffcfe71ffe 0xfe772231ff9fce3f

def z570 : W := mkw 0x1ff063233b9c6256 0x283fe0c6467738c4 0x7ff0e703fffee079 0x7effe1ce07fffdc0

def z571 : W := mkw 0x1fd121137bbd62c6 0xa83fa24226f77ac5 0x3ff00003ffffe3f8 0x7e7fe00007ffffc7

def z572 : W := mkw 0x0001084444430d00 0xc40002108888861a 0x029118cc4cc71c2a 0x9a05223198998e38

def z573 : W := mkw 0x0000000228000004 0x0000000004500000 0x20000003fc000038 0x0040000007f80000

def z574 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xc60ff8007c01fc03 0x918c1ff000f803f8

def z575 : W := mkw 0x1ffcf7a811086278 0x283ff9ef502210c4 0xdd6ee7003318e011 0x05baddce006631c0

def z576 : W := mkw 0x0001001040210080 0x8000020020804201 0x05610030733903dc 0xf60ac20060e67207

def z577 : W := mkw 0x0980010103802200 0x2013000202070044 0x3980070383c1e3fd 0xae73000e070783c7

def z578 : W := mkw 0x29870dd5c7e3bfa1 0xf4530e1bab8fc77f 0xb98f1fff83c1ffff 0xaf731e3fff0783ff

def z579 : W := mkw 0x20030955c7e3bf81 0xf4400612ab8fc77f 0x229118ffcfe7fffe 0xfa452231ff9fcfff

def z580 : W := mkw 0x760bb943ffc1ff05 0xf0ec177287ff83fe 0xfe0ff803ffc1fffb 0x9ffc1ff007ff83ff

def z581 : W := mkw 0x1fd008472ed60d46 0x443fa0108e5dac1a 0x3a9018cf8cc61c22 0x087520319f198c38

def z582 : W := mkw 0x000000032a940006 0x0000000006552800 0x200000038cc60020 0x0040000007198c00

def z583 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7300001e385 0xf68ac3ce600003c7

def z584 : W := mkw 0x5fd9b8037e954846 0xc0bfb37006fd2a90 0x7ff1f803fffe0078 0x7effe3f007fffc00

def z585 : W := mkw 0x298604c182c09521 0x10530c098305812a 0xb98e00c383c01c7a 0x2f731c0187078038

def z586 : W := mkw 0x560bb912fd29fa85 0xe8ac177225fa53f5 0xfe0ff803ff39fffb 0x9ffc1ff007fe73ff

def z587 : W := mkw 0x562bfb76fd6bff95 0xecac57f6edfad7ff 0xffffffffffffffff 0xffffffffffffffff

def z588 : W := mkw 0x29860dc587c2bf21 0x74530c1b8b0f857e 0xbb9e1fcf8fc7ffff 0xaf773c3f9f1f8fff

def z589 : W := mkw 0x098404c000400520 0x001308098000800a 0x998e07c000c11fef 0xaf331c0f8001823f

def z590 : W := mkw 0x1ffcd6e800400578 0x003ff9add000800a 0xdffffffc00c11fef 0xffbffffff801823f

def z591 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4561e03073380058 0x768ac3c060e67000

def z592 : W := mkw 0x0020422000000010 0x0000408440000000 0x47f1fffc00000007 0xfe8fe3fff8000000

def z593 : W := mkw 0x00030800c4019801 0xc000061001880330 0xba0f1803cc01fc3b 0x9f741e30079803f8

def z594 : W := mkw 0x40032856fc63dd85 0xc4800650adf8c7bb 0x20000003fce7fff8 0x0040000007f9cfff

def z595 : W := mkw 0x0000010001002200 0x2000000200020044 0x000007000001e385 0x8000000e000003c7

def z596 : W := mkw 0x5fdfbc8afc01d86d 0xc0bfbf7915f803b0 0xfe9ff8cffc01fc3b 0x9ffd3ff19ff803f8

def z597 : W := mkw 0x0000004000400500 0x000000008000800a 0x029000c04ce71fee 0xfa0520018099ce3f

def z598 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400000070000018 0x1608000000e00000

def z599 : W := mkw 0x0000004000400500 0x000000008000800a 0x008000c000c01c22 0x0801000180018038

def z600 : W := mkw 0x1628d22000000010 0x002c51a440000000 0xdf6fff3000000007 0xffbedffe60000000

def z601 : W := mkw 0x0984048000000020 0x0013080900000000 0x990e070000000001 0x05321c0e00000000

def z602 : W := mkw 0x5f8bb803fe81d805 0xc0bf177007fd03b0 0xff8ff803ffc1fc7b 0xbfff1ff007ff83f8

def z603 : W := mkw 0x29850dd547e32fa0 0xf4530a1baa8fc65f 0x03911ffc4fe71fee 0xfa07223ff89fce3f

def z604 : W := mkw 0x0000010001002200 0x2000000200020044 0x000000000301e3d8 0x00000000000603c7

def z605 : W := mkw 0x1608900000000000 0x002c112000000000 0x9a0e180000000002 0x09341c3000000000

def z606 : W := mkw 0x3fde95c983c0b769 0x307fbd2b9307816e 0xbb9e1fcf83c1ffff 0xaf773c3f9f0783ff

def z607 : W := mkw 0x1fdc948800000068 0x003fb92910000000 0xde9ff8cc00000003 0x9fbd3ff198000000

def z608 : W := mkw 0x40032802fc01d805 0xc080065005f803b0 0x6401e003fc01fc39 0x96c803c007f803f8

def z609 : W := mkw 0x0001211051296280 0xa800024220a252c5 0x4401e0007339e3d9 0x968803c000e673c7

def z610 : W := mkw 0x20030955c7e3bf81 0xf4400612ab8fc77f 0x20000003cfe7fff8 0x00400000079fcfff

def z611 : W := mkw 0x562bfa32fc29d895 0xc8ac57f465f853b1 0xfe6ff833fc39fc3b 0xdffcdff067f873f8

def z612 : W := mkw 0x20070dd4c563bfa1 0xf4400e1ba98ac77f 0x829f1ffc4ce7ffef 0xfb053e3ff899cfff

def z613 : W := mkw 0x1ff8d22b2a94005e 0x003ff1a456552800 0x7ff1f83ffffe0078 0x7effe3f07ffffc00

def z614 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb98e07c38300e017 0xaf731c0f870601c0

def z615 : W := mkw 0x0000004000400500 0x000000008000800a 0x029118fc00c11fee 0xfa052231f801823f

def z616 : W := mkw 0x00204374016a2790 0x2c004086e802d44f 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z617 : W := mkw 0x3ffed7e983c0b779 0x307ffdafd307816e 0xfdeee7c383c1ffff 0xaffbddcf870783ff

def z618 : W := mkw 0x1ffdf6b8502940f8 0x883ffbed70a05281 0xdffffffc70380007 0xffbffffff8e07000

def z619 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfffee703fffe0079 0x7ffffdce07fffc00

def z620 : W := mkw 0x002ddefc44630db8 0xc4005bbdf888c61b 0xc00ffffc00011f87 0x81801ffff800023f

def z621 : W := mkw 0x560a9802ac009805 0x40ac153005580130 0xfe0ff8038c001c23 0x9ffc1ff007180038

def z622 : W := mkw 0x60032943ffc1ff05 0xf0c0065287ff83fe 0x20000003ffc1fff8 0x0040000007ff83ff

def z623 : W := mkw 0x1fd4048000000060 0x003fa80900000000 0x9ffe07c000000007 0xff3ffc0f80000000

def z624 : W := mkw 0x098000032a940006 0x0013000006552800 0x39800003fffe0078 0x2e73000007fffc00

def z625 : W := mkw 0x0000014001402700 0x200000028002804e 0x018007c003c1ffff 0xae03000f800783ff

def z626 : W := mkw 0x2986048182809021 0x10530c0903050120 0xb80e000380000000 0x01701c0007000000

def z627 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0x810e07c00301ffdf 0xa7021c0f800603ff

def z628 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100070000000005 0xa602000e00000000

def z629 : W := mkw 0x09f447b8012822f8 0x2813e88f70025045 0x01f007fc033803c4 0x6003e00ff8067007

def z630 : W := mkw 0x5f8fbc82fc01d825 0xc0bf1f7905f803b0 0xff8fffc3fc01fc3f 0xbfff1fff87f803f8

def z631 : W := mkw 0x09a446a000000030 0x0013488d40000000 0xddefe7f000000007 0xffbbdfcfe0000000

def z632 : W := mkw 0x1f8000032a800004 0x003f000006550000 0x3f800003ffc00078 0x3e7f000007ff8000

def z633 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x39f0000383fe0078 0x6e73e0000707fc00

def z634 : W := mkw 0x0984048000000020 0x0013080900000000 0x988e00c000000002 0x09311c0180000000

def z635 : W := mkw 0x1fd0000102800040 0x003fa00002050000 0x3ff0000383c00078 0x7e7fe00007078000

def z636 : W := mkw 0x0001080044010800 0xc000021000880210 0x029118fc4c011c2e 0xfa052231f8980238

def z637 : W := mkw 0x0000084404420d00 0x440000108808841a 0x000000000cc61c20 0x0000000000198c38

def z638 : W := mkw 0x0000080004000800 0x4000001000080010 0x020018000c001c22 0x0804003000180038

def z639 : W := mkw 0x5659b8027c154846 0xc0acb37004f82a90 0x4671f8007c3e0000 0x508ce3f000f87c00

def z640 : W := mkw 0x7f8eb583bb80f225 0x30ff1d6b077701e4 0xfd0ee703b300e011 0x05fa1dce076601c0

def z641 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3800000380000000 0x0070000007000000

def z642 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x03f000004ffe0068 0x7a07e000009ffc00

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000003000058 0x2602000000060000

def z644 : W := mkw 0x09f446a800000078 0x0013e88d50000000 0x45f1e7fc00000005 0xf68be3cff8000000

def z645 : W := mkw 0x0002000080009001 0x0000040001000120 0x200000038001fc38 0x00400000070003f8

def z646 : W := mkw 0x160000032a940006 0x002c000006552800 0x3e000003fffe0078 0x1e7c000007fffc00

def z647 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e730733803c4 0x708ac3ce60e67007

def z648 : W := mkw 0x0020432001082210 0x2800408640021044 0x0160070003180000 0x0002c00e00063000

def z649 : W := mkw 0x1678d22800000058 0x002cf1a450000000 0x46f1f8fc00000006 0xfa8de3f1f8000000

def z650 : W := mkw 0x3ff767f3fbfdf7f7 0xb87feecfe7f7fbef 0xffffe7f3ffffffff 0xffffffcfe7ffffff

def z651 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xc40ff8007001fc1b 0x97881ff000e003f8

def z652 : W := mkw 0x3fd20143abd4b747 0x307fa4028757a96e 0x3ff00003fffffff8 0x7e7fe00007ffffff

def z653 : W := mkw 0x400ab0009000d001 0x00801560012001a0 0xc00ee0000000e001 0x01801dc0000001c0

def z654 : W := mkw 0x09d4048800000068 0x0013a80910000000 0x009000cc00000000 0x0001200198000000

def z655 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3a900003fffe0078 0x0875200007fffc00

def z656 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4161e7300339e3c5 0xe082c3ce600673c7

def z657 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff118fc00000006 0xfe3fe231f8000000

def z658 : W := mkw 0x0980004102c00500 0x001300008205800a 0x398000c383c11ffe 0xae7300018707823f

def z659 : W := mkw 0x00012954556b6f80 0xec000252a8aad6df 0x029118fc7ffffffe 0xfa052231f8ffffff

def z660 : W := mkw 0x0980000102800000 0x0013000002050000 0x3880000380c00020 0x0871000007018000

def z661 : W := mkw 0x1fd0000228140046 0x003fa00004502800 0x1ff000007c3e0000 0x7e3fe00000f87c00

def z662 : W := mkw 0x5629fb327d296a94 0xe8ac53f664fa52d5 0x4761ff307f39e3dd 0xf68ec3fe60fe73c7

def z663 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c0fc33 0x0d731c0f870781f8

def z664 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdf7fff3c00000001 0x55befffe78000000

def z665 : W := mkw 0x29860cc586c29d21 0x54530c198b0d853a 0xba9e18cf8cc61c22 0x09753c319f198c38

def z666 : W := mkw 0x0001080044010800 0xc000021000880210 0x020118004c000000 0x1004023000980000

def z667 : W := mkw 0x5ffbfb33ffbdfad7 0xe8bff7f667ff7bf5 0xffffff33ffffffff 0xfffffffe67ffffff

def z668 : W := mkw 0x0021623050294090 0x880042c460a05281 0x4001e03000000000 0x008003c060000000

def z669 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1a90000000000000 0x0835200000000000

def z670 : W := mkw 0x0020422000000010 0x0000408440000000 0x4461e03000000000 0x5088c3c060000000

def z671 : W := mkw 0x0001001040210080 0x8000020020804201 0x0001003000010384 0x8000020060000207

def z672 : W := mkw 0x562bfb22fd09fa15 0xe8ac57f645fa13f4 0xff6fff03ff19fc3b 0x9ffedffe07fe33f8

def z673 : W := mkw 0x1ffdf7b8512962f8 0xa83ffbef70a252c5 0xdffffffc0001e387 0xffbffffff80003c7

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x029118fc4ce6006e 0xfa052231f899cc00

def z675 : W := mkw 0x00216a34542b4890 0xcc0042d468a85691 0x4671f83c7c3e0000 0x508ce3f078f87c00

def z676 : W := mkw 0x0980000102800000 0x0013000002050000 0x3900000383000010 0x0472000007060000

def z677 : W := mkw 0x0001280054014800 0xc000025000a80290 0x4601f8007c01fc3b 0x9e8c03f000f803f8

def z678 : W := mkw 0x0000200010004000 0x0000004000200080 0x4400e0003000e011 0x048801c0006001c0

def z679 : W := mkw 0x1629f33051296290 0xa82c53e660a252c5 0xdf6fff307339e3df 0xffbedffe60e673c7

def z680 : W := mkw 0x298405c103c02720 0x3053080b8207804e 0x998e07c003c003c7 0xaf331c0f80078007

def z681 : W := mkw 0x40022002b800d005 0x00800440057001a0 0x20000003b000e010 0x00400000076001c0

def z682 : W := mkw 0x0001081444230880 0xc400021028884611 0x000000004c260000 0x0000000000984c00

def z683 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3f600003ff180038 0x1e7ec00007fe3000

def z684 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x000100304ce71fec 0xf20002006099ce3f

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000000103cc 0xa200000000000207

def z686 : W := mkw 0x1ffcdeec04420d78 0x443ff9bdd808841a 0xdffffffc0cc61c27 0xffbffffff8198c38

def z687 : W := mkw 0x0020433001282290 0x2800408660025045 0x05600730733803dc 0x760ac00e60e67007

def z688 : W := mkw 0x1fd008472ed60d46 0x443fa0108e5dac1a 0x3ff018cffffe1c7a 0x7e7fe0319ffffc38

def z689 : W := mkw 0x09d0000102940042 0x0013a00002052800 0x05f0000073fe0058 0x760be00000e7fc00

def z690 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x0211183c4ce71fe8 0x500422307899ce3f

def z691 : W := mkw 0x3fde94c982c09569 0x107fbd299305812a 0xba9e18cf80c01c22 0x09753c319f018038

def z692 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3d600003f3380058 0x767ac00007e67000

def z693 : W := mkw 0x1ffdf6a850014078 0x803ffbed50a00280 0xdffffffc7001e01f 0xffbffffff8e003c0

def z694 : W := mkw 0x09d1085546f70dc2 0xc413a210aa8dee1b 0x03f118fc4fff1fee 0xfa07e231f89ffe3f

def z695 : W := mkw 0x0070422800000058 0x0000e08450000000 0x0070003c00000000 0x4000e00078000000

def z696 : W := mkw 0x40236b32fd29fa95 0xe88046d665fa53f5 0x6561e733ff39fffd 0xf6cac3ce67fe73ff

def z697 : W := mkw 0x1fd0000000000040 0x003fa00000000000 0x1ff000004ce60068 0x7e3fe0000099cc00

def z698 : W := mkw 0x1609b00050014000 0x802c136000a00280 0xde0ff8007001e01b 0x9fbc1ff000e003c0

def z699 : W := mkw 0x298405c103c02720 0x3053080b8207804e 0x398007c383c003fc 0x2e73000f87078007

def z700 : W := mkw 0x298725c1d3c1f721 0xb0530e4b83a783ee 0xfd8fe7c3f3c1ffff 0xbffb1fcf87e783ff

def z701 : W := mkw 0x5fda9803ae949847 0x40bfb530075d2930 0xbffe1803fffe1c7a 0x7f7ffc3007fffc38

def z702 : W := mkw 0x40032802fc01d805 0xc080065005f803b0 0xb80e0003fc01fc3b 0x8f701c0007f803f8

def z703 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce603c4 0x70052231f899cc07

def z704 : W := mkw 0x5fde9c8aac00986d 0x40bfbd3915580130 0xba9e18cf8c001c22 0x09753c319f180038

def z705 : W := mkw 0x1ffcd7a801002278 0x203ff9af50020044 0xdffffffc0301e3df 0xffbffffff80603c7

def z706 : W := mkw 0x5fd32803fe95d847 0xc0bfa65007fd2bb0 0x3ff00003fffffc78 0x7e7fe00007fffff8

def z707 : W := mkw 0x5629fa367c2b4894 0xccac53f46cf85691 0x4671f83c7c3e0000 0x508ce3f078f87c00

def z708 : W := mkw 0x365605c2a954b767 0x306cac0b8552a96e 0x867e07c07c3fff87 0xd10cfc0f80f87fff

def z709 : W := mkw 0x40032956fd6bff85 0xec800652adfad7ff 0x20000003fffffff8 0x0040000007ffffff

def z710 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803ff39fc7b 0x9ffc1ff007fe73f8

def z711 : W := mkw 0x565bb802fc15d847 0xc0acb77005f82bb0 0xff7ff803ff3ffc7b 0xfffefff007fe7ff8

def z712 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfa0ff803fc01fc3b 0x89f41ff007f803f8

def z713 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xde9ffffc00000007 0xffbd3ffff8000000

def z714 : W := mkw 0x000000032a940006 0x0000000006552800 0x24600003fffe0078 0x5048c00007fffc00

def z715 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003fffe0030 0x5c7fe00007fffc00

def z716 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbffe07c3ffffffff 0xff7ffc0f87ffffff

def z717 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xfffffffffce6007f 0xfffffffffff9cc00

def z718 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff8fffc01fc3f 0x9ffc1ff1fff803f8

def z719 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x7d61e733f339e3fd 0xfefac3ce67e673c7

def z720 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb99e07c383e7ffff 0xef733c0f8707cfff

def z721 : W := mkw 0x298605818380b221 0x30530c0b03070164 0xb90e07038301ffff 0xaf721c0e070603ff

def z722 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffb3fe0057 0xffffffffff67fc00

def z723 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xdffffffc73fe005f 0xffbffffff8e7fc00

def z724 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xc3fffffc00000007 0xfb87fffff8000000

def z725 : W := mkw 0x00206b64154a6f10 0x6c0040d6c82a94de 0x47f0ffcc3fdefc33 0x0c8fe1ff987fbdf8

def z726 : W := mkw 0x3ffed7abab94b27f 0x307ffdaf57572964 0xfd6ee703b318e011 0x05faddce076631c0

def z727 : W := mkw 0x29a447e903c02738 0x3053488fd207804e 0x018007fc03c003c4 0x2003000ff8078007

def z728 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xff6ff803fc01fc3b 0xfffedff007f803f8

def z729 : W := mkw 0x000201008100b201 0x2000040201020164 0xb80e07038001ffbf 0x8f701c0e070003ff

def z730 : W := mkw 0x29a766f1d2e9d5b1 0x98534ecde3a5d3ab 0xfcefe0f3f0f81c22 0x59f9dfc1e7e1f038

def z731 : W := mkw 0x29870d95c7a3baa1 0xf4530e1b2b8f4775 0xbb1f1f3fcf26e011 0x55763e3e7f9e4dc0

def z732 : W := mkw 0x200605c183c0b721 0x30400c0b8307816e 0xb80e07c383c1ffff 0x8f701c0f870783ff

def z733 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb8e07c3cfc1ffff 0xbf771c0f879f83ff

def z734 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xc21ffffc00000007 0x81843ffff8000000

def z735 : W := mkw 0x167cd6aa2814007e 0x002cf9ad54502800 0xc67ffffc7c3e0007 0xd18cfffff8f87c00

def z736 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1fffd 0x25731c0f870783ff

def z737 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xd90ffffc00000007 0x85b21ffff8000000

def z738 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01fc3a 0x19fc1ff007f803f8

def z739 : W := mkw 0x560bb812fc29d885 0xc8ac177025f853b1 0xfe0ff803fc39fc3b 0x9ffc1ff007f873f8

def z740 : W := mkw 0x1fddb598512962e8 0xa83fbb6b30a252c5 0x9a9e18cc7339e3da 0x09353c3198e673c7

def z741 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ee003b001fc11 0x05f81dc0076003f8

def z742 : W := mkw 0x1ffddefc44630df8 0xc43ffbbdf888c61b 0xdd6ee7004ce71fe9 0x05baddce0099ce3f

def z743 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e3d9 0x548ac3ce60e673c7

def z744 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xfffffffff3f8007f 0xffffffffffe7f000

def z745 : W := mkw 0x09acd6a902800038 0x001359ad52050000 0xf98fffff83c0007f 0xaff31fffff078000

def z746 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe6ff803fc39fc3b 0xdffcdff007f873f8

def z747 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4771ff3c7339e3dd 0xf68ee3fe78e673c7

def z748 : W := mkw 0x165000032a940046 0x002ca00006552800 0x26f00003fffe0078 0x7a4de00007fffc00

def z749 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c38301ff97 0xaf731c0f870603ff

def z750 : W := mkw 0x0001285454634d80 0xc4000250a8a8c69b 0x4291f8fc4ce7ffef 0xfa8523f1f899cfff

def z751 : W := mkw 0x00012854546b4d80 0xcc000250a8a8d69b 0x029118fc7cff1fee 0xfa052231f8f9fe3f

def z752 : W := mkw 0x2002014183c0b701 0x304004028307816e 0xb90e070383c1ffff 0xaf721c0e070783ff

def z753 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc0cc71fee 0xaa052231f8198e3f

def z754 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfffffffffcc6003f 0xfffffffffff98c00

def z755 : W := mkw 0x29f447f903e827f8 0x3853e88ff207d04f 0x01f007fc03f803c4 0x6003e00ff807f007

def z756 : W := mkw 0x098000032a940006 0x0013000006552800 0x3de00003fffe0078 0x7e7bc00007fffc00

def z757 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc00fc33 0x1dfc1ff007f801f8

def z758 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1ffe7 0xa9731c0f870783ff

def z759 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb88e07c380c1ffbf 0x8f711c0f870183ff

def z760 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4560e7007339e3d9 0x768ac1ce00e673c7

def z761 : W := mkw 0x49f76eaafc01d87d 0xc093eedd55f803b0 0x21f007fffc01fc3c 0x6043e00ffff803f8

def z762 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xffffffff83fe007f 0xffffffffff07fc00

def z763 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0fe003fc01fc39 0x97f81fc007f803f8

def z764 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e07c383c1ffff 0x85721c0f870783ff

def z765 : W := mkw 0x565bb802fc15d847 0xc0acb77005f82bb0 0xfe6ff803fc19fc3b 0x9ffcdff007f833f8

def z766 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9f1fffcfe7ffff 0xff773e3fff9fcfff

def z767 : W := mkw 0x162cd6aa2800003c 0x002c59ad54500000 0xfe0ffffffc00003f 0x9ffc1ffffff80000

def z768 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ff803fc01fc3b 0x85f81ff007f803f8

def z769 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fee 0x88052231f899ce3f

def z770 : W := mkw 0x0001210051016200 0xa000024200a202c4 0x4561e7007339e3dd 0xf68ac3ce00e673c7

def z771 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0xb88e07c380c1ffff 0xaf711c0f870183ff

def z772 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe0ff803fc27fc3b 0x9ffc1ff007f84ff8

def z773 : W := mkw 0x560bb002f801d005 0x80ac176005f003a0 0xfc0fe003f001fc3b 0x9ff81fc007e003f8

def z774 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfe0ee003fc01fc3b 0x9ffc1dc007f803f8

def z775 : W := mkw 0x29d605c183d4b763 0x3053ac0b8307a96e 0xbdfe07c3f3ffffff 0xff7bfc0f87e7ffff

def z776 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc4c260007 0xffbffffff8984c00

def z777 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307338e3d5 0x748ac3ce60e671c7

def z778 : W := mkw 0x560ab056b862d585 0x04ac1560ad70c5ab 0xfc9ee0ffb0e6e3d5 0x65f93dc1ff61cdc7

def z779 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff8038c01fc23 0x9ffc1ff0071803f8

def z780 : W := mkw 0x1ffcd6ab2a80007c 0x003ff9ad56550000 0xffffffffffc0007f 0xffffffffffff8000

def z781 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xfffffffffc3e003f 0xfffffffffff87c00

def z782 : W := mkw 0x565bb802fc01d845 0xc0acb77005f803b0 0xfe7ff803fc01fc3b 0xdffcfff007f803f8

def z783 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xbffe0003fffe0078 0x7f7ffc0007fffc00

def z784 : W := mkw 0x09d000032a940046 0x0013a00006552800 0x21600003fffe0078 0x0042c00007fffc00

def z785 : W := mkw 0x0000084404420d00 0x440000108808841a 0x029118fc0cc71fee 0xfa052231f8198e3f

def z786 : W := mkw 0x49dbb801d695d843 0xc093b77003ad2bb0 0xc1fff80003fffc43 0xe183fff00007fff8

def z787 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0xbffe0003fffe007b 0xff7ffc0007fffc00

def z788 : W := mkw 0x29f447fd03e227f8 0x3453e88ffa07c44f 0x01f007fc03e603c4 0x6003e00ff807cc07

def z789 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xc7fffffc00000007 0xf18ffffff8000000

def z790 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4560e7307339e3dd 0x648ac1ce60e673c7

def z791 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffff8fc6007f 0xffffffffff1f8c00

def z792 : W := mkw 0x29d605c183c0b761 0x3053ac0b8307816e 0xb9fe07c383c1ffff 0xef73fc0f870783ff

def z793 : W := mkw 0x1fd108576ef70dc6 0xc43fa210aeddee1b 0x3d6118ffb3191f96 0x847ac231ff66323f

def z794 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe1ff83ffc01fc3b 0xdffc3ff07ff803f8

def z795 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7303319e3dd 0xa68ac3ce606633c7

def z796 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x4771ff3c7f3fffff 0xfe8ee3fe78fe7fff

def z797 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfffff803fffffc7b 0xfffffff007fffff8

def z798 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x03f118fc4fff1fee 0xfa07e231f89ffe3f

def z799 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xc5fffffc00000007 0xf78bfffff8000000

def z800 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce61fe6 0x78052231f899cc3f

def z801 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff8fffce7fc7f 0xfffd3ff1fff9cff8

def z802 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xffffffffff38007f 0xfffffffffffe7000

def z803 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xde7ffffc00000007 0xdfbcfffff8000000

def z804 : W := mkw 0x1fd404832a940066 0x003fa80906552800 0x3ff007c3fffe007c 0x7e7fe00f87fffc00

def z805 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803bc01fc33 0x8dfc1ff0077803f8

def z806 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfa0ff803cc01fc2b 0x9bf41ff0079803f8

def z807 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1fffe 0x29731c0f870783ff

def z808 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4561e7303338e3d5 0xf68ac3ce606671c7

def z809 : W := mkw 0x367ad36983c0b759 0x306cf5a6d307816e 0x6671f83f83c1fff8 0x50cce3f07f0783ff

def z810 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xc18ffffc00000007 0xa1831ffff8000000

def z811 : W := mkw 0x1fd890032a940046 0x003fb12006552800 0xbffe1803fffe007a 0x7f7ffc3007fffc00

def z812 : W := mkw 0x002cd6ab2a94003e 0x000059ad56552800 0xe00ffffffffe007f 0x81c01ffffffffc00

def z813 : W := mkw 0x1fd890032a940046 0x003fb12006552800 0xfffff8fffffe007f 0xfffffff1fffffc00

def z814 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xda0ffffc00000007 0x89b41ffff8000000

def z815 : W := mkw 0x402bfb74d56bff91 0xec8057f6e9aad7ff 0xc00ffffc0001ff87 0x81801ffff80003ff

def z816 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4560e7003319e391 0x048ac1ce006633c7

def z817 : W := mkw 0x000000032a940006 0x0000000006552800 0x25600003fffe0078 0x044ac00007fffc00

def z818 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3bf00003fffe0078 0x6877e00007fffc00

def z819 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff833fc01fc3f 0xfffc1ff067f803f8

def z820 : W := mkw 0x005000032a940046 0x0000a00006552800 0x20700003fffe0078 0x4040e00007fffc00

def z821 : W := mkw 0x29a447f503ea27b0 0x3c53488fea07d44f 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z822 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff018cffffe007a 0x7e7fe0319ffffc00

def z823 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x47f1e7307339e3dd 0xfe8fe3ce60e673c7

def z824 : W := mkw 0x20032955d7ebff81 0xfc400652abafd7ff 0x20000003fffffff8 0x0040000007ffffff

def z825 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00000005 0x75bffffff8000000

def z826 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4561e7303319e3dd 0xf68ac3ce606633c7

def z827 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x45e1e73073f9e3fd 0xfe8bc3ce60e7f3c7

def z828 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xc46ffffc00000007 0x8188dffff8000000

def z829 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfc0ef803b000fc13 0x05f81df0076001f8

def z830 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9e07c38fc7ffff 0xaf773c0f871f8fff

def z831 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307319e39d 0x968ac3ce60e633c7

def z832 : W := mkw 0x29f447e903d4277a 0x3053e88fd207a84e 0x01f007fc03fe03c4 0x6003e00ff807fc07

def z833 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfc0ee003b001fc13 0x85f81dc0076003f8

def z834 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc21ffffc00000007 0xd1843ffff8000000

def z835 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0xdd6fe7307339e3df 0xffbadfce60e673c7

def z836 : W := mkw 0x09a446a000000030 0x0013488d40000000 0xdffffffc00000007 0xffbffffff8000000

def z837 : W := mkw 0x0000085404620d80 0x44000010a808c41b 0x029118fc0ce61fe6 0xfa052231f819cc3f

def z838 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdd6ffffc00000007 0xf7badffff8000000

def z839 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe0ff803fc21fffb 0x9ffc1ff007f843ff

def z840 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc000103cf 0xffbffffff8000207

def z841 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce7ffff 0xfe052231f899cfff

def z842 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb99e07ff83c1ffff 0xef733c0fff0783ff

def z843 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e070383c1fffb 0x8f721c0e070783ff

def z844 : W := mkw 0x1ff163337bbd62d6 0xa83fe2c666f77ac5 0x7a91e7338cc7e3a5 0x88f523ce67198fc7

def z845 : W := mkw 0x40032802fc01d805 0xc080065005f803b0 0xfc0fe003fc01fc3b 0x9ff81fc007f803f8

def z846 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffff18003f 0xfffffffffffe3000

def z847 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfd6fffffb3180017 0x85fadfffff663000

def z848 : W := mkw 0x160a900080009001 0x002c152001000120 0xfc0ee0038001fc3b 0x8ff81dc0070003f8

def z849 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xdffffffc0c060007 0xffbffffff8180c00

def z850 : W := mkw 0x0980000102800000 0x0013000002050000 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z851 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc0cc60027 0xffbffffff8198c00

def z852 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc09ffffc00000007 0xe1813ffff8000000

def z853 : W := mkw 0x565bb802fc15d847 0xc0acb77005f82bb0 0xfe1ff803fc07fc3b 0x9ffc3ff007f80ff8

def z854 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc7fff1ffe 0xfa052231f8fffe3f

def z855 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdb9ffffc00000007 0xafb73ffff8000000

def z856 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x3a9118ffcce71ffe 0xfe752231ff99ce3f

def z857 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4560e7303318e395 0x048ac1ce606631c7

def z858 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x039118fc4fe71ffe 0xfe072231f89fce3f

def z859 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc00ffffc00000007 0xf3801ffff8000000

def z860 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561fffc7339e3df 0xf68ac3fff8e673c7

def z861 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e3dd 0x848ac3ce60e673c7

def z862 : W := mkw 0x0000085404620d80 0x44000010a808c41b 0x029018fc4ce61fee 0x7a052031f899cc3f

def z863 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbd8e07c3f3c1ffff 0xbf7b1c0f87e783ff

def z864 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xdf6ffffc00000007 0xffbedffff8000000

def z865 : W := mkw 0x562adb32ad28ba95 0x68ac55b6655a5175 0xbb6e1f338f381fe6 0x6976dc3e671e703f

def z866 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfffffffff338005f 0xffffffffffe67000

def z867 : W := mkw 0x1fd404832a940066 0x003fa80906552800 0xbfff1ffffffe007f 0xff7ffe3ffffffc00

def z868 : W := mkw 0x000000032a940006 0x0000000006552800 0x21600003fffe0078 0x6042c00007fffc00

def z869 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00e60047 0xffbffffff801cc00

def z870 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc10ffffc00000007 0xa7821ffff8000000

def z871 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc4c00002f 0xffbffffff8980000

def z872 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x4561ff307339ffdf 0xf68ac3fe60e673ff

def z873 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xfa0ff803cc01fc3b 0x9ff41ff0079803f8

def z874 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xc09ffffc00000007 0x81813ffff8000000

def z875 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98f1fff83c1ffff 0xaf731e3fff0783ff

def z876 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3f700003fffe0078 0x547ee00007fffc00

def z877 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdf6ffffc00000007 0x9fbedffff8000000

def z878 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc0cc71fa6 0xfa052231f8198e3f

def z879 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x4561ff3c7339e3dd 0xf68ac3fe78e673c7

def z880 : W := mkw 0x165000032a940046 0x002ca00006552800 0x27700003fffe0078 0x764ee00007fffc00

def z881 : W := mkw 0x00216334512b6290 0xac0042c668a256c5 0x4571e73c733fe3dd 0xf68ae3ce78e67fc7

def z882 : W := mkw 0x000000032a940006 0x0000000006552800 0x27f00003fffe0078 0x7e4fe00007fffc00

def z883 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xff0fff03fc01fc3f 0xbffe1ffe07f803f8

def z884 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e3dc 0x708ac3ce60e673c7

def z885 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xda9ffffc00000007 0xfbb53ffff8000000

def z886 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fa6 0xd8052231f899ce3f

def z887 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfe0ff803bc00fc33 0x9ffc1ff0077801f8

def z888 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e070383c1fffd 0xa7721c0e070783ff

def z889 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3df00003fffe0078 0x647be00007fffc00

def z890 : W := mkw 0x160bb000d001d001 0x802c176001a003a0 0xfe0ff803f001fc3b 0x9ffc1ff007e003f8

def z891 : W := mkw 0x09d000032a940046 0x0013a00006552800 0x39f00003fffe0078 0x6e73e00007fffc00

def z892 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc4020004f 0xffbffffff8804000

def z893 : W := mkw 0x29d605c183d4b763 0x3053ac0b8307a96e 0xb9ee07c383d9ffff 0xaf73dc0f8707b3ff

def z894 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ee003fc01fc3b 0x8ff81dc007f803f8

def z895 : W := mkw 0x29d605c183d4b763 0x3053ac0b8307a96e 0xb99e07c383c7ffff 0xaf733c0f87078fff

def z896 : W := mkw 0x160b9800c4019801 0xc02c173001880330 0xfe0ff803cc01fc3b 0x9ffc1ff0079803f8

def z897 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003fffe0050 0x747fe00007fffc00

def z898 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4cc71fae 0x9a052231f8998e3f

def z899 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01fc39 0x15fc1ff007f803f8

def z900 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xfd8fe7c383c1ffff 0xbffb1fcf870783ff

def z901 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3d600003fffe0078 0x767ac00007fffc00

def z902 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb80e07c38001ff87 0x81701c0f870003ff

def z903 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe9ff833fce7ffff 0xfffd3ff067f9cfff

def z904 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc29ffffc4ce6006f 0xfb853ffff899cc00

def z905 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xdb9ffffc00000007 0xffb73ffff8000000

def z906 : W := mkw 0x098201018380b201 0x2013040203070164 0xb98e070383c1ffff 0xaf731c0e070783ff

def z907 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff803fc01fc3b 0xfffd3ff007f803f8

def z908 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003ffff1c7a 0xfe7fe00007fffe38

def z909 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xdffffffc00c60007 0xffbffffff8018c00

def z910 : W := mkw 0x160a9002a8009005 0x002c152005500120 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z911 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfe0ff803b001fc3b 0x9ffc1ff0076003f8

def z912 : W := mkw 0x1fd4048b2a94006e 0x003fa80916552800 0x3ff000cffffe0078 0x7e7fe0019ffffc00

def z913 : W := mkw 0x1f8c948000000020 0x003f192900000000 0xdf9ffffc00000007 0xffbf3ffff8000000

def z914 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff11803fffe007a 0xfe7fe23007fffc00

def z915 : W := mkw 0x29f447e903c02778 0x3053e88fd207804e 0x01e007c003c003c4 0x2003c00f80078007

def z916 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc70380007 0xffbffffff8e07000

def z917 : W := mkw 0x560bb800d401d801 0xc0ac177001a803b0 0xfe0ff8038001fc3b 0x9ffc1ff0070003f8

def z918 : W := mkw 0x0001285454634d80 0xc4000250a8a8c69b 0x029118fc7ce7fffe 0xfa052231f8f9cfff

def z919 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc46ffffc00000007 0xd188dffff8000000

def z920 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xff6ff803ff19fc3b 0x9ffedff007fe33f8

def z921 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x45e1e7f07339e3df 0xfe8bc3cfe0e673c7

def z922 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfa0ff8038c01fc3b 0x8ff41ff0071803f8

def z923 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4560e7003338e3d1 0x048ac1ce006671c7

def z924 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xf80ff8038001fc13 0x85f01ff0070003f8

def z925 : W := mkw 0x16032002f801d005 0x802c064005f003a0 0xfe0fe003fc01fc3b 0x9ffc1fc007f803f8

def z926 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x47f1fffc7fffe3ff 0xfe8fe3fff8ffffc7

def z927 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xdffffffc03c00047 0xffbffffff8078000

def z928 : W := mkw 0x1ffcd6a80014007a 0x003ff9ad50002800 0xdffffffc003e0007 0xffbffffff8007c00

def z929 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xffffffff80c00027 0xffffffffff018000

def z930 : W := mkw 0x298605c583c2b721 0x34530c0b8b07856e 0xb99e07cf83c7ffff 0xaf733c0f9f078fff

def z931 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff000c3fffe007e 0xfe7fe00187fffc00

def z932 : W := mkw 0x1fd890032a940046 0x003fb12006552800 0xfffee003fffe0079 0x7ffffdc007fffc00

def z933 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffb3d8007f 0xffffffffff67b000

def z934 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdbfffffc00000007 0xe9b7fffff8000000

def z935 : W := mkw 0x560bb802fc15d807 0xc0ac177005f82bb0 0xfe0ff803fc3ffc3b 0x9ffc1ff007f87ff8

def z936 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ee003fc01fc39 0x1ffc1dc007f803f8

def z937 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe9ff83ffce7fc7b 0xfffd3ff07ff9cff8

def z938 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff803fcc7fc3b 0x9ffd3ff007f98ff8

def z939 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4761ff307339e3df 0xfe8ec3fe60e673c7

def z940 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc56ffffc00000007 0x858adffff8000000

def z941 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4560e7303339e3dd 0xe68ac1ce606673c7

def z942 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc20ffffc00000007 0x9b841ffff8000000

def z943 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x4761ff307f39e3dd 0xf68ec3fe60fe73c7

def z944 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb88e07c383c1ffff 0x89711c0f870783ff

def z945 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4771e7307f3fe3dd 0xf68ee3ce60fe7fc7

def z946 : W := mkw 0x09d000032a940046 0x0013a00006552800 0x23f00003fffe0078 0x7a47e00007fffc00

def z947 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x27f00003fffe0078 0x704fe00007fffc00

def z948 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xd88ffffc00000007 0x89b11ffff8000000

def z949 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307fffe3fd 0xf68ac3ce60ffffc7

def z950 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe8ff803fcc1fc7b 0xbffd1ff007f983f8

def z951 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7003319e3d9 0x048ac1ce006633c7

def z952 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe1ff803fc27fc3b 0xdffc3ff007f84ff8

def z953 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x4691f8fc4ce71fef 0xfe8d23f1f899ce3f

def z954 : W := mkw 0x000a900080009001 0x0000152001000120 0xf80ff8038001fc3b 0x8ff01ff0070003f8

def z955 : W := mkw 0x7fde9cc3aed49d67 0x50ffbd39875da93a 0xba9e18c38cc61c22 0x09753c3187198c38

def z956 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xdffffffc7c000007 0xffbffffff8f80000

def z957 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ff803f001fc1b 0x97f81ff007e003f8

def z958 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc56ffffc7338005f 0xf78adffff8e67000

def z959 : W := mkw 0x5629fa327c294894 0xc8ac53f464f85291 0x4601f8307c000000 0x108c03f060f80000

def z960 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00703fffe007d 0xfe7fe00e07fffc00

def z961 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc33180017 0xffbffffff8663000

def z962 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc03380047 0xffbffffff8067000

def z963 : W := mkw 0x29d605c983c0b769 0x3053ac0b9307816e 0xb99e07cf83c1ffff 0xaf733c0f9f0783ff

def z964 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0xb80e07c38001ffa7 0x89701c0f870003ff

def z965 : W := mkw 0x29a447e103c82730 0x3853488fc207904e 0x01e007c003d803c4 0x2003c00f8007b007

def z966 : W := mkw 0x7f8dbdc37fc16f24 0xf0ff1b7b86ff82de 0x4781ffc07fc003c4 0x308f03ff80ff8007

def z967 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e07c38301ffdf 0xa7721c0f870603ff

def z968 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbdee07c3b3d9ffff 0xaf7bdc0f8767b3ff

def z969 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00011c2f 0xffbffffff8000238

def z970 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7003319e395 0x848ac1ce006633c7

def z971 : W := mkw 0x1fdc94832a940066 0x003fb92906552800 0xffffffc3fffe007f 0xffffffff87fffc00

def z972 : W := mkw 0x0021632051096210 0xa80042c640a212c4 0x4561e7007319e3dd 0xb68ac3ce00e633c7

def z973 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00c0006f 0xffbffffff8018000

def z974 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc21fc7b 0xfffc1ff007f843f8

def z975 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9e07c383c1ffff 0xff773c0f870783ff

def z976 : W := mkw 0x1fd404832a940066 0x003fa80906552800 0xbffe00c3fffe007a 0x7f7ffc0187fffc00

def z977 : W := mkw 0x565bb802fc15d847 0xc0acb77005f82bb0 0xfefff803fcfffc7b 0xfffdfff007f9fff8

def z978 : W := mkw 0x565bb80afc01d84d 0xc0acb77015f803b0 0xfe1ff80ffc01fc3b 0x9ffc3ff01ff803f8

def z979 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1ffd7 0xa5731c0f870783ff

def z980 : W := mkw 0x5679fa327c3d48d6 0xc8acf3f464f87a91 0x4671f8307c3e0000 0x508ce3f060f87c00

def z981 : W := mkw 0x09fcd6a90294007a 0x0013f9ad52052800 0xc1fffffc03fe0047 0xe183fffff807fc00

def z982 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff1183ffffe0078 0x7e7fe2307ffffc00

def z983 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e07038301ff91 0x05721c0e070603ff

def z984 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7003318e3d5 0x248ac1ce006631c7

def z985 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3f600003fffe0078 0x1e7ec00007fffc00

def z986 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xbffe1fcffffe007f 0xff7ffc3f9ffffc00

def z987 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe0ff833fc21fc3b 0xdffc1ff067f843f8

def z988 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xf80ff8038001fc03 0x81f01ff0070003f8

def z989 : W := mkw 0x1fd404832a940066 0x003fa80906552800 0xbffe0703fffe0079 0x7f7ffc0e07fffc00

def z990 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfa9fffff8cc60027 0x89f53fffff198c00

def z991 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xffffffff8c000027 0xffffffffff180000

def z992 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x47f1fffc7f39ffff 0xfe8fe3fff8fe73ff

def z993 : W := mkw 0x1600000228000004 0x002c000004500000 0x3ff00003fffe0078 0x7e7fe00007fffc00

def z994 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803b001fc13 0x9ffc1ff0076003f8

def z995 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xc6fffffc00000007 0xfb8dfffff8000000

def z996 : W := mkw 0x0000004000400500 0x000000008000800a 0x029118fc4ce71fee 0xfa052231f899ce3f

def z997 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003ffff03fc 0xfe7fe00007fffe07

def z998 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fce7fc7b 0x9ffc1ff007f9cff8

def z999 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xdffffffc03180007 0xffbffffff8063000

def z1000 : W := mkw 0x09acd6a800000038 0x001359ad50000000 0xddeffffc00000007 0xffbbdffff8000000

def z1001 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe1ff83ffc27ffff 0xfffc3ff07ff84fff

def z1002 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb8f1fc383c1ffff 0xbf771e3f870783ff

def z1003 : W := mkw 0x098604c080409521 0x00130c098100812a 0xb98e07c380c1ffff 0xaf731c0f870183ff

def z1004 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339ffff 0xfe8ac3ce60e673ff

def z1005 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb90e07c38301ffbf 0x8f721c0f870603ff

def z1006 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xf80ff8038001fc23 0x89f01ff0070003f8

def z1007 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xdc0ffffc00000007 0x85b81ffff8000000

def z1008 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x9a9f18fc4ce71fef 0xff353e31f899ce3f

def z1009 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xd80ffffc00000007 0x8fb01ffff8000000

def z1010 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x4561e7307f39fffd 0xf68ac3ce60fe73ff

def z1011 : W := mkw 0x560a9802ac009805 0x40ac153005580130 0xfe0ff8038c01fc3b 0x9ffc1ff0071803f8

def z1012 : W := mkw 0x1628d22000000010 0x002c51a440000000 0xdffffffc00000007 0xffbffffff8000000

def z1013 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbdee07c383c1ffff 0xff7bdc0f870783ff

def z1014 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xff6ff833ff39ffff 0xfffedff067fe73ff

def z1015 : W := mkw 0x1ffcd6aa2800007c 0x003ff9ad54500000 0xffffffffb0000017 0xffffffffff600000

def z1016 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc7000001f 0xffbffffff8e00000

def z1017 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0xb90e07c38301ffff 0xaf721c0f870603ff

def z1018 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1ffb7 0x8d731c0f870783ff

def z1019 : W := mkw 0x09d000032a940046 0x0013a00006552800 0x25f00003fffe0078 0x764be00007fffc00

def z1020 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xffffffff83000017 0xffffffffff060000

def z1021 : W := mkw 0x60032957ffe3ff85 0xf4c00652afffc7ff 0x20000003ffe7fff8 0x0040000007ffcfff

def z1022 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc0001e01f 0xffbffffff80003c0

def z1023 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe9ff8fffc27fc3f 0xfffd3ff1fff84ff8

def z1024 : W := mkw 0x165000032a940046 0x002ca00006552800 0x3e700003fffe0078 0x5e7ce00007fffc00

def z1025 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ef803fc01fc3b 0x0dfc1df007f803f8

def z1026 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xc16ffffc00000007 0x8182dffff8000000

def z1027 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c3f3f9ffff 0xaf731c0f87e7f3ff

def z1028 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdefffffc00000007 0xd9bdfffff8000000

def z1029 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7007339e3d9 0x968ac3ce00e673c7

def z1030 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c383c1fffb 0x0d731c0f870783ff

def z1031 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7303319e395 0xf68ac3ce606633c7

def z1032 : W := mkw 0x000220009000d001 0x00000440012001a0 0xfc0ee003b001fc3b 0x8ff81dc0076003f8

def z1033 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c380c1ffa7 0xaf731c0f870183ff

def z1034 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fea 0x58052231f899ce3f

def z1035 : W := mkw 0x00032800d401d801 0xc000065001a803b0 0xfe0ff803fc01fc3b 0x9ffc1ff007f803f8

def z1036 : W := mkw 0x560bb806fc03d805 0xc4ac17700df807b0 0xfe1ff80ffc07fc3b 0x9ffc3ff01ff80ff8

def z1037 : W := mkw 0x0001285454634d80 0xc4000250a8a8c69b 0x4691f8fc7ce71fee 0xfa8d23f1f8f9ce3f

def z1038 : W := mkw 0x3fde94cbaad4956f 0x107fbd299755a92a 0xba9e18cf8cc61c22 0x09753c319f198c38

def z1039 : W := mkw 0x00032000d001d001 0x8000064001a003a0 0xf80fe0038001fc3b 0x8ff01fc0070003f8

def z1040 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x7ff1e003fffe0079 0xfeffe3c007fffc00

def z1041 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00000006 0x79bffffff8000000

def z1042 : W := mkw 0x298605c08140b721 0x30530c0b8102816e 0xb98e07c38001ffbf 0xaf731c0f870003ff

def z1043 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e3c5 0xf08ac3ce60e673c7

def z1044 : W := mkw 0x165000032a940046 0x002ca00006552800 0x24600003fffe0078 0x0048c00007fffc00

def z1045 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc0300005f 0xffbffffff8060000

def z1046 : W := mkw 0x200605c08140b721 0x30400c0b8102816e 0xb80e07c38001ff97 0x85701c0f870003ff

def z1047 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xffffffff8000003f 0xffffffffff000000

def z1048 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffff80000007 0xffffffffff000000

def z1049 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc29ffffc00000007 0x89853ffff8000000

def z1050 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003fffe0060 0x787fe00007fffc00

def z1051 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7303339e3d5 0xe48ac3ce606673c7

def z1052 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb9ee07c383f9ffff 0xef73dc0f8707f3ff

def z1053 : W := mkw 0x1ffcd6a902800078 0x003ff9ad52050000 0xffffffffcfe6007f 0xffffffffff9fcc00

def z1054 : W := mkw 0x098605808100b221 0x20130c0b01020164 0xb98e07c38301ffff 0xaf731c0f870603ff

def z1055 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x47f1fffc7f3fe3df 0xfe8fe3fff8fe7fc7

def z1056 : W := mkw 0x007cd6a800000078 0x0000f9ad50000000 0xc07ffffc00000007 0xc180fffff8000000

def z1057 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c3cfe7ffff 0xaf731c0f879fcfff

def z1058 : W := mkw 0x162cd6a800000038 0x002c59ad50000000 0xc60ffffc00000007 0x918c1ffff8000000

def z1059 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01fc13 0x95fc1ff007f803f8

def z1060 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xde9ffffc00000007 0x9fbd3ffff8000000

def z1061 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x06f118fc7cff1fee 0xfa0de231f8f9fe3f

def z1062 : W := mkw 0x00216b3055296a90 0xe80042d660aa52d5 0x47f1ff307fffffff 0xfe8fe3fe60ffffff

def z1063 : W := mkw 0x560bb816fc23d885 0xc4ac17702df847b1 0xfe0ff83ffc01fc3b 0x9ffc1ff07ff803f8

def z1064 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x07f118fc4ce71fee 0xfe0fe231f899ce3f

def z1065 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xbb9e1fcf83c1ffff 0xaf773c3f9f0783ff

def z1066 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xfffff8cffffe007b 0xfffffff19ffffc00

def z1067 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xddfffffc00000007 0xe5bbfffff8000000

def z1068 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e070383c1fff9 0x2f731c0e070783ff

def z1069 : W := mkw 0x1fd890032a940046 0x003fb12006552800 0x7ff1f803fffe0078 0x7effe3f007fffc00

def z1070 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4560e7007339e3dd 0xa68ac1ce00e673c7

def z1071 : W := mkw 0x29a447f103e827b0 0x3853488fe207d04f 0x018007f003c003c4 0x2003000fe0078007

def z1072 : W := mkw 0x0002000080009001 0x0000040001000120 0xfc0fe0038001fc3b 0x9ff81fc0070003f8

def z1073 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4761e7307f39e3fd 0xfe8ec3ce60fe73c7

def z1074 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc08ffffc00000007 0xab811ffff8000000

def z1075 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98e07c3c3e1ffff 0xff731c0f8787c3ff

def z1076 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x4561e7307f3fe3dd 0xf68ac3ce60fe7fc7

def z1077 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb88e07c380c1ffef 0xab711c0f870183ff

def z1078 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x45f1e7fc7339e3dd 0xf68be3cff8e673c7

def z1079 : W := mkw 0x00216b34552b6a90 0xec0042d668aa56d5 0x47f1ff3c7fffe3fd 0xfe8fe3fe78ffffc7

def z1080 : W := mkw 0x29a447e103c02730 0x3053488fc207804e 0x01e007f003c003c4 0x6003c00fe0078007

def z1081 : W := mkw 0x160000032a940006 0x002c000006552800 0x3f600003fffe0078 0x7e7ec00007fffc00

def z1082 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ef00003fffe0078 0x587de00007fffc00

def z1083 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffff3e0017 0xfffffffffffe7c00

def z1084 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003ffffe079 0xfe7fe00007ffffc0

def z1085 : W := mkw 0x565bb816fc37d8c7 0xc4acb7702df86fb1 0xfe7ff83ffc3ffc3b 0xdffcfff07ff87ff8

def z1086 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc0ce71fe6 0xe8052231f819ce3f

def z1087 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe9ff8fffc21ffff 0xfffd3ff1fff843ff

def z1088 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff10033fffe007c 0xfe7fe20067fffc00

def z1089 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffcce6006f 0xffffffffff99cc00

def z1090 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x4561e7307339e395 0xd48ac3ce60e673c7

def z1091 : W := mkw 0x29f447f103fc27f2 0x3853e88fe207f84f 0x01f007f003fe03c4 0x6003e00fe007fc07

def z1092 : W := mkw 0x400bb800d401d801 0xc080177001a803b0 0xfc0ff803f001fc3b 0x9ff81ff007e003f8

def z1093 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff00003fffe0078 0x0c7fe00007fffc00

def z1094 : W := mkw 0x5679fa3a7c2948dc 0xc8acf3f474f85291 0x4671f83c7c380000 0x508ce3f078f87000

def z1095 : W := mkw 0x1fd8900b2a94004e 0x003fb12016552800 0x3ff0180ffffe0078 0x7e7fe0301ffffc00

def z1096 : W := mkw 0x0001285454634d80 0xc4000250a8a8c69b 0x47f1f8fc7fffffff 0xfe8fe3f1f8ffffff

def z1097 : W := mkw 0x000201408140b701 0x200004028102816e 0xb98e07c383c1ffff 0xaf731c0f870783ff

def z1098 : W := mkw 0x400ab0009000d001 0x00801560012001a0 0xf80ee0038001fc3b 0x8ff01dc0070003f8

def z1099 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfc0ee003bc00fc31 0x05f81dc0077801f8

def z1100 : W := mkw 0x400bb802fc01d805 0xc080177005f803b0 0xf80ff803fc01fc3b 0x8ff01ff007f803f8

def z1101 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc7fffffc00000007 0xff8ffffff8000000

def z1102 : W := mkw 0x29d605c183d4b763 0x3053ac0b8307a96e 0xbbfe07c3cfffffff 0xff77fc0f879fffff

def z1103 : W := mkw 0x0020632011086210 0x280040c6402210c4 0x4560e7007339e3dd 0xf68ac1ce00e673c7

def z1104 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfc0ee003b000fc33 0x0df81dc0076001f8

def z1105 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfe0ef803fc00fc3b 0x1ffc1df007f801f8

def z1106 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xdffffffc30180007 0xffbffffff8603000

def z1107 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fc6 0xf0052231f899ce3f

def z1108 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00000007 0x8dbffffff8000000

def z1109 : W := mkw 0x298605c183c0b721 0x30530c0b8307816e 0xb98f07f383c1ffff 0xff731e0fe70783ff

def z1110 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029018fc4ce71fee 0x68052031f899ce3f

def z1111 : W := mkw 0x0020432001002210 0x2000408640020044 0x4561e7307339e3dd 0xf68ac3ce60e673c7

def z1112 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3ff000fffffe007c 0x7e7fe001fffffc00

def z1113 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xdffffffc7f3e005f 0xffbffffff8fe7c00

def z1114 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc00000003 0x5dbffffff8000000

def z1115 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdffffffc7ffe007f 0xffbffffff8fffc00

def z1116 : W := mkw 0x1fd000032a940046 0x003fa00006552800 0x3de00003fffe0078 0x2e7bc00007fffc00

def z1117 : W := mkw 0x1fdc948b2a94006e 0x003fb92916552800 0xbfff18fffffe007e 0xff7ffe31fffffc00

def z1118 : W := mkw 0x0020633011286290 0x280040c6602250c5 0x4560e7307338e3dd 0x768ac1ce60e671c7

def z1119 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc16ffffc00000007 0xe182dffff8000000

def z1120 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xdffffffc7ffe0047 0xffbffffff8fffc00

def z1121 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x069118fc7ce71ffe 0xfe0d2231f8f9ce3f

def z1122 : W := mkw 0x167cd6a800000078 0x002cf9ad50000000 0xc77ffffc00000007 0xf78efffff8000000

def z1123 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xfffffffffcfe0027 0xfffffffffff9fc00

def z1124 : W := mkw 0x560ab002b800d005 0x00ac1560057001a0 0xfc0ee003b001fc39 0x05f81dc0076003f8

def z1125 : W := mkw 0x5679fa3e7c2348dc 0xc4acf3f47cf84691 0x4671f83c7c260000 0x508ce3f078f84c00

def z1126 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe9ff8cffc01fc3b 0x9ffd3ff19ff803f8

def z1127 : W := mkw 0x20276ff4d56bffb1 0xfc404edfe9aad7ff 0xc00ffffc0001ff87 0x81801ffff80003ff

def z1128 : W := mkw 0x09fcd6a800000078 0x0013f9ad50000000 0xd9fffffc00000007 0xefb3fffff8000000

def z1129 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x029118fc4ce71fec 0x70052231f899ce3f

def z1130 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xdf7ffffc00000007 0xd5befffff8000000

def z1131 : W := mkw 0x1facd6a800000038 0x003f59ad50000000 0xdf8ffffc00000007 0xbfbf1ffff8000000

def z1132 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01ffff 0xbffc1ff007f803ff

def z1133 : W := mkw 0x002cd6a800000038 0x000059ad50000000 0xc40ffffc00000007 0x97881ffff8000000

def z1134 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe0ff803fc01fc23 0x99fc1ff007f803f8

def z1135 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfa0ef8038c00fc23 0x09f41df0071801f8

def z1136 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xd80ffffc00000007 0x81b01ffff8000000

def z1137 : W := mkw 0x0000085404620d80 0x44000010a808c41b 0x029018fc0cc61fa6 0x08052031f8198c3f

def z1138 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xff0ff803ff01fc7b 0xbffe1ff007fe03f8

def z1139 : W := mkw 0x0001085444630d80 0xc4000210a888c61b 0x03911ffc4ce71fef 0xfe07223ff899ce3f

def z1140 : W := mkw 0x0000085404620d80 0x44000010a808c41b 0x029018fc0ce71fee 0xea052031f819ce3f

def z1141 : W := mkw 0x1ffcd6aa2814007e 0x003ff9ad54502800 0xdffffffc7cfe006f 0xffbffffff8f9fc00

def z1142 : W := mkw 0x560bb812fc21d885 0xc0ac177025f843b1 0xfe0ff833fc01ffbf 0x9ffc1ff067f803ff

def z1143 : W := mkw 0x560ab802bc00d805 0x40ac1570057801b0 0xfe0ef803bc01fc3b 0x8ffc1df0077803f8

def z1144 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfc0ff803b001fc3b 0x8ff81ff0076003f8

def z1145 : W := mkw 0x560bb802fc01d805 0xc0ac177005f803b0 0xfe8ff8c3fc01fc3f 0xbffd1ff187f803f8

def z1146 : W := mkw 0x1ffcd6a800000078 0x003ff9ad50000000 0xddeffffc00000007 0xafbbdffff8000000

def z1147 : W := mkw 0x0021633051296290 0xa80042c660a252c5 0x45f1e73073ffe3dd 0xf68be3ce60e7ffc7

def z1148 : W := mkw 0x298605c183d4b723 0x30530c0b8307a96e 0xb98e07c383ffffff 0xaf731c0f8707ffff

def z1149 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffffbfde0037 0xffffffffff7fbc00

def z1150 : W := mkw 0x1ffcd6a90294007a 0x003ff9ad52052800 0xdffffffc4ffe006f 0xffbffffff89ffc00

def z1151 : W := mkw 0x1ffcd6ab2a94007e 0x003ff9ad56552800 0xffffffff8ffe0067 0xffffffffff1ffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z8,z9]),(0,[z1,z2,z3,z4,z5,z10,z6]),(0,[z1,z2,z3,z11,z4,z5,z6])],[(0,[z12,z1,z2,z3,z4,z13,z6]),(0,[z1,z2,z3,z14,z4,z5,z6])],[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z16,z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z6]),(0,[z1,z20,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z2,z22,z3,z5,z23,z6])],[(0,[z1,z24,z2,z3,z4,z5,z6]),(0,[z25,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z26,z3,z27,z5,z6]),(0,[z28,z1,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z30]),(0,[z1,z31,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z1,z33,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z35,z6]),(0,[z1,z2,z3,z4,z36,z5,z6])],[(0,[z1,z2,z26,z3,z37,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z39,z3,z4,z5,z6])],[(1,[z1,z2,z3,z40,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z8]),(0,[z1,z2,z42,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z32,z6]),(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z45,z3,z4,z5,z46])],[(0,[z1,z2,z47,z48,z3,z5,z6]),(0,[z2,z3,z4,z49,z5,z50,z6])],[(0,[z28,z1,z2,z3,z4,z51,z6]),(0,[z1,z2,z3,z4,z5,z41,z9]),(0,[z1,z2,z3,z4,z5,z41,z52]),(0,[z1,z2,z3,z34,z32,z5,z6]),(0,[z1,z2,z3,z34,z5,z35,z6]),(0,[z1,z2,z3,z4,z5,z53,z6]),(0,[z1,z2,z54,z3,z4,z55,z6]),(0,[z1,z2,z56,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z6]),(0,[z1,z2,z59,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z5,z6,z61]),(0,[z1,z3,z4,z32,z5,z44,z6]),(0,[z62,z1,z2,z26,z3,z5,z6]),(1,[z1,z2,z3,z63,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z65,z3,z4,z5,z6])],[(1,[z66,z67,z3,z4,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z69,z3,z5,z6])],[(1,[z70,z2,z48,z4,z5,z6]),(1,[z71,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z72,z5,z6]),(0,[z1,z73,z2,z3,z4,z5,z6]),(1,[z1,z2,z74,z3,z46,z6]),(0,[z1,z2,z75,z3,z76,z5,z6]),(0,[z1,z2,z3,z4,z77,z5,z6]),(0,[z1,z2,z78,z3,z4,z5,z6])],[(0,[z25,z2,z3,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z1,z2,z3,z4,z76,z50,z6]),(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z81,z6])],[(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z1,z2,z3,z34,z37,z5,z6]),(0,[z1,z82,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z84]),(0,[z1,z2,z85,z3,z4,z5,z6]),(0,[z1,z86,z2,z3,z4,z5,z6]),(0,[z1,z87,z2,z3,z4,z5,z6])],[(0,[z1,z2,z88,z3,z4,z5,z6]),(1,[z1,z89,z2,z3,z4,z90])],[(0,[z1,z2,z3,z4,z49,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6]),(0,[z43,z1,z89,z2,z3,z4,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z56,z3,z34,z5,z6]),(0,[z1,z2,z4,z93,z5,z94,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z95]),(0,[z16,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z6,z96]),(0,[z1,z97,z98,z3,z4,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z1,z3,z4,z5,z101,z6,z8]),(0,[z1,z2,z102,z3,z4,z5,z6]),(0,[z1,z2,z74,z103,z4,z5,z6]),(0,[z1,z2,z3,z4,z104,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z67,z3,z4,z5,z6]),(0,[z1,z2,z106,z3,z4,z5,z6]),(0,[z1,z2,z107,z3,z4,z5,z6]),(0,[z1,z98,z2,z3,z4,z5,z101])],[(0,[z1,z108,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z109,z6]),(1,[z110,z1,z2,z26,z5,z6]),(0,[z1,z111,z2,z26,z3,z5,z6]),(0,[z1,z2,z74,z3,z5,z46,z6]),(0,[z1,z2,z56,z3,z4,z112,z5]),(0,[z1,z2,z3,z4,z5,z113,z6])],[(0,[z1,z2,z114,z3,z4,z5,z6]),(1,[z115,z2,z3,z116,z5,z6]),(0,[z1,z2,z26,z3,z93,z5,z6]),(1,[z1,z2,z3,z117,z5,z6]),(0,[z1,z2,z118,z3,z4,z5,z6])],[(0,[z1,z2,z119,z3,z4,z5,z6])],[(0,[z1,z120,z2,z4,z34,z5,z6]),(0,[z1,z97,z3,z4,z5,z6,z8]),(0,[z121,z1,z2,z3,z4,z5,z6])],[(0,[z12,z1,z2,z3,z122,z5,z6]),(0,[z123,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z124,z6]),(0,[z1,z2,z26,z3,z5,z125,z6]),(0,[z126,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z56,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z1,z127,z3,z4,z128,z5,z6]),(1,[z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z26,z48,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z6,z8]),(0,[z1,z2,z3,z4,z93,z5,z6]),(1,[z1,z2,z3,z4,z55,z6]),(0,[z1,z2,z3,z4,z5,z6,z130])],[(0,[z1,z2,z67,z3,z34,z5,z6]),(0,[z1,z2,z26,z3,z131,z5,z6]),(0,[z1,z2,z107,z3,z34,z5,z6])],[(0,[z2,z67,z3,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z132,z6]),(0,[z1,z2,z26,z3,z5,z6,z9]),(0,[z1,z2,z26,z3,z5,z6,z52]),(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z90])],[(0,[z134,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(1,[z1,z2,z3,z138,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z139]),(0,[z1,z2,z3,z4,z5,z125,z6])],[(0,[z1,z127,z2,z26,z3,z5,z6]),(0,[z1,z140,z2,z3,z4,z5,z6])],[(0,[z1,z2,z141,z3,z4,z5,z6]),(0,[z142,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z143,z4,z34,z5,z6]),(0,[z1,z2,z144,z4,z34,z5,z6]),(0,[z1,z145,z2,z3,z4,z5,z6])],[(0,[z146,z1,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z1,z148,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z149,z6]),(1,[z1,z2,z45,z3,z4,z5])]],
   [[(1,[z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z3,z4,z5,z151,z6]),(0,[z1,z2,z3,z34,z5,z125,z6])],[(0,[z152,z1,z2,z3,z4,z5,z6]),(0,[z12,z2,z3,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z153]),(0,[z1,z2,z3,z154,z4,z5,z6]),(0,[z1,z89,z155,z2,z3,z4,z6]),(0,[z1,z2,z156,z4,z5,z6,z9])],[(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z157,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z8]),(0,[z1,z2,z158,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z159,z6]),(0,[z1,z2,z160,z3,z4,z5,z6])],[(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z48,z4,z5,z6]),(0,[z1,z162,z2,z3,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z50,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z165])],[(0,[z166,z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z9]),(0,[z1,z2,z3,z34,z5,z6,z52]),(0,[z1,z2,z26,z54,z3,z5,z6]),(0,[z168,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z169,z5,z6]),(0,[z1,z2,z3,z4,z170,z5,z6]),(1,[z1,z2,z27,z34,z5,z6]),(0,[z1,z171,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z172,z6]),(0,[z1,z2,z173,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z174,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z175])],[(0,[z43,z1,z127,z3,z4,z5,z6]),(0,[z1,z98,z127,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z176]),(0,[z1,z2,z3,z4,z112,z5,z177]),(0,[z178,z1,z2,z3,z4,z5,z6]),(0,[z179,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z180,z6]),(0,[z1,z2,z3,z4,z5,z181,z6])],[(0,[z1,z182,z2,z3,z4,z5,z6]),(0,[z1,z2,z183,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z184]),(0,[z1,z148,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z2,z3,z186,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z25,z2,z3,z4,z5,z6,z41]),(0,[z1,z2,z3,z4,z5,z188,z6]),(0,[z1,z2,z3,z4,z5,z6,z189]),(0,[z1,z2,z3,z4,z5,z190,z6]),(0,[z1,z2,z143,z3,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z191])],[(0,[z1,z192,z2,z26,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z193]),(1,[z1,z120,z107,z4,z5,z6]),(0,[z1,z2,z26,z3,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z46,z6]),(0,[z1,z2,z3,z4,z112,z5,z125])],[(0,[z1,z2,z3,z4,z5,z194,z6]),(0,[z161,z1,z2,z3,z34,z5,z6])],[(0,[z66,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z195]),(0,[z1,z2,z3,z4,z5,z196,z6])],[(0,[z1,z98,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z34,z5,z23,z6]),(0,[z1,z2,z3,z4,z112,z5,z9]),(0,[z1,z2,z75,z3,z4,z76,z6])],[(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z197,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z54,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z200]),(0,[z1,z2,z201,z3,z4,z5,z6])],[(0,[z1,z2,z3,z202,z4,z5,z6]),(0,[z203,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z204,z4,z5,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(0,[z1,z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z1,z2,z3,z4,z5,z46,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z207,z6]),(0,[z1,z2,z143,z3,z34,z5,z6]),(0,[z1,z2,z144,z3,z34,z5,z6]),(0,[z1,z89,z2,z26,z3,z5,z6])],[(0,[z1,z208,z2,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z112,z125,z6])],[(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z209,z2,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z5,z6,z41]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z1,z211,z2,z3,z4,z6,z8]),(0,[z1,z2,z26,z3,z5,z94,z6]),(0,[z1,z212,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z213,z6]),(0,[z1,z89,z2,z22,z3,z4,z5])],[(1,[z1,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z215,z6]),(0,[z1,z2,z3,z4,z216,z5,z6]),(0,[z1,z2,z3,z34,z5,z46,z6]),(0,[z1,z2,z144,z3,z4,z5,z165]),(0,[z1,z217,z2,z3,z4,z5,z6])],[(0,[z16,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z218]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z219,z1,z2,z3,z4,z5,z6])],[(0,[z1,z120,z67,z3,z4,z5,z6]),(0,[z1,z2,z220,z3,z4,z5,z6]),(0,[z163,z2,z3,z4,z5,z50,z6]),(0,[z1,z2,z3,z4,z5,z6,z221]),(0,[z1,z2,z3,z4,z222,z5,z6]),(0,[z1,z2,z223,z3,z4,z93,z6])],[(0,[z1,z2,z3,z224,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z225]),(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z227,z6]),(0,[z166,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z228,z107,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z1,z83,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z34,z5,z101,z6])],[(0,[z2,z67,z3,z4,z5,z6,z41]),(0,[z1,z2,z230,z3,z4,z5,z6]),(1,[z1,z231,z3,z4,z5,z6]),(0,[z1,z82,z2,z3,z34,z5,z6]),(1,[z232,z2,z3,z4,z5,z6]),(1,[z1,z2,z156,z4,z5,z9]),(0,[z1,z2,z3,z4,z112,z5,z233]),(0,[z1,z2,z3,z4,z5,z6,z234])]],
   [[(0,[z1,z127,z3,z131,z4,z5,z6]),(1,[z1,z2,z3,z122,z5,z6]),(0,[z1,z2,z235,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z5,z6]),(0,[z1,z2,z74,z3,z4,z5,z6]),(0,[z1,z236,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z237,z6]),(0,[z1,z2,z3,z238,z4,z5,z6]),(1,[z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z94,z125,z6]),(1,[z1,z2,z144,z4,z93,z6])],[(0,[z1,z2,z3,z239,z4,z5,z6]),(1,[z240,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z241,z5,z6])],[(0,[z1,z127,z120,z3,z4,z5,z6]),(0,[z1,z2,z242,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z41]),(0,[z1,z2,z3,z34,z5,z94,z6]),(1,[z1,z2,z243,z4,z5,z6]),(0,[z1,z244,z2,z3,z4,z5,z6])],[(0,[z16,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z93,z32,z6]),(0,[z110,z1,z2,z3,z34,z5,z6])],[(0,[z1,z2,z3,z245,z4,z5,z6]),(0,[z28,z1,z246,z3,z4,z5,z6]),(0,[z1,z2,z3,z116,z4,z5,z6]),(0,[z1,z2,z247,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z177,z6,z41]),(0,[z248,z1,z2,z3,z4,z5,z6]),(0,[z249,z1,z2,z3,z4,z5,z6])],[(0,[z115,z1,z2,z3,z37,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z250]),(0,[z16,z1,z251,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z252,z5,z6]),(0,[z1,z2,z3,z34,z253,z5,z6])]],
   [[(0,[z163,z147,z2,z3,z4,z5,z6]),(0,[z1,z83,z2,z3,z254,z5,z6]),(0,[z1,z97,z2,z3,z34,z5,z6]),(0,[z1,z2,z74,z3,z34,z5,z6]),(0,[z1,z255,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z1,z82,z2,z3,z254,z5,z6]),(0,[z1,z2,z256,z3,z4,z5,z6]),(0,[z257,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z258,z6])],[(1,[z1,z2,z3,z252,z5,z6]),(0,[z259,z1,z2,z3,z4,z5,z6]),(0,[z260,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z261,z5,z6]),(0,[z262,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z26,z3,z5,z44,z6])],[(0,[z1,z82,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6]),(0,[z1,z2,z3,z4,z112,z5,z41]),(0,[z1,z2,z264,z3,z4,z5,z6]),(0,[z1,z2,z3,z265,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z112,z5])],[(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z267,z5,z6]),(0,[z1,z2,z3,z116,z34,z5,z6]),(0,[z1,z155,z2,z3,z4,z32,z6]),(0,[z1,z2,z26,z4,z34,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z268]),(0,[z1,z2,z3,z4,z5,z6,z269]),(0,[z1,z82,z3,z254,z4,z5,z6]),(1,[z1,z211,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z270,z6]),(1,[z1,z2,z14,z4,z5,z6])],[(0,[z25,z1,z67,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z271,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z272,z6]),(0,[z1,z2,z3,z4,z5,z6,z273])]],
   [[(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z50,z6]),(0,[z1,z2,z3,z5,z23,z6,z52])],[(0,[z1,z2,z3,z276,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z277,z6])],[(0,[z1,z2,z3,z4,z5,z278,z6]),(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z1,z2,z3,z4,z5,z6,z280]),(0,[z1,z2,z3,z4,z5,z281,z6]),(0,[z1,z2,z3,z4,z125,z6,z90])],[(0,[z1,z282,z2,z3,z4,z5,z6]),(0,[z43,z1,z155,z3,z4,z5,z6]),(1,[z43,z1,z3,z4,z44,z6]),(0,[z1,z2,z283,z3,z4,z5,z6])],[(0,[z1,z2,z3,z34,z5,z44,z6]),(0,[z1,z2,z284,z3,z4,z5,z6]),(0,[z1,z2,z285,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z286,z6])],[(0,[z1,z2,z26,z3,z49,z5,z6]),(0,[z1,z2,z3,z287,z4,z5,z6]),(0,[z71,z1,z2,z254,z4,z5,z6])],[(0,[z147,z1,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z4,z50,z46,z6]),(0,[z1,z2,z3,z4,z288,z5,z6]),(0,[z1,z2,z144,z3,z117,z5,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z3,z4,z5,z6,z90])],[(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z291,z6]),(0,[z28,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z26,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z293,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z294,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z1,z296,z2,z3,z4,z5,z6])],[(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z298,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z238,z5,z6]),(0,[z166,z1,z3,z131,z4,z5,z6]),(0,[z110,z1,z120,z2,z4,z5,z6]),(0,[z1,z2,z3,z276,z34,z5,z6])],[(0,[z1,z2,z3,z4,z5,z299,z6]),(0,[z1,z300,z2,z3,z4,z5,z6]),(0,[z1,z301,z2,z3,z4,z5,z6]),(1,[z302,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z2,z283,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z304]),(0,[z1,z2,z305,z3,z4,z5,z6])],[(0,[z1,z2,z3,z306,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z307,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z166,z1,z120,z3,z4,z5,z6]),(1,[z1,z2,z3,z238,z5,z6]),(1,[z1,z2,z228,z3,z5,z6]),(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z310,z5,z6]),(0,[z1,z2,z156,z3,z311,z5,z6]),(0,[z1,z2,z3,z4,z5,z312,z6])],[(1,[z1,z2,z3,z311,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6])],[(0,[z28,z1,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z4,z50,z94,z6]),(0,[z1,z2,z3,z34,z49,z5,z6]),(0,[z1,z314,z2,z3,z4,z5,z6]),(0,[z1,z2,z315,z3,z4,z5,z6]),(0,[z1,z316,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z317,z4,z5,z6]),(0,[z1,z2,z3,z254,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z318])]],
   [[(0,[z1,z2,z4,z34,z5,z6,z9])],[(0,[z66,z1,z2,z3,z4,z5,z278]),(1,[z1,z319,z3,z4,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z321]),(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z3,z4,z5,z6,z323])],[(0,[z70,z2,z67,z3,z4,z5,z6]),(0,[z70,z1,z2,z26,z3,z5,z6]),(0,[z115,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z325,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z56,z3,z5,z52])],[(0,[z1,z2,z326,z3,z4,z5,z6]),(0,[z1,z327,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z328,z5,z6]),(0,[z1,z2,z45,z3,z4,z5,z6])],[(0,[z1,z67,z3,z131,z4,z5,z6]),(0,[z1,z2,z329,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z321]),(0,[z330,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z331,z6]),(0,[z1,z2,z3,z4,z34,z5,z6]),(0,[z1,z2,z332,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z333])],[(0,[z1,z2,z26,z3,z5,z149,z6])],[(0,[z28,z115,z2,z3,z4,z5,z6]),(0,[z1,z2,z223,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z4,z5,z9]),(0,[z1,z2,z75,z3,z4,z46,z6]),(0,[z1,z89,z2,z56,z3,z4,z5])],[(0,[z1,z2,z334,z3,z4,z5,z6]),(0,[z166,z110,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z254,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z335,z6])]],
   [[(0,[z336,z1,z2,z3,z4,z5,z6]),(1,[z1,z337,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z338]),(0,[z1,z89,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z218,z6]),(0,[z1,z2,z3,z4,z339,z5,z6]),(0,[z1,z2,z3,z34,z93,z5,z6]),(0,[z340,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z54,z156,z4,z5,z6]),(0,[z1,z2,z341,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z342]),(0,[z1,z83,z2,z3,z128,z5,z6]),(0,[z1,z2,z343,z3,z4,z5,z6]),(0,[z1,z2,z344,z3,z4,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z23])],[(0,[z345,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z1,z2,z347,z3,z4,z5,z6]),(0,[z1,z2,z348,z3,z4,z5,z6]),(0,[z1,z82,z2,z3,z128,z5,z6]),(0,[z1,z2,z349,z3,z4,z5,z6])],[(0,[z1,z120,z2,z3,z4,z5,z6]),(0,[z1,z2,z350,z3,z4,z5,z6]),(0,[z1,z2,z351,z3,z4,z5,z6]),(0,[z1,z2,z118,z144,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z352])],[(0,[z1,z89,z2,z3,z4,z5,z125]),(0,[z353,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z13,z6]),(0,[z1,z354,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z355,z5,z6]),(0,[z356,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z357,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z278]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z358,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z3,z4,z359,z5,z6]),(0,[z1,z2,z3,z4,z5,z360,z6]),(0,[z1,z2,z223,z3,z34,z5,z6]),(0,[z1,z361,z2,z26,z3,z5,z6])],[(1,[z1,z2,z29,z4,z5,z6]),(0,[z362,z1,z2,z3,z4,z5,z6]),(0,[z363,z1,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z9]),(0,[z1,z2,z364,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z365,z6]),(0,[z1,z97,z2,z3,z4,z5,z101]),(0,[z1,z2,z54,z3,z4,z159,z6]),(0,[z1,z2,z54,z3,z4,z5,z233]),(0,[z1,z2,z3,z4,z112,z5,z6])],[(0,[z1,z2,z3,z4,z5,z366,z6]),(0,[z1,z2,z3,z4,z5,z6,z367]),(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z1,z337,z2,z3,z4,z5,z6]),(1,[z1,z2,z34,z5,z6,z9]),(0,[z369,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z370]),(1,[z163,z2,z3,z4,z50,z6]),(1,[z167,z2,z3,z4,z5,z6]),(1,[z1,z2,z144,z34,z5,z6])],[(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z6]),(1,[z1,z2,z3,z4,z51,z6]),(0,[z1,z120,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z372,z5,z6])],[(0,[z373,z1,z2,z3,z4,z5,z6]),(0,[z1,z374,z2,z3,z4,z5,z6]),(1,[z1,z2,z186,z4,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z6])],[(0,[z1,z127,z3,z4,z5,z6,z8]),(0,[z376,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z27,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z377,z6]),(1,[z1,z2,z3,z4,z5,z124]),(0,[z240,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z177]),(0,[z1,z155,z2,z26,z3,z5,z6]),(0,[z1,z97,z89,z2,z3,z4,z5])],[(0,[z1,z2,z3,z3,z34,z5,z6]),(0,[z1,z378,z2,z26,z3,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6])],[(0,[z66,z2,z67,z3,z4,z5,z6]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z382,z5,z6]),(0,[z1,z2,z3,z4,z5,z383,z6]),(0,[z1,z2,z384,z3,z4,z5,z6]),(0,[z1,z2,z4,z34,z5,z94,z6]),(0,[z1,z2,z156,z3,z4,z5,z9]),(0,[z1,z2,z3,z4,z5,z385,z6])]],
   [[(0,[z43,z1,z2,z26,z3,z5,z6]),(0,[z1,z98,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z386,z6]),(0,[z1,z2,z387,z3,z4,z5,z6]),(0,[z1,z2,z102,z156,z3,z5,z6])],[(0,[z240,z25,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z388]),(0,[z1,z2,z3,z4,z389,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z233]),(1,[z1,z2,z3,z4,z112,z125])],[(0,[z1,z2,z3,z4,z5,z233,z8])],[(0,[z1,z2,z3,z4,z390,z5,z6]),(0,[z1,z82,z127,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z2,z26,z3,z222,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z392])],[(0,[z1,z2,z3,z4,z393,z5,z6])],[(0,[z240,z2,z3,z4,z5,z177,z6]),(0,[z1,z83,z3,z4,z128,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6])],[(0,[z1,z67,z3,z4,z32,z5,z6]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z25,z1,z127,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z396]),(0,[z1,z2,z3,z397,z4,z5,z6]),(1,[z1,z97,z3,z4,z5,z8]),(0,[z1,z2,z3,z34,z5,z206,z6])],[(0,[z1,z2,z3,z4,z398,z5,z6]),(0,[z1,z2,z26,z223,z3,z5,z6]),(0,[z1,z2,z3,z76,z5,z46,z6])]],
   [[(0,[z1,z2,z399,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z400,z6]),(0,[z1,z120,z107,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z5,z52])],[(0,[z12,z1,z2,z48,z4,z5,z6]),(0,[z1,z2,z401,z3,z4,z5,z6]),(1,[z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z402]),(1,[z1,z2,z3,z4,z5,z396]),(0,[z1,z89,z2,z3,z4,z93,z6]),(0,[z1,z2,z156,z3,z4,z5,z233])],[(0,[z403,z1,z2,z3,z4,z5,z6]),(1,[z1,z155,z3,z4,z32,z6]),(1,[z1,z2,z3,z4,z159,z6])],[(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z405,z1,z2,z3,z4,z5,z6]),(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z107,z4,z5,z6]),(0,[z1,z2,z406,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z407,z6])],[(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z112,z5])],[(0,[z25,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z409,z6]),(0,[z1,z2,z26,z3,z5,z50,z6])],[(0,[z1,z2,z3,z4,z5,z410,z6]),(0,[z1,z89,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z411,z46])],[(0,[z1,z2,z47,z3,z4,z5,z6]),(0,[z1,z2,z412,z26,z3,z5,z6]),(0,[z1,z2,z413,z3,z4,z5,z6])]],
   [[(0,[z414,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z34,z5,z94,z6]),(1,[z1,z2,z22,z3,z5,z23])],[(1,[z25,z127,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z415]),(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z417,z6]),(0,[z1,z2,z3,z4,z418,z5,z6])],[(0,[z419,z1,z2,z3,z4,z5,z6]),(0,[z163,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z50,z6]),(0,[z1,z2,z26,z3,z128,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z75,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z421,z5,z6]),(0,[z1,z2,z422,z3,z4,z5,z6]),(0,[z1,z2,z107,z3,z138,z5,z6]),(0,[z1,z2,z3,z4,z423,z5,z6]),(0,[z1,z2,z424,z3,z4,z5,z6])],[(1,[z1,z2,z103,z4,z5,z6])],[(0,[z1,z111,z2,z3,z4,z5,z6]),(0,[z1,z425,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z426])],[(0,[z1,z2,z3,z4,z5,z150,z6]),(0,[z1,z2,z427,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z428,z6]),(0,[z1,z89,z2,z3,z4,z94,z6]),(0,[z1,z2,z429,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z430,z6])],[(0,[z1,z2,z3,z4,z51,z5,z6]),(0,[z1,z2,z3,z431,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z432,z6]),(0,[z1,z433,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z128,z5,z6])]],
   [[],[(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z231,z3,z4,z5,z6]),(0,[z1,z251,z2,z3,z4,z5,z6]),(0,[z1,z434,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z435,z6])],[(0,[z166,z295,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z432,z6]),(0,[z1,z2,z3,z436,z4,z5,z6]),(0,[z1,z2,z75,z3,z34,z5,z6]),(0,[z1,z2,z437,z26,z3,z5,z6])],[(0,[z438,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z41]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z2,z439,z3,z4,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z441])],[(0,[z28,z1,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z442,z5,z6]),(0,[z1,z443,z2,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z5,z6,z90]),(0,[z1,z2,z444,z3,z4,z5,z6])],[(0,[z2,z48,z3,z27,z4,z5,z6]),(1,[z295,z2,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z446,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z447])],[(1,[z166,z1,z2,z34,z5,z6]),(0,[z1,z2,z448,z3,z4,z5,z6]),(0,[z449,z1,z2,z3,z4,z5,z6])],[(0,[z1,z127,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z54,z4,z34,z5,z6])]],
   [[(0,[z127,z2,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z450,z4,z5,z6]),(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z452])],[(0,[z1,z67,z3,z4,z5,z6,z8]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z147,z1,z337,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z454,z5,z6]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z155,z2,z3,z4,z44,z6]),(0,[z456,z1,z2,z3,z4,z5,z6])],[(0,[z12,z1,z2,z3,z34,z5,z6])],[(1,[z1,z2,z401,z4,z5,z6]),(0,[z1,z2,z457,z3,z4,z5,z6]),(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z459,z3,z4,z5,z6]),(0,[z1,z2,z3,z460,z4,z5,z6])],[(1,[z1,z2,z47,z3,z5,z6]),(0,[z43,z1,z2,z3,z4,z44,z6]),(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z462])],[(0,[z1,z127,z3,z4,z32,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z463]),(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z2,z465,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z90])],[(0,[z1,z466,z2,z3,z4,z5,z6])],[(0,[z1,z127,z2,z3,z34,z5,z6]),(0,[z1,z2,z48,z3,z267,z5,z6]),(0,[z467,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z468,z4,z5,z6]),(1,[z166,z1,z131,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z469,z6]),(0,[z470,z1,z2,z3,z4,z5,z6]),(0,[z1,z89,z98,z2,z3,z4,z5]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z472,z6]),(0,[z1,z2,z473,z3,z4,z5,z6]),(0,[z1,z2,z144,z4,z93,z5,z6])],[(0,[z474,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z475,z6]),(0,[z1,z2,z476,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z477]),(0,[z478,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z223,z4,z94,z6]),(0,[z1,z2,z54,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z177,z8]),(0,[z1,z2,z479,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z34,z5,z6])],[(0,[z1,z192,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z267,z5,z6]),(0,[z1,z2,z48,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z177,z9]),(0,[z1,z2,z3,z4,z5,z177,z52]),(0,[z1,z2,z3,z480,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z481,z6])],[(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z240,z1,z2,z3,z4,z5,z177]),(0,[z482,z1,z2,z3,z4,z5,z6])],[(0,[z66,z1,z2,z3,z4,z5,z6]),(0,[z483,z1,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z124]),(0,[z1,z484,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z4,z34,z5,z6]),(0,[z1,z2,z26,z144,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z485,z6]),(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z486,z3,z4,z5,z6]),(0,[z1,z2,z487,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z67,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z1,z2,z3,z489,z4,z5,z6])],[(0,[z12,z1,z2,z3,z40,z5,z6]),(0,[z1,z2,z26,z3,z116,z5,z6]),(0,[z1,z2,z3,z4,z76,z49,z6]),(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z1,z2,z3,z491,z4,z5,z6]),(0,[z1,z2,z54,z3,z34,z5,z6]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6])],[(0,[z1,z2,z3,z493,z4,z5,z6]),(0,[z1,z2,z494,z3,z4,z5,z6]),(0,[z1,z2,z495,z3,z4,z5,z6]),(0,[z1,z2,z56,z14,z4,z5,z6]),(0,[z1,z496,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6])],[(0,[z25,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z225]),(0,[z1,z120,z2,z131,z4,z5,z6]),(0,[z1,z2,z3,z34,z34,z5,z6]),(0,[z497,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z118,z3,z5,z6]),(0,[z1,z2,z498,z3,z4,z5,z6])],[(0,[z1,z2,z499,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z177]),(0,[z1,z2,z26,z3,z254,z5,z6]),(0,[z1,z2,z3,z4,z32,z94,z6]),(0,[z1,z2,z3,z4,z5,z500,z6]),(0,[z1,z2,z3,z4,z5,z501,z6]),(0,[z1,z2,z26,z487,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z270]),(0,[z502,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z1,z98,z2,z3,z4,z5,z8])],[(0,[z66,z1,z2,z3,z34,z5,z6]),(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z110,z1,z2,z27,z4,z5,z6]),(0,[z1,z2,z3,z131,z4,z5,z6]),(0,[z1,z2,z26,z3,z112,z5,z6]),(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z112,z6])],[(0,[z1,z2,z505,z3,z4,z5,z6]),(0,[z1,z208,z2,z3,z4,z5,z6])]],
   [[(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z155,z2,z3,z4,z125,z6]),(0,[z1,z2,z3,z4,z5,z6,z506]),(0,[z110,z1,z2,z144,z4,z5,z6])],[(0,[z1,z2,z3,z4,z507,z5,z6]),(0,[z1,z2,z3,z4,z508,z5,z6]),(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z510,z3,z4,z5,z6]),(0,[z1,z2,z511,z3,z4,z5,z6]),(1,[z1,z2,z26,z34,z5,z6]),(0,[z1,z2,z243,z56,z4,z5,z6])],[(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z513,z6]),(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z156,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z514,z3,z4,z5,z6]),(0,[z147,z1,z231,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z125,z6]),(0,[z110,z1,z2,z4,z5,z6,z9]),(0,[z1,z2,z26,z515,z3,z5,z6])],[(0,[z516,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z95]),(1,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z254,z397,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z5,z6])],[(0,[z1,z517,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z101,z177]),(0,[z1,z2,z3,z4,z518,z5,z6]),(0,[z1,z2,z3,z4,z5,z519,z6]),(0,[z1,z2,z520,z3,z4,z5,z6])],[(0,[z1,z2,z48,z3,z34,z5,z6]),(0,[z1,z2,z3,z521,z4,z5,z6]),(0,[z1,z2,z3,z131,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z2,z3,z523,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z524])],[(0,[z1,z2,z3,z4,z525,z5,z6]),(1,[z1,z2,z143,z34,z5,z6]),(0,[z1,z2,z3,z34,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z1,z2,z3,z526,z4,z5,z6])]],
   [[(0,[z240,z2,z67,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z527,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z271,z5,z6]),(0,[z1,z2,z3,z4,z528,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z530,z3,z4,z5,z6])],[(0,[z1,z2,z531,z3,z4,z5,z6]),(0,[z1,z2,z156,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z532,z5,z6]),(0,[z1,z2,z3,z4,z63,z5,z6])],[(0,[z66,z1,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z1,z2,z3,z534,z4,z5,z6]),(0,[z1,z2,z3,z4,z535,z5,z6]),(1,[z1,z98,z3,z4,z5,z101]),(1,[z1,z2,z3,z34,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z5,z6])],[(0,[z1,z537,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z101,z9]),(0,[z1,z2,z3,z538,z4,z5,z6]),(0,[z1,z2,z3,z4,z539,z5,z6]),(1,[z1,z2,z3,z4,z5,z411]),(0,[z1,z2,z3,z4,z540,z5,z6])],[(0,[z12,z1,z129,z3,z4,z5,z6]),(0,[z1,z2,z541,z3,z4,z5,z6]),(0,[z1,z2,z520,z3,z34,z5,z6]),(0,[z1,z2,z542,z3,z4,z5,z6])],[(1,[z1,z251,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z165])],[(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z545,z5,z6]),(0,[z1,z3,z254,z4,z128,z5,z6])]],
   [[(0,[z12,z70,z2,z3,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z49,z6]),(0,[z1,z2,z546,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z547,z5,z6])],[(0,[z548,z1,z2,z3,z4,z5,z6]),(0,[z549,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z27,z4,z5,z6]),(0,[z28,z1,z2,z3,z37,z5,z6]),(0,[z1,z550,z2,z3,z4,z5,z6]),(0,[z1,z2,z530,z3,z34,z5,z6]),(0,[z1,z2,z3,z551,z4,z5,z6])],[(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z26,z107,z3,z5,z6]),(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z554,z4,z5,z6])],[(0,[z70,z1,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z555,z5,z6]),(0,[z240,z1,z2,z3,z4,z5,z41]),(1,[z1,z2,z397,z4,z5,z6]),(0,[z1,z2,z22,z3,z34,z5,z6])],[(0,[z28,z1,z2,z3,z4,z5,z150]),(1,[z1,z83,z3,z128,z5,z6]),(0,[z1,z83,z2,z26,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z556,z6]),(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z82,z2,z26,z3,z5,z6]),(0,[z1,z2,z223,z69,z3,z5,z6]),(0,[z1,z2,z3,z4,z117,z5,z6])],[(0,[z1,z2,z3,z4,z5,z557,z6]),(0,[z1,z558,z2,z3,z4,z5,z6])],[(0,[z25,z66,z2,z3,z4,z5,z6]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z560,z6])]],
   [[(0,[z1,z2,z3,z561,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z562]),(0,[z1,z2,z3,z4,z5,z6,z563]),(0,[z1,z2,z3,z4,z564,z5,z6]),(0,[z1,z2,z4,z5,z233,z6,z9])],[(0,[z1,z2,z3,z4,z565,z5,z6]),(1,[z1,z2,z102,z3,z5,z6])],[(0,[z16,z1,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z41]),(0,[z110,z1,z2,z26,z3,z5,z6]),(0,[z110,z1,z2,z4,z5,z94,z6]),(0,[z566,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z567,z3,z4,z5,z6]),(0,[z1,z568,z2,z3,z4,z5,z6])],[(0,[z25,z127,z2,z3,z4,z5,z6]),(0,[z1,z107,z3,z131,z4,z5,z6]),(0,[z1,z2,z569,z3,z4,z5,z6])],[(0,[z1,z2,z3,z570,z4,z5,z6]),(0,[z1,z2,z3,z571,z4,z5,z6]),(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z573,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z574,z6])],[(0,[z1,z2,z3,z4,z138,z5,z6]),(0,[z1,z2,z3,z4,z575,z5,z6]),(0,[z1,z2,z3,z4,z44,z94,z6])],[(0,[z576,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z37,z5,z6]),(0,[z1,z97,z2,z26,z3,z5,z6])],[(0,[z1,z2,z577,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z578,z6]),(0,[z115,z2,z3,z116,z4,z5,z6]),(0,[z1,z2,z3,z4,z579,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580])],[(0,[z1,z2,z3,z581,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z50,z6]),(0,[z1,z2,z3,z4,z5,z6,z321]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z94,z6]),(0,[z1,z2,z3,z4,z5,z6,z584])],[(0,[z1,z2,z26,z22,z3,z5,z6]),(0,[z1,z2,z22,z3,z4,z5,z23])],[(1,[z12,z2,z27,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z101,z41]),(0,[z1,z2,z3,z4,z585,z5,z6]),(0,[z1,z2,z228,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z586]),(0,[z1,z2,z3,z4,z93,z44,z6])],[(0,[z66,z1,z2,z3,z4,z5,z268]),(0,[z1,z2,z3,z4,z5,z6,z587]),(0,[z1,z2,z3,z4,z5,z588,z6]),(0,[z115,z1,z2,z3,z4,z5,z6]),(0,[z28,z2,z3,z4,z37,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z590,z5,z6]),(0,[z1,z2,z3,z34,z5,z6,z426]),(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z1,z2,z56,z3,z4,z5,z52])],[(0,[z1,z592,z2,z3,z4,z5,z6]),(0,[z1,z593,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z338]),(0,[z1,z2,z3,z4,z5,z594,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z596])],[(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z1,z2,z332,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z128,z5,z6]),(0,[z597,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z6,z477,z8])]],
   [[(0,[z2,z3,z116,z4,z37,z5,z6]),(0,[z598,z1,z2,z3,z4,z5,z6]),(1,[z1,z120,z2,z34,z5,z6])],[(0,[z599,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z600,z3,z4,z5,z6]),(0,[z1,z2,z74,z3,z4,z46,z6])],[(0,[z340,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z601,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z5,z177,z6]),(0,[z1,z2,z223,z144,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z1,z2,z3,z4,z603,z5,z6])],[(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z2,z26,z74,z3,z5,z6]),(0,[z1,z2,z56,z3,z5,z6,z52])],[(0,[z70,z1,z2,z3,z34,z5,z6]),(0,[z115,z1,z2,z3,z34,z5,z6]),(0,[z147,z1,z2,z3,z4,z5,z338]),(0,[z1,z2,z3,z4,z5,z606,z6]),(0,[z1,z2,z3,z607,z4,z5,z6]),(0,[z1,z98,z3,z4,z5,z101,z6]),(0,[z1,z2,z3,z4,z5,z411,z6])],[(0,[z12,z1,z2,z26,z3,z5,z6]),(0,[z28,z1,z2,z26,z3,z5,z6]),(1,[z16,z2,z3,z4,z5,z41]),(0,[z1,z2,z69,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z1,z2,z3,z310,z34,z5,z6]),(0,[z1,z2,z26,z3,z5,z472,z6]),(0,[z1,z2,z74,z75,z3,z5,z6]),(0,[z1,z609,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z610,z5,z6]),(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z1,z2,z3,z4,z5,z6,z611])]],
   [[(0,[z1,z2,z3,z27,z4,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z26,z3,z76,z5,z6])],[(1,[z1,z2,z3,z4,z5,z268])],[(0,[z340,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z612,z5,z6]),(0,[z1,z2,z54,z133,z3,z5,z6]),(0,[z1,z2,z3,z613,z4,z5,z6])],[(0,[z1,z2,z3,z4,z614,z5,z6]),(0,[z115,z1,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z34,z5,z177,z6]),(0,[z1,z2,z3,z4,z5,z6,z8])],[(0,[z615,z1,z2,z3,z4,z5,z6])],[(0,[z1,z616,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z1,z2,z3,z4,z93,z49,z6]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z1,z2,z26,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z1,z2,z3,z4,z76,z5,z6]),(0,[z1,z2,z243,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52])],[(0,[z1,z2,z3,z4,z619,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z270])],[(0,[z1,z319,z2,z3,z4,z5,z6]),(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z240,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z396,z6]),(0,[z1,z2,z3,z4,z5,z621,z6]),(0,[z1,z155,z2,z3,z4,z5,z6]),(1,[z1,z208,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z233,z101]),(0,[z1,z2,z3,z4,z5,z6,z622])]],
   [[(0,[z1,z2,z3,z27,z34,z5,z6]),(0,[z1,z378,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z1,z2,z624,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z6,z90])],[(0,[z625,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z626,z5,z6]),(0,[z1,z2,z3,z4,z627,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z629,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z76,z5,z6]),(0,[z1,z2,z26,z3,z5,z23,z6]),(0,[z1,z2,z3,z4,z5,z6,z630]),(0,[z1,z2,z3,z4,z112,z5,z90])],[(0,[z66,z1,z127,z3,z4,z5,z6]),(1,[z28,z2,z3,z37,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z631,z3,z4,z5,z6]),(0,[z1,z98,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z125,z6]),(0,[z1,z2,z54,z4,z5,z233,z6]),(0,[z1,z2,z632,z3,z4,z5,z6]),(0,[z1,z2,z633,z3,z4,z5,z6])],[(0,[z12,z1,z2,z3,z4,z271,z6]),(0,[z147,z1,z2,z3,z4,z49,z6]),(0,[z1,z2,z26,z143,z3,z5,z6]),(0,[z1,z2,z74,z3,z4,z76,z6])],[(1,[z1,z246,z3,z4,z5,z6]),(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z636,z1,z2,z3,z4,z5,z6])],[(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z638,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z48,z34,z5,z6]),(0,[z1,z155,z3,z4,z32,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z639]),(0,[z1,z2,z3,z4,z5,z6,z640])],[(0,[z1,z2,z3,z4,z5,z23,z6])],[(0,[z1,z2,z641,z3,z4,z5,z6]),(0,[z16,z2,z3,z4,z5,z6,z41]),(0,[z240,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z642,z3,z4,z5,z6]),(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z155,z2,z3,z34,z5,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(0,[z110,z1,z2,z26,z4,z5,z6]),(0,[z1,z645,z2,z3,z4,z5,z6]),(0,[z1,z2,z646,z3,z4,z5,z6]),(0,[z1,z647,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z648,z2,z3,z4,z5,z6]),(0,[z1,z2,z649,z3,z4,z5,z6]),(0,[z166,z1,z2,z131,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z650,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z302,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z652,z6])],[(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z1,z2,z654,z3,z4,z5,z6]),(0,[z97,z302,z2,z3,z4,z5,z6]),(0,[z232,z97,z2,z3,z4,z5,z6])],[(0,[z240,z16,z2,z3,z4,z5,z6]),(0,[z1,z2,z655,z3,z4,z5,z6]),(0,[z43,z1,z3,z4,z5,z44,z6]),(0,[z43,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z44]),(0,[z1,z2,z26,z3,z5,z101,z6]),(0,[z1,z656,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z49,z46,z6]),(0,[z1,z2,z3,z4,z252,z5,z6])],[(0,[z1,z2,z657,z3,z4,z5,z6]),(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z28,z1,z2,z401,z4,z5,z6]),(0,[z1,z659,z2,z3,z4,z5,z6]),(0,[z1,z2,z223,z4,z5,z94,z6]),(1,[z1,z2,z133,z3,z5,z6])],[(0,[z147,z2,z3,z4,z49,z5,z6]),(0,[z1,z2,z660,z3,z4,z5,z6]),(0,[z110,z1,z2,z143,z4,z5,z6]),(0,[z1,z89,z2,z3,z34,z5,z6]),(0,[z1,z2,z26,z3,z5,z233,z6]),(0,[z1,z2,z515,z3,z4,z5,z6]),(0,[z1,z2,z26,z75,z3,z5,z6]),(0,[z1,z2,z661,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z662])],[(0,[z1,z2,z3,z4,z663,z5,z6]),(0,[z70,z2,z48,z3,z4,z5,z6]),(0,[z1,z98,z2,z3,z4,z112,z5])],[(0,[z1,z2,z3,z664,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z665,z6]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z667]),(0,[z1,z668,z2,z3,z4,z5,z6]),(0,[z1,z2,z669,z3,z4,z5,z6]),(0,[z1,z670,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z101,z6])]],
   [[(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z672]),(0,[z1,z2,z3,z4,z673,z5,z6]),(1,[z1,z2,z54,z34,z5,z6]),(0,[z674,z1,z2,z3,z4,z5,z6])],[(0,[z1,z120,z2,z26,z3,z5,z6]),(1,[z1,z2,z3,z4,z6,z477]),(0,[z1,z2,z26,z156,z3,z5,z6]),(0,[z1,z2,z412,z3,z4,z5,z6])],[(0,[z1,z2,z675,z3,z4,z5,z6]),(0,[z1,z2,z676,z3,z4,z5,z6]),(0,[z16,z1,z2,z3,z4,z5,z177]),(0,[z232,z1,z2,z3,z4,z5,z6])],[(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z678,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z246,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z49,z94,z6]),(0,[z1,z120,z2,z107,z4,z5,z6]),(0,[z1,z2,z3,z4,z446,z5,z6]),(0,[z1,z2,z679,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z680,z5,z6])],[(0,[z1,z2,z3,z4,z5,z681,z6]),(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z163,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z41]),(0,[z1,z2,z683,z3,z4,z5,z6]),(0,[z684,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z6])],[(0,[z685,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z686,z5,z6]),(0,[z12,z1,z319,z3,z4,z5,z6]),(0,[z1,z687,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z688,z4,z5,z6]),(0,[z1,z214,z2,z3,z4,z5,z6]),(0,[z1,z2,z689,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z233,z6]),(0,[z1,z2,z26,z56,z3,z5,z6])],[(0,[z43,z1,z67,z3,z4,z5,z6]),(0,[z1,z98,z67,z3,z4,z5,z6]),(0,[z1,z2,z54,z3,z63,z5,z6]),(0,[z690,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z691,z6])]],
   [[(0,[z1,z2,z692,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z674,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z2,z695,z3,z4,z5,z6])],[(0,[z1,z2,z3,z122,z4,z5,z6]),(0,[z1,z2,z74,z186,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z696,z6])],[(0,[z1,z67,z3,z4,z128,z5,z6]),(0,[z1,z374,z2,z26,z3,z5,z6])],[(0,[z70,z1,z2,z27,z4,z5,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z1,z2,z698,z3,z4,z5,z6]),(0,[z1,z97,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z261,z5,z6]),(0,[z1,z2,z3,z4,z699,z5,z6])],[(0,[z163,z1,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z700,z6]),(0,[z1,z2,z3,z4,z5,z6,z701]),(0,[z1,z2,z437,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z702,z6]),(0,[z703,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z342]),(1,[z1,z2,z3,z4,z475,z6]),(0,[z1,z2,z223,z3,z446,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z704])],[(1,[z147,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z705,z5,z6]),(0,[z1,z2,z26,z3,z32,z5,z6]),(0,[z1,z2,z3,z34,z545,z5,z6]),(0,[z1,z2,z26,z3,z5,z6,z563]),(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z706])],[(0,[z1,z2,z223,z3,z4,z94,z6]),(0,[z1,z2,z144,z3,z4,z93,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z29,z37,z5,z6])],[(0,[z1,z127,z3,z4,z5,z268]),(0,[z1,z2,z3,z4,z6,z707]),(0,[z1,z2,z144,z4,z708,z6])],[(0,[z1,z2,z3,z5,z709,z6]),(0,[z1,z2,z401,z4,z5,z225]),(0,[z1,z2,z3,z4,z5,z710])],[(0,[z1,z2,z29,z4,z5,z150]),(0,[z1,z89,z2,z3,z4,z139]),(0,[z1,z2,z3,z4,z5,z711]),(0,[z1,z98,z3,z4,z5,z435]),(0,[z1,z89,z2,z34,z94,z6]),(0,[z1,z2,z3,z117,z5,z165])],[(0,[z1,z2,z450,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z712])],[(0,[z576,z1,z2,z34,z5,z6]),(0,[z1,z2,z713,z3,z5,z6]),(0,[z714,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z34,z55,z6])],[(0,[z1,z208,z155,z2,z3,z4]),(0,[z1,z208,z2,z3,z4,z5])],[(0,[z1,z2,z715,z4,z5,z6]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z2,z3,z4,z51,z150]),(0,[z1,z2,z3,z717,z5,z6]),(0,[z302,z2,z26,z3,z5,z6]),(0,[z1,z2,z284,z34,z5,z6]),(0,[z1,z2,z26,z3,z5,z718]),(0,[z1,z719,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z34,z5,z268]),(0,[z1,z2,z156,z311,z5,z9])],[(0,[z67,z3,z4,z5,z41,z8]),(0,[z12,z2,z27,z40,z5,z6]),(0,[z1,z2,z3,z4,z720,z6]),(0,[z28,z2,z3,z37,z5,z6]),(0,[z1,z2,z26,z655,z5,z6])],[(0,[z1,z2,z3,z4,z721,z6]),(0,[z1,z2,z3,z4,z112,z279])],[(0,[z1,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z723,z5,z6])],[(0,[z1,z2,z34,z5,z177,z9]),(0,[z1,z2,z34,z5,z6,z323])],[(0,[z260,z67,z3,z4,z5,z6]),(0,[z1,z2,z74,z186,z46,z6])],[(0,[z1,z2,z724,z3,z5,z6]),(0,[z302,z98,z3,z4,z5,z6])],[(1,[z725,z3,z4,z5,z6]),(0,[z1,z2,z437,z34,z5,z6]),(0,[z2,z3,z4,z5,z726,z6]),(0,[z1,z2,z26,z3,z5,z727])]],
   [[(0,[z1,z2,z3,z4,z5,z728]),(0,[z1,z729,z2,z3,z4,z6]),(0,[z1,z155,z3,z4,z730,z6])],[(0,[z147,z2,z3,z4,z731,z6]),(0,[z1,z2,z26,z3,z5,z321]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z1,z217,z2,z34,z5,z6])],[(0,[z1,z2,z3,z4,z733,z6])],[(0,[z671,z67,z3,z4,z5,z6]),(0,[z1,z231,z3,z4,z5,z338]),(0,[z166,z1,z131,z252,z5,z6]),(0,[z1,z2,z734,z3,z5,z6]),(0,[z1,z2,z133,z3,z5,z6]),(0,[z1,z2,z735,z3,z5,z6]),(0,[z2,z3,z34,z5,z726,z6])],[(0,[z12,z2,z27,z4,z5,z95]),(0,[z1,z2,z332,z34,z5,z6]),(0,[z43,z1,z3,z4,z218,z44]),(0,[z1,z2,z34,z32,z94,z6]),(0,[z1,z2,z489,z34,z5,z6])],[(0,[z1,z2,z3,z122,z5,z342]),(0,[z471,z2,z48,z4,z5,z6]),(0,[z1,z2,z26,z3,z5,z338]),(0,[z553,z2,z3,z4,z49,z6]),(0,[z110,z1,z2,z4,z159,z6])],[(0,[z1,z2,z3,z4,z736,z6]),(0,[z1,z2,z737,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z5,z739]),(0,[z1,z2,z26,z3,z5,z270]),(0,[z1,z2,z144,z4,z93,z270])],[(0,[z1,z214,z3,z4,z5,z6]),(0,[z1,z2,z3,z238,z432,z6]),(0,[z1,z2,z3,z740,z5,z6]),(0,[z1,z2,z3,z4,z125,z611]),(0,[z1,z2,z3,z4,z5,z741])]],
   [[(0,[z28,z2,z3,z742,z5,z6]),(0,[z1,z3,z4,z730,z44,z6]),(0,[z1,z208,z2,z3,z4,z94]),(0,[z1,z2,z3,z4,z6,z477]),(0,[z1,z2,z74,z45,z3,z46])],[(0,[z1,z2,z3,z122,z13,z6]),(0,[z1,z2,z29,z4,z5,z225]),(0,[z1,z743,z3,z4,z5,z6]),(0,[z1,z2,z3,z744,z5,z6]),(0,[z1,z2,z745,z34,z5,z6])],[(0,[z1,z2,z26,z3,z13,z6]),(0,[z1,z246,z3,z4,z475,z6]),(0,[z295,z2,z3,z238,z5,z6]),(0,[z1,z2,z3,z252,z5,z321]),(0,[z1,z2,z3,z4,z5,z746])],[(0,[z1,z747,z3,z4,z5,z6])],[(0,[z1,z2,z34,z5,z366,z6]),(0,[z1,z2,z748,z4,z5,z6]),(0,[z167,z2,z3,z4,z5,z396])],[(0,[z2,z67,z27,z34,z5,z6]),(0,[z12,z129,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z749,z6]),(0,[z750,z2,z3,z4,z5,z6]),(0,[z751,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z378,z2,z3,z149,z6]),(0,[z1,z2,z144,z4,z93,z6])],[(0,[z179,z2,z3,z116,z5,z6]),(0,[z166,z1,z2,z138,z5,z6]),(0,[z1,z2,z26,z3,z100,z6]),(0,[z753,z2,z3,z4,z5,z6]),(0,[z1,z120,z26,z107,z5,z6]),(0,[z1,z2,z3,z754,z5,z6])],[(0,[z1,z98,z3,z4,z5,z556]),(0,[z1,z127,z120,z34,z5,z6]),(0,[z1,z214,z3,z34,z5,z6]),(0,[z163,z2,z26,z3,z50,z6]),(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z756,z4,z5,z6]),(0,[z497,z1,z3,z4,z44,z6]),(0,[z1,z211,z2,z26,z3,z6]),(0,[z1,z2,z243,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z741])]],
   [[(0,[z1,z2,z3,z4,z5,z757]),(0,[z1,z2,z692,z34,z5,z6]),(0,[z1,z2,z26,z3,z51,z6]),(0,[z166,z295,z2,z34,z5,z6]),(0,[z1,z2,z3,z4,z758,z6]),(0,[z1,z2,z3,z4,z759,z6]),(0,[z1,z2,z3,z34,z6,z477]),(0,[z1,z760,z26,z3,z5,z6]),(0,[z1,z2,z3,z5,z761,z6]),(0,[z1,z2,z3,z762,z5,z6])],[(0,[z43,z1,z78,z3,z4,z6]),(0,[z1,z2,z56,z3,z5,z563])],[(0,[z1,z2,z332,z29,z5,z6]),(0,[z1,z2,z521,z34,z5,z6]),(0,[z1,z208,z2,z3,z4,z93]),(0,[z1,z2,z74,z3,z149,z6])],[(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z2,z486,z34,z5,z6]),(0,[z1,z2,z3,z34,z766,z6]),(0,[z1,z2,z767,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z2,z3,z4,z475,z6]),(0,[z1,z2,z457,z34,z5,z6]),(0,[z1,z2,z106,z34,z5,z6]),(0,[z769,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z5,z101,z9]),(0,[z1,z2,z3,z4,z180,z125]),(0,[z1,z2,z118,z144,z93,z6])],[(0,[z166,z1,z131,z238,z5,z6]),(0,[z1,z98,z26,z3,z5,z101]),(0,[z1,z86,z2,z34,z5,z6]),(0,[z1,z2,z144,z34,z93,z6]),(0,[z1,z2,z223,z69,z94,z6]),(0,[z1,z770,z3,z4,z5,z6])],[(0,[z380,z1,z2,z34,z5,z6]),(0,[z1,z2,z3,z4,z771,z6]),(0,[z1,z2,z3,z4,z5,z772]),(0,[z1,z2,z26,z3,z112,z125])],[(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z3,z252,z100,z6]),(0,[z1,z2,z243,z34,z5,z6]),(0,[z1,z89,z2,z3,z4,z385])]],
   [[(0,[z1,z2,z3,z4,z775,z6]),(0,[z1,z2,z144,z446,z5,z6]),(0,[z1,z2,z144,z4,z93,z165])],[(0,[z1,z2,z3,z776,z5,z6]),(0,[z232,z97,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z94,z270])],[(0,[z1,z777,z3,z4,z5,z6]),(0,[z166,z295,z131,z4,z5,z6]),(0,[z1,z2,z14,z4,z5,z6])],[(0,[z2,z3,z4,z5,z778,z41]),(0,[z1,z211,z2,z3,z4,z177]),(0,[z1,z2,z3,z4,z5,z779]),(0,[z1,z97,z26,z3,z5,z8]),(0,[z1,z2,z22,z3,z5,z472]),(0,[z1,z2,z3,z780,z5,z6]),(0,[z1,z2,z3,z781,z5,z6])],[(0,[z1,z2,z3,z34,z475,z6]),(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z148,z3,z253,z5,z6]),(0,[z1,z2,z56,z14,z5,z52])],[(0,[z1,z2,z783,z4,z5,z6]),(0,[z1,z2,z784,z4,z5,z6]),(0,[z167,z2,z3,z4,z432,z6]),(0,[z166,z1,z131,z4,z5,z321]),(0,[z785,z2,z3,z4,z5,z6]),(0,[z1,z2,z156,z4,z5,z786]),(0,[z1,z2,z787,z4,z5,z6])],[(0,[z1,z17,z26,z3,z5,z6]),(0,[z1,z2,z26,z3,z5,z396]),(1,[z1,z2,z34,z5,z165]),(0,[z1,z2,z554,z34,z5,z6])],[(0,[z1,z2,z3,z4,z5,z788]),(0,[z43,z1,z3,z4,z44,z6]),(0,[z1,z2,z26,z3,z159,z6]),(0,[z1,z2,z3,z789,z5,z6])]],
   [[(0,[z1,z2,z315,z34,z5,z6]),(0,[z1,z2,z34,z5,z6,z563]),(0,[z1,z2,z3,z63,z5,z6])],[(0,[z66,z67,z3,z4,z5,z6]),(0,[z1,z2,z69,z3,z5,z6])],[(0,[z70,z2,z48,z4,z5,z6]),(0,[z1,z790,z3,z4,z5,z6]),(0,[z1,z2,z3,z791,z5,z6]),(0,[z1,z211,z2,z3,z4,z9]),(0,[z1,z2,z3,z4,z792,z6]),(0,[z1,z2,z144,z34,z94,z6])],[(0,[z1,z2,z793,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z531,z4,z94,z6]),(0,[z1,z2,z520,z34,z5,z9])],[(0,[z1,z211,z127,z3,z4,z6]),(0,[z1,z795,z3,z4,z5,z6]),(0,[z1,z2,z34,z418,z5,z6]),(0,[z1,z796,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z797]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z44,z94,z6]),(0,[z1,z2,z412,z34,z5,z6]),(0,[z1,z89,z2,z3,z4,z90])],[(0,[z127,z725,z3,z4,z5,z6]),(0,[z1,z2,z799,z3,z5,z6]),(0,[z1,z2,z14,z4,z112,z5])],[(0,[z1,z2,z401,z4,z51,z6]),(0,[z1,z2,z3,z252,z5,z396]),(0,[z800,z2,z3,z4,z5,z6]),(0,[z43,z1,z3,z34,z44,z6]),(0,[z1,z2,z3,z34,z5,z801]),(0,[z1,z2,z4,z5,z708,z6])]],
   [[(0,[z1,z2,z242,z34,z5,z6]),(0,[z2,z17,z3,z4,z5,z41]),(0,[z1,z2,z571,z34,z5,z6]),(0,[z1,z2,z3,z802,z5,z6]),(0,[z1,z2,z803,z3,z5,z6]),(0,[z1,z2,z804,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z805]),(0,[z66,z67,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z806]),(0,[z1,z2,z3,z238,z100,z6]),(0,[z1,z2,z34,z5,z6,z321]),(0,[z1,z120,z228,z107,z5,z6]),(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z2,z26,z397,z5,z6]),(0,[z1,z2,z283,z3,z5,z426]),(0,[z1,z2,z34,z5,z6,z584])],[(0,[z1,z2,z514,z34,z5,z6]),(0,[z70,z2,z48,z34,z5,z6]),(0,[z1,z808,z3,z4,z5,z6]),(0,[z71,z1,z2,z34,z5,z6]),(0,[z1,z211,z98,z2,z3,z4]),(0,[z1,z2,z633,z34,z5,z6])],[(0,[z115,z2,z3,z116,z5,z6]),(0,[z166,z167,z131,z4,z5,z6]),(0,[z1,z2,z3,z117,z5,z6]),(0,[z1,z2,z22,z14,z5,z6])],[(0,[z302,z2,z3,z4,z5,z8]),(0,[z1,z211,z2,z3,z4,z233])],[(0,[z1,z319,z3,z4,z5,z6]),(0,[z1,z246,z3,z4,z5,z150]),(0,[z566,z2,z3,z4,z5,z41]),(0,[z240,z2,z3,z4,z5,z778]),(0,[z161,z2,z3,z310,z5,z6]),(0,[z1,z2,z118,z3,z5,z270]),(0,[z1,z2,z3,z809,z46,z6]),(0,[z1,z2,z810,z3,z5,z6])],[(0,[z1,z2,z811,z4,z5,z6]),(0,[z1,z2,z490,z34,z5,z6]),(0,[z1,z2,z26,z812,z5,z6]),(0,[z1,z2,z133,z3,z55,z6]),(0,[z1,z2,z74,z3,z411,z46]),(0,[z1,z2,z56,z3,z5,z52])],[(0,[z1,z2,z813,z4,z5,z6]),(0,[z1,z2,z26,z3,z432,z6]),(0,[z1,z2,z814,z3,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z815,z6]),(0,[z17,z3,z4,z5,z6,z41]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z1,z2,z133,z34,z5,z6]),(0,[z1,z89,z2,z3,z4,z323])],[(0,[z817,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z100,z321]),(0,[z1,z2,z818,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z819]),(0,[z295,z2,z26,z3,z5,z6]),(0,[z302,z2,z3,z4,z112,z5]),(0,[z1,z2,z54,z34,z55,z6]),(0,[z1,z2,z820,z4,z5,z6])],[(0,[z1,z2,z3,z138,z5,z6]),(0,[z1,z97,z78,z3,z4,z5]),(0,[z1,z2,z4,z708,z94,z6])],[(0,[z1,z337,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z822,z4,z5,z6]),(0,[z1,z823,z3,z4,z5,z6]),(0,[z167,z2,z4,z34,z5,z6])],[(0,[z1,z2,z3,z824,z5,z6]),(0,[z638,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z342]),(0,[z1,z319,z3,z34,z5,z6]),(0,[z1,z2,z3,z825,z5,z6]),(0,[z1,z2,z358,z3,z5,z52])],[(0,[z1,z826,z3,z4,z5,z6]),(0,[z1,z2,z45,z3,z4,z5])],[(0,[z1,z827,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z150]),(0,[z1,z2,z828,z3,z5,z6]),(0,[z16,z2,z26,z3,z5,z41]),(0,[z110,z1,z2,z4,z100,z6]),(0,[z1,z2,z144,z34,z5,z270])]],
   [[(0,[z1,z129,z3,z34,z5,z6]),(0,[z1,z2,z47,z401,z5,z6]),(0,[z110,z167,z2,z4,z5,z6]),(0,[z1,z2,z3,z252,z432,z6]),(0,[z1,z2,z3,z4,z5,z829]),(0,[z1,z816,z3,z34,z5,z6])],[(0,[z1,z2,z3,z4,z830,z6]),(0,[z1,z2,z3,z4,z13,z6]),(0,[z1,z831,z3,z4,z5,z6]),(0,[z1,z416,z2,z34,z5,z6]),(0,[z1,z2,z697,z34,z5,z6]),(0,[z1,z211,z2,z3,z4,z41]),(0,[z1,z2,z3,z238,z5,z396]),(0,[z1,z2,z3,z4,z5,z832]),(0,[z1,z2,z3,z4,z5,z833])],[(0,[z1,z2,z3,z4,z5,z278]),(0,[z67,z3,z4,z5,z6,z268]),(0,[z1,z2,z834,z3,z5,z6]),(0,[z166,z1,z131,z4,z5,z396]),(0,[z1,z20,z2,z34,z5,z6]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z1,z835,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z352])],[(0,[z1,z2,z836,z3,z5,z6]),(0,[z295,z2,z3,z252,z5,z6]),(0,[z837,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z838,z5,z6]),(0,[z1,z2,z27,z34,z5,z6]),(0,[z1,z337,z3,z34,z5,z6])],[(0,[z1,z2,z3,z4,z5,z839]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z2,z3,z34,z5,z342]),(0,[z841,z2,z3,z4,z5,z6]),(0,[z1,z111,z515,z3,z5,z6])],[(0,[z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z40,z5,z95]),(0,[z28,z214,z3,z37,z5,z6]),(0,[z1,z2,z29,z4,z51,z6]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z1,z2,z3,z4,z843,z6]),(0,[z1,z3,z844,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z845]),(0,[z1,z2,z256,z4,z94,z6]),(0,[z1,z2,z144,z34,z5,z6]),(0,[z1,z2,z26,z14,z5,z6])],[(0,[z25,z2,z3,z4,z5,z268]),(0,[z1,z2,z657,z34,z5,z6]),(0,[z1,z2,z3,z34,z5,z150]),(0,[z2,z3,z116,z742,z5,z6]),(0,[z2,z3,z4,z5,z778,z6]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z167,z2,z3,z4,z100,z6]),(0,[z166,z1,z844,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z847,z5,z6]),(0,[z1,z2,z848,z3,z4,z5]),(0,[z1,z2,z334,z4,z5,z9]),(0,[z1,z2,z3,z849,z5,z6])],[(0,[z1,z2,z850,z4,z5,z6]),(0,[z1,z2,z3,z851,z5,z6]),(0,[z1,z2,z3,z4,z5,z124]),(0,[z1,z120,z107,z4,z5,z6]),(0,[z110,z1,z2,z4,z5,z165])],[(0,[z1,z2,z3,z34,z5,z278]),(0,[z1,z2,z26,z619,z5,z6]),(0,[z1,z2,z852,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z154,z34,z5,z6])],[(0,[z1,z246,z3,z4,z5,z225]),(0,[z1,z2,z3,z742,z5,z6]),(0,[z854,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z855,z5,z6]),(0,[z1,z2,z487,z34,z5,z6]),(0,[z1,z2,z623,z34,z5,z6]),(0,[z1,z2,z530,z3,z46,z6]),(0,[z856,z2,z3,z4,z5,z6]),(0,[z1,z857,z3,z4,z5,z6])],[(0,[z163,z2,z3,z4,z731,z6]),(0,[z858,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z5,z6,z639]),(0,[z1,z2,z3,z4,z112,z125])],[(0,[z1,z2,z859,z3,z5,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z1,z246,z26,z3,z5,z6]),(0,[z167,z2,z3,z34,z5,z6])],[(0,[z1,z129,z3,z40,z5,z6]),(0,[z1,z861,z3,z4,z5,z6]),(0,[z302,z3,z4,z5,z6,z8])]],
   [[(0,[z2,z3,z793,z4,z5,z6]),(0,[z862,z2,z3,z4,z5,z6]),(0,[z1,z2,z34,z5,z652,z6]),(0,[z1,z2,z520,z3,z5,z23]),(0,[z1,z2,z3,z5,z809,z6])],[(0,[z1,z2,z3,z34,z5,z124]),(0,[z1,z2,z3,z4,z863,z6]),(0,[z1,z120,z107,z34,z5,z6]),(0,[z1,z3,z740,z4,z5,z6]),(0,[z1,z111,z2,z397,z5,z6]),(0,[z1,z2,z144,z34,z5,z165]),(0,[z1,z2,z3,z4,z809,z6])],[(0,[z25,z31,z3,z4,z5,z6]),(1,[z2,z793,z4,z5,z6]),(0,[z1,z2,z864,z3,z5,z6]),(1,[z1,z3,z4,z5,z865]),(0,[z1,z2,z3,z4,z112,z331]),(0,[z1,z98,z3,z4,z5,z865])],[(0,[z1,z2,z3,z866,z5,z6]),(0,[z1,z2,z27,z40,z5,z6]),(0,[z28,z2,z3,z37,z475,z6]),(0,[z1,z2,z867,z4,z5,z6]),(0,[z166,z1,z131,z4,z432,z6]),(0,[z1,z2,z3,z4,z5,z218]),(0,[z1,z2,z3,z63,z55,z6])],[(0,[z868,z1,z2,z4,z5,z6]),(0,[z1,z2,z812,z143,z5,z6])],[(0,[z12,z319,z27,z4,z5,z6]),(0,[z1,z2,z3,z869,z5,z6]),(0,[z1,z2,z3,z4,z5,z225]),(0,[z1,z2,z870,z3,z5,z6])],[(0,[z232,z2,z3,z4,z5,z6]),(0,[z1,z231,z3,z4,z5,z6]),(0,[z1,z2,z3,z871,z5,z6]),(0,[z1,z872,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z17,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z100,z396]),(0,[z1,z155,z3,z4,z32,z6]),(0,[z1,z2,z874,z3,z5,z6]),(0,[z1,z2,z349,z34,z5,z6]),(0,[z1,z2,z156,z4,z5,z9])],[(0,[z66,z67,z3,z4,z5,z268]),(0,[z1,z2,z3,z122,z5,z6]),(0,[z70,z2,z47,z48,z5,z6]),(0,[z1,z2,z223,z446,z94,z6]),(0,[z1,z2,z3,z4,z93,z270])]],
   [[(0,[z1,z2,z26,z3,z5,z6]),(0,[z677,z2,z3,z4,z5,z41]),(0,[z1,z120,z2,z138,z5,z6]),(0,[z1,z2,z3,z4,z112,z639])],[(0,[z1,z2,z3,z4,z875,z6]),(0,[z1,z2,z876,z4,z5,z6]),(0,[z240,z2,z3,z4,z5,z177]),(0,[z1,z120,z276,z4,z5,z6])],[(0,[z1,z129,z3,z4,z5,z95]),(0,[z1,z2,z3,z877,z5,z6]),(0,[z878,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z432,z321])],[(0,[z1,z2,z34,z49,z94,z6]),(0,[z1,z2,z3,z34,z5,z218]),(0,[z1,z2,z38,z34,z94,z6])],[(0,[z1,z209,z3,z4,z5,z8]),(0,[z1,z211,z2,z3,z34,z6]),(0,[z1,z2,z22,z3,z5,z23])],[(0,[z25,z127,z3,z4,z5,z6]),(0,[z12,z2,z27,z4,z5,z342]),(0,[z1,z879,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z5,z225]),(0,[z636,z2,z3,z4,z5,z41]),(0,[z295,z2,z3,z4,z5,z321]),(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z2,z694,z34,z5,z6])],[(0,[z2,z3,z4,z742,z5,z6]),(0,[z1,z231,z3,z34,z5,z6]),(0,[z1,z881,z3,z4,z5,z6]),(0,[z166,z1,z2,z34,z5,z321]),(0,[z1,z155,z3,z34,z32,z6]),(0,[z302,z2,z3,z4,z5,z101]),(0,[z232,z2,z3,z34,z5,z6]),(0,[z1,z2,z156,z34,z5,z9]),(0,[z1,z2,z144,z4,z539,z6]),(0,[z1,z2,z3,z4,z5,z786])],[(0,[z882,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z883]),(0,[z1,z884,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z885,z5,z6]),(0,[z886,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z887]),(0,[z1,z2,z3,z4,z888,z6]),(0,[z12,z2,z27,z4,z13,z6]),(0,[z1,z214,z3,z4,z475,z6]),(0,[z1,z2,z889,z4,z5,z6]),(0,[z240,z2,z3,z34,z5,z177]),(0,[z1,z2,z3,z252,z5,z6]),(0,[z1,z120,z276,z34,z5,z6]),(0,[z1,z2,z890,z3,z4,z5]),(0,[z1,z2,z26,z3,z5,z411]),(0,[z1,z2,z26,z624,z5,z6]),(0,[z1,z2,z891,z4,z5,z6])],[(0,[z1,z2,z3,z892,z5,z6]),(0,[z1,z2,z688,z34,z5,z6]),(0,[z110,z1,z2,z47,z5,z6]),(0,[z1,z2,z3,z4,z893,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z4,z895,z6])],[(0,[z1,z677,z3,z4,z5,z8]),(0,[z1,z2,z293,z34,z5,z6]),(0,[z1,z2,z896,z3,z4,z5]),(0,[z1,z2,z897,z4,z5,z6]),(0,[z1,z251,z26,z3,z5,z6]),(0,[z898,z2,z3,z4,z5,z6]),(0,[z302,z89,z2,z3,z4,z5]),(0,[z1,z2,z26,z3,z5,z165])],[(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z2,z3,z4,z475,z225]),(0,[z1,z2,z3,z4,z5,z778]),(0,[z64,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z350,z34,z5,z6]),(0,[z1,z2,z22,z3,z5,z761])],[(0,[z1,z2,z901,z4,z5,z6]),(0,[z1,z246,z401,z4,z5,z6]),(0,[z1,z211,z2,z3,z4,z6])],[(0,[z380,z2,z27,z4,z5,z6]),(0,[z1,z2,z3,z4,z271,z6]),(0,[z70,z129,z3,z4,z5,z6]),(0,[z147,z231,z3,z4,z49,z6]),(0,[z1,z2,z34,z5,z6,z706]),(0,[z1,z2,z186,z5,z46,z6])],[(0,[z1,z2,z3,z4,z902,z6]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z97,z3,z4,z477,z8]),(0,[z1,z2,z745,z144,z5,z6])]],
   [[(0,[z147,z2,z26,z3,z49,z6]),(0,[z97,z302,z3,z4,z5,z8])],[(0,[z1,z2,z904,z3,z5,z6]),(0,[z1,z2,z905,z3,z5,z6]),(0,[z240,z17,z3,z4,z5,z6]),(0,[z1,z2,z906,z3,z4,z6]),(0,[z1,z2,z3,z446,z5,z6]),(0,[z1,z2,z201,z4,z5,z9])],[(0,[z295,z2,z3,z4,z100,z6]),(0,[z1,z2,z256,z34,z5,z6])],[(0,[z1,z2,z3,z4,z5,z907]),(0,[z166,z1,z2,z34,z100,z6])],[(0,[z1,z2,z908,z4,z5,z6]),(0,[z1,z2,z42,z3,z5,z23]),(0,[z166,z167,z2,z34,z5,z6]),(0,[z1,z2,z3,z909,z5,z6]),(0,[z1,z3,z4,z5,z101,z865]),(0,[z1,z2,z910,z3,z34,z5]),(0,[z1,z2,z56,z3,z540,z5])],[(0,[z66,z725,z3,z4,z5,z6]),(0,[z1,z2,z14,z34,z5,z6])],[(0,[z1,z2,z3,z34,z271,z6]),(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z2,z912,z4,z5,z6]),(0,[z1,z2,z54,z311,z5,z6])],[(0,[z1,z2,z401,z4,z5,z6]),(0,[z16,z2,z3,z4,z5,z778]),(0,[z1,z2,z34,z5,z41,z9])]],
   [[(0,[z2,z27,z310,z34,z5,z6]),(0,[z1,z2,z913,z3,z5,z6])],[(0,[z302,z2,z3,z4,z5,z6]),(0,[z43,z1,z3,z4,z291,z6]),(0,[z1,z2,z3,z4,z5,z718]),(0,[z1,z2,z914,z4,z5,z6]),(0,[z1,z2,z4,z34,z5,z321]),(0,[z1,z302,z3,z4,z5,z8])],[(0,[z25,z725,z3,z4,z5,z6]),(1,[z2,z3,z742,z5,z6]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z2,z3,z916,z5,z6])],[(0,[z615,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z238,z5,z6]),(0,[z1,z2,z228,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z89,z2,z3,z4,z462]),(0,[z1,z2,z102,z156,z5,z9])],[(0,[z1,z17,z3,z4,z5,z41]),(0,[z166,z1,z131,z4,z5,z6]),(0,[z1,z2,z303,z34,z5,z6]),(0,[z918,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z311,z5,z6]),(0,[z1,z2,z4,z5,z786,z6])],[(0,[z166,z1,z131,z4,z100,z6]),(0,[z1,z2,z910,z3,z4,z5])],[(0,[z28,z2,z3,z37,z5,z150]),(0,[z1,z2,z919,z3,z5,z6]),(0,[z1,z2,z26,z186,z5,z6])],[(0,[z1,z2,z3,z4,z5,z920]),(0,[z12,z2,z27,z122,z5,z6]),(0,[z1,z2,z401,z34,z5,z6]),(0,[z1,z921,z3,z4,z5,z6]),(0,[z1,z2,z247,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z922]),(0,[z1,z2,z3,z4,z432,z396]),(1,[z1,z3,z4,z730,z6]),(0,[z1,z923,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z267,z5,z6]),(0,[z1,z2,z3,z4,z5,z924]),(0,[z1,z2,z649,z3,z76,z6]),(0,[z1,z2,z925,z3,z4,z5])],[(0,[z1,z2,z3,z122,z5,z95]),(0,[z248,z1,z2,z34,z5,z6]),(0,[z302,z2,z3,z34,z5,z6]),(0,[z1,z926,z3,z4,z5,z6]),(0,[z1,z2,z530,z4,z94,z6]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z3,z927,z5,z6]),(0,[z1,z2,z3,z928,z5,z6])],[(0,[z1,z2,z26,z3,z5,z95]),(0,[z295,z2,z3,z4,z5,z396]),(0,[z1,z2,z3,z929,z5,z6]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z1,z2,z446,z5,z94,z6])],[(0,[z1,z2,z114,z34,z5,z6]),(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z2,z931,z4,z5,z6]),(0,[z1,z2,z932,z4,z5,z6]),(0,[z1,z2,z91,z34,z5,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z1,z2,z3,z4,z5,z321]),(0,[z1,z2,z3,z934,z5,z6]),(0,[z166,z1,z2,z34,z5,z396]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z26,z3,z5,z936]),(0,[z1,z2,z3,z4,z5,z937]),(0,[z1,z2,z3,z5,z23,z761])],[(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z246,z29,z4,z5,z6]),(0,[z1,z939,z3,z4,z5,z6]),(0,[z166,z1,z131,z34,z5,z6]),(0,[z1,z2,z4,z5,z786,z9])],[(0,[z1,z2,z940,z3,z5,z6]),(0,[z1,z2,z3,z40,z271,z6]),(0,[z1,z941,z3,z4,z5,z6]),(0,[z1,z2,z448,z34,z5,z6])],[(0,[z1,z2,z620,z34,z5,z6]),(0,[z1,z2,z942,z3,z5,z6]),(0,[z1,z2,z4,z34,z100,z6]),(0,[z1,z361,z2,z34,z5,z6]),(0,[z1,z2,z144,z117,z93,z6]),(0,[z1,z2,z341,z4,z93,z6])],[(0,[z1,z2,z3,z4,z5,z338]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z16,z17,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z2,z118,z3,z5,z6]),(0,[z1,z2,z357,z34,z5,z6])]],
   [[(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z246,z3,z4,z51,z6]),(0,[z1,z2,z946,z4,z5,z6]),(0,[z166,z1,z120,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z270]),(0,[z1,z2,z947,z4,z5,z6])],[(0,[z70,z2,z692,z4,z5,z6]),(0,[z1,z926,z3,z34,z5,z6]),(0,[z1,z2,z530,z34,z94,z6])],[(0,[z1,z2,z948,z3,z5,z6]),(0,[z1,z97,z3,z4,z5,z865]),(0,[z1,z97,z211,z2,z3,z4])],[(0,[z1,z949,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z950]),(0,[z1,z2,z3,z34,z5,z321]),(0,[z1,z2,z26,z3,z55,z6]),(0,[z1,z951,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z952]),(0,[z1,z214,z3,z4,z5,z150]),(0,[z1,z314,z3,z4,z5,z101]),(0,[z703,z2,z3,z4,z5,z177]),(0,[z953,z2,z3,z4,z5,z6]),(0,[z1,z3,z740,z128,z5,z6]),(0,[z1,z591,z3,z4,z32,z6]),(0,[z1,z954,z2,z26,z3,z5]),(0,[z1,z2,z26,z646,z5,z6]),(0,[z1,z3,z4,z5,z6,z955]),(0,[z1,z2,z3,z956,z5,z6])],[(0,[z1,z2,z3,z4,z5,z957]),(0,[z1,z108,z2,z34,z5,z6]),(0,[z1,z2,z958,z3,z5,z6]),(0,[z1,z2,z3,z4,z6,z959]),(0,[z1,z2,z960,z4,z5,z6])],[(0,[z2,z67,z3,z4,z5,z268]),(0,[z1,z2,z26,z3,z5,z268]),(0,[z1,z2,z3,z961,z5,z6]),(0,[z12,z2,z27,z4,z271,z6]),(0,[z1,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z962,z5,z6]),(0,[z1,z668,z2,z34,z5,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z2,z3,z4,z964,z6]),(0,[z1,z2,z243,z133,z5,z6]),(0,[z1,z2,z75,z186,z5,z6])],[(0,[z67,z3,z274,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z34,z5,z338]),(0,[z1,z2,z3,z4,z6,z966])]],
   [[(0,[z1,z2,z3,z4,z967,z6]),(0,[z1,z2,z3,z4,z968,z6]),(0,[z1,z2,z3,z4,z271,z95]),(0,[z1,z2,z136,z34,z5,z6]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z34,z5,z6,z9]),(0,[z1,z2,z3,z34,z5,z270]),(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z2,z971,z4,z5,z6])],[(0,[z163,z2,z3,z4,z50,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z120,z844,z4,z5,z6]),(1,[z1,z2,z812,z5,z6]),(0,[z1,z2,z283,z3,z5,z52])],[(0,[z1,z2,z3,z973,z5,z6]),(0,[z1,z760,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z51,z6]),(0,[z1,z83,z2,z397,z5,z6]),(0,[z1,z155,z3,z4,z6,z662]),(0,[z1,z2,z34,z5,z159,z6]),(0,[z110,z1,z2,z118,z5,z6]),(0,[z1,z2,z118,z3,z5,z165])],[(0,[z1,z2,z3,z4,z5,z974]),(0,[z725,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z49,z731,z6]),(1,[z2,z3,z4,z5,z778]),(0,[z295,z2,z3,z4,z432,z6]),(0,[z1,z2,z143,z34,z5,z6]),(0,[z1,z2,z34,z5,z6,z165]),(0,[z1,z2,z767,z34,z5,z6]),(0,[z1,z2,z186,z4,z5,z6]),(1,[z1,z2,z4,z708,z6]),(0,[z1,z2,z3,z4,z125,z966])],[(0,[z1,z2,z3,z34,z13,z6]),(0,[z28,z2,z3,z37,z5,z225]),(0,[z166,z1,z2,z34,z432,z6]),(0,[z1,z20,z3,z4,z5,z8]),(0,[z1,z2,z3,z34,z5,z832])],[(0,[z1,z2,z3,z4,z975,z6]),(0,[z1,z2,z976,z4,z5,z6]),(0,[z43,z1,z3,z4,z730,z6])],[(0,[z1,z2,z29,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z977]),(0,[z1,z2,z3,z4,z5,z978]),(0,[z1,z2,z34,z5,z180,z6])],[(0,[z544,z1,z2,z34,z5,z6]),(0,[z1,z319,z3,z40,z5,z6]),(0,[z1,z2,z3,z4,z979,z6]),(0,[z147,z337,z3,z4,z49,z6]),(0,[z147,z2,z3,z4,z49,z338]),(0,[z1,z98,z3,z4,z5,z101]),(0,[z1,z2,z4,z34,z159,z6]),(0,[z1,z2,z223,z4,z708,z6]),(0,[z1,z2,z74,z103,z46,z6])]],
   [[(0,[z2,z48,z793,z4,z5,z6]),(0,[z71,z1,z2,z238,z5,z6]),(0,[z1,z2,z3,z34,z100,z6]),(0,[z1,z2,z3,z4,z6,z980]),(0,[z1,z2,z34,z5,z6,z191]),(0,[z1,z2,z3,z4,z5,z411]),(0,[z1,z2,z56,z3,z5,z761])],[(0,[z1,z129,z3,z4,z271,z6]),(0,[z1,z2,z3,z4,z475,z150]),(0,[z163,z2,z3,z34,z50,z6]),(0,[z1,z2,z981,z3,z5,z6]),(0,[z1,z2,z54,z34,z5,z9])],[(0,[z1,z2,z982,z4,z5,z6]),(0,[z1,z2,z3,z34,z51,z6]),(0,[z1,z2,z3,z4,z983,z6]),(0,[z1,z2,z74,z3,z809,z6])],[(0,[z1,z2,z186,z34,z5,z6])],[(0,[z1,z2,z34,z5,z196,z6]),(0,[z1,z2,z311,z5,z6,z9]),(0,[z1,z984,z3,z4,z5,z6])],[(0,[z1,z2,z29,z116,z5,z6]),(0,[z1,z2,z985,z4,z5,z6]),(0,[z1,z2,z986,z4,z5,z6]),(0,[z1,z97,z3,z4,z5,z8]),(0,[z1,z3,z4,z5,z6,z865])],[(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z2,z904,z34,z5,z6]),(0,[z369,z2,z3,z4,z49,z6]),(0,[z502,z2,z3,z4,z5,z177])],[(0,[z1,z2,z3,z40,z5,z342]),(0,[z1,z2,z989,z4,z5,z6]),(0,[z1,z2,z990,z34,z5,z6]),(0,[z166,z1,z351,z4,z5,z6]),(0,[z1,z98,z3,z34,z5,z101]),(0,[z1,z2,z26,z11,z5,z6]),(0,[z1,z2,z133,z3,z159,z6])]],
   [[(0,[z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z396]),(0,[z71,z1,z2,z26,z5,z6]),(1,[z302,z3,z4,z5,z8]),(0,[z1,z2,z3,z34,z112,z125])],[(0,[z1,z2,z422,z3,z46,z6]),(0,[z1,z2,z3,z991,z5,z6]),(0,[z1,z2,z3,z4,z159,z6]),(0,[z1,z992,z3,z4,z5,z6])],[(0,[z356,z67,z3,z4,z5,z6]),(0,[z1,z2,z993,z4,z5,z6]),(0,[z1,z319,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z994]),(0,[z1,z2,z995,z3,z5,z6]),(0,[z1,z214,z3,z4,z5,z225]),(0,[z512,z1,z2,z34,z5,z6]),(0,[z1,z2,z26,z243,z5,z6])],[(0,[z1,z2,z3,z40,z13,z6]),(0,[z1,z2,z204,z34,z5,z6]),(1,[z17,z3,z4,z5,z41]),(0,[z1,z2,z205,z34,z5,z6]),(0,[z1,z2,z54,z34,z159,z6]),(0,[z1,z2,z54,z34,z5,z233]),(0,[z996,z2,z3,z4,z5,z6])],[(0,[z1,z2,z997,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z70,z2,z793,z4,z5,z6]),(0,[z1,z2,z904,z48,z5,z6]),(0,[z147,z2,z3,z4,z49,z124])],[(0,[z1,z2,z3,z999,z5,z6]),(0,[z1,z214,z26,z3,z5,z6]),(0,[z1,z2,z1000,z3,z5,z6]),(0,[z1,z97,z3,z34,z5,z8]),(0,[z1,z2,z102,z3,z5,z6])],[(0,[z240,z2,z3,z4,z5,z346]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z1,z2,z26,z3,z6,z477]),(0,[z674,z2,z3,z545,z5,z6])],[(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z2,z689,z34,z5,z6]),(0,[z1,z2,z812,z3,z5,z6]),(0,[z1,z2,z34,z5,z94,z6])]],
   [[(0,[z725,z67,z3,z4,z5,z6]),(0,[z1,z120,z505,z4,z5,z6]),(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1,z2,z1003,z3,z4,z6]),(0,[z1,z1004,z3,z4,z5,z6]),(0,[z1,z17,z3,z34,z5,z6]),(0,[z1,z2,z3,z34,z5,z396])],[(0,[z66,z67,z3,z4,z5,z278]),(0,[z1,z2,z3,z4,z1005,z6]),(1,[z2,z3,z4,z731,z6]),(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z745,z3,z5,z6]),(0,[z1,z2,z3,z34,z159,z6])],[(0,[z1,z2,z1007,z3,z5,z6]),(0,[z1,z3,z4,z5,z865,z8]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z1,z2,z1009,z3,z5,z6])],[(0,[z1,z1010,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z2,z103,z4,z5,z6]),(0,[z996,z2,z3,z34,z5,z6])],[(0,[z1,z2,z1012,z3,z5,z6]),(0,[z2,z3,z742,z37,z5,z6]),(0,[z1,z2,z3,z4,z1013,z6])],[(0,[z576,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z3,z1015,z5,z6]),(0,[z115,z2,z3,z742,z5,z6]),(0,[z1,z2,z238,z34,z5,z6]),(0,[z1,z2,z3,z1016,z5,z6]),(0,[z1,z111,z2,z34,z5,z6]),(0,[z1,z3,z4,z32,z730,z6])],[(0,[z1,z2,z3,z4,z13,z95]),(0,[z28,z2,z401,z37,z5,z6]),(0,[z1,z2,z344,z34,z5,z6])],[(0,[z325,z127,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z2,z34,z5,z6,z701])]],
   [[(0,[z1,z2,z3,z4,z1018,z6]),(0,[z25,z127,z3,z34,z5,z6]),(0,[z1,z2,z1019,z4,z5,z6]),(0,[z1,z255,z89,z2,z3,z4])],[(0,[z2,z48,z27,z34,z5,z6]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1,z2,z3,z5,z6,z1021]),(0,[z1,z2,z3,z4,z432,z6]),(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z34,z5,z258,z6]),(0,[z1,z2,z3,z4,z5,z1023])],[(0,[z1,z2,z26,z3,z475,z6]),(0,[z1,z2,z26,z613,z5,z6]),(0,[z1,z2,z1024,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1025]),(0,[z1,z129,z3,z4,z5,z342]),(0,[z529,z2,z3,z4,z5,z41]),(0,[z1,z2,z1026,z3,z5,z6]),(0,[z1,z2,z34,z5,z8,z9]),(0,[z1,z2,z103,z34,z5,z6]),(0,[z1,z2,z412,z14,z5,z6])],[(0,[z295,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z96]),(0,[z1,z2,z26,z440,z5,z6]),(0,[z1,z2,z201,z34,z5,z6])],[(0,[z674,z2,z27,z4,z5,z6]),(0,[z674,z2,z3,z37,z5,z6]),(0,[z166,z1,z2,z34,z5,z6]),(0,[z110,z1,z2,z133,z5,z6])],[(0,[z1,z2,z34,z5,z6,z269]),(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z2,z3,z1028,z5,z6]),(0,[z1,z82,z2,z397,z5,z6]),(0,[z1,z2,z283,z4,z5,z9]),(0,[z1,z2,z3,z4,z966,z90])],[(0,[z1,z211,z67,z3,z4,z6]),(0,[z1,z129,z3,z4,z13,z6]),(0,[z1,z1029,z3,z4,z5,z6]),(0,[z1,z2,z34,z5,z272,z6]),(0,[z1,z2,z341,z34,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1030,z6]),(0,[z1,z1031,z3,z4,z5,z6]),(0,[z1,z208,z2,z26,z3,z5]),(0,[z1,z2,z661,z34,z5,z6]),(1,[z1,z2,z3,z4,z966])],[(0,[z1,z1032,z2,z3,z4,z5]),(0,[z16,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z1033,z6]),(0,[z1,z2,z3,z34,z432,z6])],[(0,[z2,z793,z27,z4,z5,z6]),(0,[z1034,z2,z3,z4,z5,z6]),(0,[z1,z208,z2,z3,z34,z5])],[(0,[z1,z1035,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1,z2,z47,z3,z5,z6]),(0,[z1,z2,z298,z4,z93,z6]),(0,[z1,z2,z326,z34,z5,z6]),(0,[z1,z167,z2,z34,z5,z6]),(0,[z1,z148,z3,z128,z5,z6]),(0,[z1037,z2,z3,z4,z5,z6]),(0,[z1,z2,z436,z34,z5,z6])],[(0,[z1,z2,z274,z34,z5,z6]),(0,[z1,z214,z401,z4,z5,z6]),(0,[z295,z2,z3,z34,z5,z6]),(0,[z1,z3,z4,z5,z1038,z6])],[(0,[z1,z2,z3,z4,z5,z268]),(0,[z290,z67,z3,z4,z5,z6]),(0,[z674,z2,z27,z34,z5,z6]),(1,[z1,z844,z4,z5,z6]),(0,[z1,z1039,z2,z3,z4,z5]),(0,[z43,z1,z26,z3,z44,z6]),(0,[z1,z2,z437,z186,z5,z6])],[(0,[z1,z2,z1040,z4,z5,z6]),(0,[z1,z2,z3,z1041,z5,z6]),(0,[z1,z2,z283,z34,z5,z9]),(0,[z1,z2,z3,z4,z1042,z6]),(0,[z1,z1043,z3,z4,z5,z6])],[(0,[z66,z67,z26,z3,z5,z6]),(0,[z2,z3,z4,z5,z177,z778])]],
   [[(0,[z1,z3,z34,z5,z1038,z6]),(0,[z1,z2,z223,z4,z94,z6])],[(0,[z1,z2,z1044,z4,z5,z6]),(0,[z16,z2,z3,z34,z5,z41]),(0,[z1,z2,z3,z1045,z5,z6]),(0,[z1,z374,z2,z3,z5,z563])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z120,z107,z138,z5,z6]),(0,[z1,z2,z3,z1047,z5,z6]),(0,[z1,z2,z3,z4,z55,z9])],[(0,[z1,z337,z3,z4,z5,z124]),(0,[z1,z2,z26,z45,z3,z5])],[(0,[z1,z2,z3,z1048,z5,z6]),(0,[z16,z251,z3,z4,z5,z41]),(0,[z1,z2,z34,z5,z100,z6])],[(0,[z1,z2,z1049,z3,z5,z6]),(0,[z28,z2,z29,z37,z5,z6]),(0,[z1,z2,z3,z4,z731,z6]),(0,[z1,z2,z1050,z4,z5,z6]),(0,[z1,z2,z26,z103,z5,z6])],[(0,[z164,z127,z3,z4,z5,z6]),(0,[z1,z1051,z3,z4,z5,z6]),(0,[z1,z2,z34,z50,z94,z6]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z62,z2,z487,z3,z5,z6])],[(0,[z166,z1,z2,z990,z5,z6])]],
   [[(0,[z1,z246,z3,z4,z5,z6]),(0,[z1,z2,z3,z1053,z5,z6]),(0,[z458,z1,z2,z34,z5,z6]),(0,[z1,z2,z1054,z3,z4,z6]),(0,[z1,z2,z223,z34,z94,z6]),(0,[z1,z1055,z3,z4,z5,z6]),(0,[z1,z2,z1056,z3,z5,z6])],[(0,[z678,z1,z3,z4,z5,z8]),(0,[z1,z2,z48,z34,z5,z6]),(0,[z1,z2,z3,z4,z1057,z6]),(0,[z1,z2,z401,z4,z475,z6]),(0,[z28,z2,z3,z37,z51,z6]),(0,[z1,z83,z515,z3,z5,z6]),(0,[z1,z2,z1058,z3,z5,z6])],[(0,[z1,z319,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z5,z1059]),(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z89,z2,z3,z4,z700]),(0,[z1,z2,z3,z4,z5,z966])],[(0,[z1,z319,z26,z3,z5,z6]),(0,[z1061,z2,z3,z4,z5,z6])],[(0,[z1,z2,z812,z4,z5,z6]),(0,[z1,z1062,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z55,z233])],[(0,[z1,z129,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1064,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1065,z6]),(0,[z1,z129,z26,z3,z5,z6]),(0,[z1,z2,z1066,z4,z5,z6]),(0,[z1,z2,z3,z4,z112,z966])],[(0,[z1,z2,z3,z1067,z5,z6]),(0,[z1,z2,z34,z5,z137,z6]),(0,[z1,z309,z2,z34,z5,z6]),(0,[z1,z2,z26,z3,z1068,z6]),(0,[z1,z2,z1069,z4,z5,z6])]],
   [[(0,[z197,z67,z3,z4,z5,z6]),(0,[z1,z246,z3,z34,z5,z6]),(0,[z1,z1070,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z1,z1072,z2,z3,z4,z5]),(0,[z1,z2,z26,z34,z5,z6])],[(0,[z1,z1073,z3,z4,z5,z6]),(0,[z1,z2,z1074,z3,z5,z6]),(0,[z1,z2,z243,z56,z5,z52])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1075,z6]),(0,[z1,z67,z3,z4,z5,z268]),(0,[z1,z1076,z3,z4,z5,z6]),(0,[z1,z337,z26,z3,z5,z6]),(0,[z1,z2,z34,z5,z149,z6]),(1,[z1,z2,z3,z5,z761])],[(0,[z1,z2,z3,z4,z1077,z6]),(0,[z1,z2,z26,z3,z5,z342]),(0,[z1,z214,z29,z4,z5,z6]),(0,[z1,z1078,z3,z4,z5,z6]),(0,[z43,z1,z208,z3,z4,z44]),(0,[z1,z2,z34,z5,z151,z6]),(0,[z1,z2,z4,z34,z5,z165]),(0,[z1,z2,z633,z4,z94,z6]),(0,[z1,z1079,z3,z4,z5,z6])],[(1,[z1,z2,z34,z5,z321]),(0,[z1,z148,z120,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z1080]),(0,[z1,z2,z1081,z4,z5,z6]),(0,[z1,z2,z812,z34,z5,z6]),(0,[z1,z2,z54,z34,z5,z6])],[(0,[z1,z2,z26,z3,z5,z150]),(0,[z199,z2,z3,z4,z5,z177]),(0,[z1,z2,z1082,z4,z5,z6])],[],[(0,[z1,z214,z3,z4,z51,z6]),(0,[z1,z2,z3,z1083,z5,z6]),(0,[z2,z3,z4,z5,z731,z6]),(0,[z1,z2,z1084,z4,z5,z6])]],
   [[(0,[z1,z2,z26,z3,z5,z278]),(0,[z209,z67,z3,z4,z5,z6]),(0,[z1,z2,z48,z40,z5,z6]),(0,[z1,z2,z3,z4,z5,z1085]),(0,[z1086,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z766,z6])],[(0,[z1,z2,z1088,z4,z5,z6]),(0,[z1,z592,z3,z128,z5,z6]),(0,[z572,z127,z3,z4,z5,z6]),(0,[z1,z319,z3,z4,z271,z6])],[(0,[z1,z2,z3,z34,z5,z6]),(0,[z129,z3,z27,z4,z5,z6]),(0,[z1,z2,z34,z5,z6,z370]),(0,[z1,z2,z3,z4,z51,z225]),(0,[z0,z1,z2,z26,z5,z6]),(0,[z1,z954,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z112,z113])],[(0,[z1,z2,z3,z1089,z5,z6]),(0,[z1,z1090,z3,z4,z5,z6]),(0,[z1,z2,z453,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z1091]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z2,z34,z372,z5,z6])],[(0,[z1,z2,z1093,z4,z5,z6]),(0,[z167,z2,z26,z3,z5,z6]),(0,[z1,z2,z3,z4,z6,z1094]),(0,[z1,z2,z1095,z4,z5,z6]),(0,[z1096,z2,z3,z4,z5,z6])],[(0,[z1,z251,z3,z4,z5,z6]),(0,[z1,z1097,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1098]),(0,[z1,z231,z3,z4,z5,z124]),(0,[z1,z2,z34,z5,z6,z193]),(0,[z1,z2,z3,z4,z5,z165])],[(0,[z25,z2,z27,z34,z5,z6]),(0,[z1,z2,z26,z29,z5,z6]),(0,[z1,z2,z3,z4,z5,z1099])],[(0,[z1,z2,z26,z3,z5,z124]),(0,[z1,z2,z523,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z1100])]],
   [[(0,[z1,z2,z1101,z3,z5,z6]),(0,[z70,z2,z48,z267,z5,z6]),(0,[z1,z2,z29,z4,z475,z6]),(0,[z1,z2,z34,z112,z5,z9])],[(0,[z1,z2,z3,z4,z271,z342]),(0,[z12,z2,z793,z4,z5,z6]),(0,[z1,z2,z3,z4,z1102,z6]),(1,[z1,z2,z34,z100,z6]),(0,[z179,z2,z332,z3,z5,z6])],[(0,[z1,z1103,z3,z4,z5,z6]),(0,[z1,z2,z183,z34,z5,z6]),(0,[z147,z2,z3,z4,z49,z6]),(1,[z167,z2,z34,z5,z6]),(0,[z1,z2,z397,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1104])],[(0,[z1,z2,z3,z4,z5,z1105]),(0,[z1,z83,z3,z128,z5,z6]),(0,[z1,z2,z3,z34,z5,z411])],[(0,[z1,z2,z3,z1106,z5,z6]),(0,[z1,z89,z2,z34,z5,z9]),(0,[z1,z860,z26,z3,z5,z6]),(0,[z1,z2,z26,z223,z94,z6]),(0,[z1107,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1108,z5,z6]),(0,[z1,z2,z3,z4,z1109,z6]),(0,[z1,z251,z3,z34,z5,z6]),(0,[z167,z2,z3,z252,z5,z6]),(0,[z1,z2,z844,z4,z5,z6]),(0,[z1110,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z34,z983,z6]),(0,[z1,z2,z3,z34,z5,z165]),(0,[z1,z2,z54,z767,z5,z6]),(0,[z1,z2,z530,z3,z35,z6]),(0,[z1,z1111,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z761,z52])],[(0,[z497,z1,z2,z34,z5,z6]),(0,[z1,z2,z375,z34,z5,z6]),(0,[z1,z2,z412,z3,z5,z472])],[(0,[z12,z2,z26,z27,z5,z6]),(0,[z1,z2,z1112,z4,z5,z6]),(0,[z1,z2,z3,z1113,z5,z6]),(0,[z1,z89,z2,z26,z3,z90])]],
   [[(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z725,z3,z4,z5,z6]),(0,[z1,z2,z3,z1115,z5,z6]),(0,[z1,z2,z47,z34,z5,z6]),(0,[z1,z2,z1116,z4,z5,z6]),(0,[z1,z2,z683,z34,z5,z6]),(0,[z1,z2,z7,z34,z5,z6]),(0,[z1,z2,z34,z5,z6,z221])],[(0,[z1,z2,z1117,z4,z5,z6]),(0,[z1,z2,z3,z40,z5,z6]),(0,[z1,z1118,z3,z4,z5,z6]),(0,[z115,z2,z3,z310,z5,z6]),(0,[z1,z2,z34,z5,z6,z402]),(0,[z1,z2,z3,z238,z5,z321]),(0,[z1,z327,z2,z34,z5,z6]),(0,[z1,z2,z26,z3,z5,z218]),(0,[z1,z89,z2,z3,z34,z90])],[(0,[z1,z675,z3,z4,z32,z6]),(0,[z147,z2,z3,z34,z49,z6]),(0,[z1,z2,z397,z34,z5,z6]),(0,[z1,z2,z1119,z3,z5,z6]),(0,[z1,z2,z3,z1120,z5,z6])],[(0,[z1,z2,z26,z3,z5,z225]),(0,[z1121,z2,z3,z4,z5,z6]),(0,[z1,z2,z1122,z3,z5,z6]),(0,[z1,z2,z476,z34,z5,z6]),(0,[z1,z2,z3,z1123,z5,z6]),(0,[z1,z2,z34,z5,z407,z6]),(0,[z1,z97,z211,z3,z4,z8]),(0,[z1,z89,z2,z3,z4,z273]),(0,[z1,z2,z3,z4,z5,z1124])],[(0,[z529,z67,z3,z4,z5,z6]),(0,[z1,z2,z401,z4,z5,z150]),(0,[z28,z2,z487,z3,z5,z6]),(0,[z1,z2,z3,z4,z6,z1125]),(0,[z1,z231,z26,z3,z5,z6]),(0,[z1,z2,z298,z34,z5,z6]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z1,z155,z26,z3,z32,z6]),(0,[z232,z2,z26,z3,z5,z6]),(0,[z1,z2,z34,z94,z125,z6]),(0,[z1,z2,z3,z4,z5,z801]),(0,[z1,z2,z118,z103,z5,z6])],[(0,[z380,z1,z131,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1126]),(0,[z1,z2,z34,z5,z409,z6]),(0,[z1,z2,z26,z401,z5,z6]),(0,[z597,z2,z3,z4,z50,z6]),(0,[z1,z1111,z3,z34,z5,z6])],[(0,[z2,z3,z4,z731,z50,z6]),(0,[z43,z1,z208,z2,z3,z4]),(0,[z1,z2,z520,z3,z5,z206])],[(0,[z1,z2,z4,z1127,z5,z6]),(0,[z240,z2,z26,z3,z5,z177]),(0,[z71,z1,z2,z4,z5,z6]),(0,[z110,z1,z2,z238,z5,z6]),(0,[z1,z2,z26,z3,z875,z6]),(0,[z1,z2,z1128,z3,z5,z6]),(0,[z1,z2,z74,z3,z46,z6]),(0,[z1129,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z1130,z5,z6]),(0,[z1,z2,z1131,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1132]),(0,[z1,z2,z1133,z3,z5,z6]),(0,[z1,z2,z3,z117,z5,z270]),(0,[z1,z2,z3,z4,z5,z761])],[(0,[z12,z2,z27,z4,z5,z6]),(1,[z1,z2,z34,z159,z6])],[(0,[z25,z127,z26,z3,z5,z6]),(0,[z1,z319,z3,z4,z5,z342]),(0,[z1,z2,z642,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z844,z131,z4,z5,z6]),(0,[z1,z2,z26,z156,z5,z9])],[(0,[z1,z2,z3,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z687,z3,z4,z5,z101])],[(0,[z1,z2,z3,z1136,z5,z6]),(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z83,z3,z740,z5,z6]),(0,[z1,z89,z2,z14,z4,z5])],[(0,[z1,z2,z14,z5,z6,z52])],[(0,[z1,z319,z3,z4,z13,z6]),(0,[z167,z3,z131,z4,z5,z6]),(0,[z167,z2,z3,z238,z5,z6]),(0,[z1,z120,z2,z34,z5,z6]),(0,[z110,z1,z2,z4,z5,z321]),(0,[z110,z1,z2,z26,z5,z6]),(0,[z1,z2,z118,z34,z5,z6]),(0,[z1137,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z966])]],
   [[(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z2,z235,z34,z5,z6]),(0,[z1,z2,z635,z34,z5,z6])],[(1,[z67,z3,z4,z5,z268]),(0,[z142,z127,z3,z4,z5,z6]),(0,[z1,z337,z3,z4,z5,z338]),(0,[z1139,z2,z3,z4,z5,z6]),(0,[z1140,z2,z3,z4,z5,z6])],[(0,[z25,z517,z3,z4,z5,z6]),(0,[z12,z2,z27,z34,z5,z6]),(0,[z167,z120,z3,z4,z5,z6]),(0,[z1,z107,z844,z4,z5,z6]),(0,[z1,z2,z45,z3,z34,z5])],[(0,[z1,z2,z3,z122,z271,z6]),(0,[z1,z2,z3,z1141,z5,z6]),(0,[z1,z2,z490,z4,z5,z9])],[(0,[z1,z2,z3,z4,z5,z1142]),(0,[z1,z2,z3,z4,z5,z1143]),(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z2,z26,z3,z271,z6]),(0,[z1,z2,z3,z34,z5,z95]),(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z22,z3,z5,z277])],[(0,[z1,z129,z3,z4,z5,z6]),(0,[z166,z1,z26,z131,z5,z6]),(0,[z1,z3,z4,z5,z730,z6]),(0,[z1,z2,z34,z5,z281,z6]),(0,[z1,z2,z26,z144,z93,z6]),(0,[z1,z2,z3,z4,z55,z6]),(0,[z1,z2,z4,z93,z708,z6])],[(0,[z1,z120,z67,z34,z5,z6]),(0,[z1,z2,z3,z1146,z5,z6]),(0,[z1,z1147,z3,z4,z5,z6]),(0,[z1,z2,z220,z34,z5,z6]),(0,[z1,z2,z3,z4,z1068,z6]),(0,[z353,z2,z3,z4,z5,z41]),(0,[z1,z89,z140,z2,z3,z4]),(0,[z1,z2,z3,z4,z1148,z6])],[(0,[z1,z2,z3,z1149,z5,z6]),(0,[z1,z2,z3,z4,z13,z342]),(0,[z28,z246,z3,z37,z5,z6]),(0,[z1,z2,z3,z1150,z5,z6]),(0,[z167,z2,z3,z4,z5,z321]),(0,[z1,z2,z315,z4,z93,z6]),(0,[z1,z2,z3,z1151,z5,z6]),(0,[z1,z2,z34,z5,z286,z6]),(0,[z110,z1,z2,z812,z5,z6]),(0,[z1,z2,z3,z63,z159,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 518) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1040).take 193) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1233)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 518, 193] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 92).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 92).take 85).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 177).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [92, 85, 79] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_46258

theorem PEqualNP.Outside.L_meta_46258 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277067904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277067904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46258.solve