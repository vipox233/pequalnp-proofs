import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38383

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
  Nat.testBit (4008372896 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00001b056c2e1c2a#64 ++ 0x00000d82b6170e15#64 ++ 0xbc847f1ffcfe3c7f#64 ++ 0xde423f8ffe7f1e3f#64 : BitVec 256),
   (0x1239b86ce166c598#64 ++ 0x091cdc3670b362cc#64 ++ 0xff7bb8ece367c799#64 ++ 0x7fbddc7671b3e3cc#64 : BitVec 256),
   (0x4582c0b0b6836ee0#64 ++ 0x22c160585b41b770#64 ++ 0xdd83c0f0ff87ffe0#64 ++ 0x6ec1e0787fc3fff0#64 : BitVec 256),
   (0x21dc00da03d00354#64 ++ 0x10ee006d01e801aa#64 ++ 0xf7fc00ff03f807ff#64 ++ 0xfbfe007f81fc03ff#64 : BitVec 256),
   (0x89ef6d0003fdb000#64 ++ 0x44f7b68001fed800#64 ++ 0xfbffff0003fff800#64 ++ 0x7dffff8001fffc00#64 : BitVec 256),
   (0x0ff7f6ffd8000000#64 ++ 0x87fbfb7fec000000#64 ++ 0xeffffffffc000000#64 ++ 0x77fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z1 : W := mkw 0x01d400da00000000 0x00ea006d00000000 0xe7fc00ff00000000 0x73fe007f80000000

def z2 : W := mkw 0x0e23f625d8000000 0x8711fb12ec000000 0x0803ff00fc000000 0x0401ff807e000000

def z3 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z4 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z5 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z6 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xfbffff0003fff800 0x7dffff8001fffc00

def z7 : W := mkw 0x2ff7f6ffda900244 0x97fbfb7fed480122 0xeffffffffc980066 0xf7fffffffe4c0033

def z8 : W := mkw 0x00008020a0024480 0x0000401050012240 0xdd0380e0e307c780 0x6e81c0707183e3c0

def z9 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xeffffffffc000000 0x77fffffffe000000

def z10 : W := mkw 0x0000120548000000 0x00000902a4000000 0xac847f1ffc000000 0x56423f8ffe000000

def z11 : W := mkw 0x061080fa90000000 0x8308407d48000000 0x000000e000000000 0x0000007000000000

def z12 : W := mkw 0x0000000020020400 0x0000000010010200 0x9c000000e0060400 0x4e00000070030200

def z13 : W := mkw 0x12393b4d496c911a 0x091c9da6a4b6488d 0x227c3f0f0078001f 0x913e1f87803c000f

def z14 : W := mkw 0x0e23ff25fc2e1c2a 0x8711ff92fe170e15 0xbc87ff1ffcfe3c7f 0xde43ff8ffe7f1e3f

def z15 : W := mkw 0x1210906ce0024598 0x09084836700122cc 0x040000ece0000799 0x02000076700003cc

def z16 : W := mkw 0x9bfffd6ce3fff598 0x4dfffeb671fffacc 0xffffffece3ffff99 0x7ffffff671ffffcc

def z17 : W := mkw 0x205c004a01500114 0x102e002500a8008a 0x227c000f0078001f 0x913e0007803c000f

def z18 : W := mkw 0x4402c020b4036ca0 0x220160105a01b650 0x0803c000fc07f800 0x0401e0007e03fc00

def z19 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xffffffffffffffff 0xffffffffffffffff

def z20 : W := mkw 0x33fdbbffeffedffe 0x19feddfff7ff6fff 0xffffffffffffffff 0xffffffffffffffff

def z21 : W := mkw 0x100808002166c598 0x0804040010b362cc 0x100000000367c799 0x0800000001b3e3cc

def z22 : W := mkw 0x3239b86ce3f6c7dc 0x191cdc3671fb63ee 0xff7bb8ece3ffc7ff 0xffbddc7671ffe3ff

def z23 : W := mkw 0x4582c9b0b6af7ee0 0x22c164d85b57bf70 0xfd87fff0ffffffe0 0x7ec3fff87ffffff0

def z24 : W := mkw 0x882b6d0003fdb000 0x4415b68001fed800 0x1803ff0003fff800 0x0c01ff8001fffc00

def z25 : W := mkw 0x0231b06ce0024480 0x0118d83670012240 0xff7bb8ece307c780 0x7fbddc767183e3c0

def z26 : W := mkw 0x0180000002800000 0x00c0000001400000 0xd180000003800000 0x68c0000001c00000

def z27 : W := mkw 0x0ff7fffffc2e1c2a 0x87fbfffffe170e15 0xfffffffffcfe3c7f 0xfffffffffe7f1e3f

def z28 : W := mkw 0x2ffff6ffdbd00354 0x97fffb7fede801aa 0xfffffffffff807ff 0xfffffffffffc03ff

def z29 : W := mkw 0x00292900016c9000 0x0014948000b64800 0xfbffff0003fff800 0x7dffff8001fffc00

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0xb484001f00f8047f 0xda42000f807c023f

def z31 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0x437b80e00301c380 0x21bdc0700180e1c0

def z32 : W := mkw 0x1221b824e026c488 0x0910dc1270136244 0x0803b800e007c000 0x0401dc007003e000

def z33 : W := mkw 0x89ef7f056fffbc2a 0x44f7bf82b7ffde15 0xfbffff00fffff800 0x7dffff807ffffc00

def z34 : W := mkw 0x0000000024020c20 0x0000000012010610 0x9c804010fc863c60 0x4e4020087e431e30

def z35 : W := mkw 0x1239b86ce566cdb8 0x091cdc3672b366dc 0xfffbf8fcffe7fff9 0x7ffdfc7e7ff3fffc

def z36 : W := mkw 0x00001b05482c100a 0x00000d82a4160805 0x20043f0f0078001f 0x90021f87803c000f

def z37 : W := mkw 0x4582c0b0928162c0 0x22c160584940b160 0x410380e00301c380 0x2081c0700180e1c0

def z38 : W := mkw 0xcffffffffffffee0 0xe7ffffffffffff70 0xffffffffffffffe0 0x7ffffffffffffff0

def z39 : W := mkw 0x102928002166c598 0x0814940010b362cc 0xfb7bb8000367c799 0x7dbddc0001b3e3cc

def z40 : W := mkw 0x0000100460020408 0x0000080230010204 0x0400000ce0000419 0x020000067000020c

def z41 : W := mkw 0x89ef650003d9b000 0x44f7b28001ecd800 0x43ffc7000399f800 0x21ffe38001ccfc00

def z42 : W := mkw 0x0231b06cc0000000 0x0118d83660000000 0xef7bb8ece0000000 0x77bddc7670000000

def z43 : W := mkw 0x0de7669318000000 0x86f3b3498c000000 0xebffff131c000000 0x75ffff898e000000

def z44 : W := mkw 0x0fe7f625d8000000 0x87f3fb12ec000000 0xebffff00fc000000 0x75ffff807e000000

def z45 : W := mkw 0x201000da00000354 0x1008006d000001aa 0x040000ff000007ff 0x8200007f800003ff

def z46 : W := mkw 0x886d2d00017c9000 0x4436968000be4800 0x227c3f0000780000 0x113e1f80003c0000

def z47 : W := mkw 0xcdefedb0b7fffee0 0x66f7f6d85bffff70 0xfffffff0ffffffe0 0x7ffffff87ffffff0

def z48 : W := mkw 0x000003010c081822 0x0000018086040c11 0x008447131c983866 0x804223898e4c1c33

def z49 : W := mkw 0x1210926dec024dba 0x09084936f60126dd 0x040000fffc0007ff 0x8200007ffe0003ff

def z50 : W := mkw 0x21dc1bdf6ffe1f7e 0x10ee0defb7ff0fbf 0xfffc7ffffffe3fff 0xfffe3fffffff1fff

def z51 : W := mkw 0x4792d2fffe836ee0 0xa3c9697fff41b770 0xdd83c0ffff87ffe0 0x6ec1e07fffc3fff0

def z52 : W := mkw 0x019800d803c00350 0x00cc006c01e001a8 0xf7f800fc03e007f9 0x7bfc007e01f003fc

def z53 : W := mkw 0x0039284801648110 0x001c942400b24088 0xff7bb8ec0367c799 0x7fbddc7601b3e3cc

def z54 : W := mkw 0x1239b96ce56eddba 0x091cdcb672b76edd 0xff7bb8ece3ffffff 0xffbddc7671ffffff

def z55 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x18007f00fcfe3c7f 0x8c003f807e7f1e3f

def z56 : W := mkw 0x4402c0b0b4036ee0 0x220160585a01b770 0x0c03c0f0fc07ffe0 0x0601e0787e03fff0

def z57 : W := mkw 0x0210124f48000000 0x81080927a4000000 0x0000000f00000000 0x0000000780000000

def z58 : W := mkw 0x09e7640000000000 0x04f3b20000000000 0xebffff0000000000 0x75ffff8000000000

def z59 : W := mkw 0x440080b0b4024ee0 0x220040585a012770 0x040000f0fc0007e0 0x020000787e0003f0

def z60 : W := mkw 0x0029280001648000 0x0014940000b24000 0xfb7bb8000367c000 0x7dbddc0001b3e000

def z61 : W := mkw 0xc9ef6d0027fffee0 0x64f7b68013ffff70 0xfbffff0003ffffe0 0x7dffff8001fffff0

def z62 : W := mkw 0x8fffffffdbfdb000 0xc7ffffffedfed800 0xfffffffffffff800 0x7ffffffffffffc00

def z63 : W := mkw 0x0182400002812000 0x00c1200001409000 0xd983c0000387f800 0x6cc1e00001c3fc00

def z64 : W := mkw 0x4582c0b0928162c0 0x22c160584940b160 0xd58380f00381c7e0 0x6ac1c07801c0e3f0

def z65 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x08007f00fc063800 0x04003f807e031c00

def z66 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x437800e003000380 0x21bc0070018001c0

def z67 : W := mkw 0x2dde46db1bd00354 0x96ef236d8de801aa 0xf7fc47ff1ff807ff 0xfbfe23ff8ffc03ff

def z68 : W := mkw 0x0002400000012000 0x0001200000009000 0x0803c0000007f800 0x0401e0000003fc00

def z69 : W := mkw 0x1229b824e166c488 0x0914dc1270b36244 0xfb7bb800e367c000 0x7dbddc0071b3e000

def z70 : W := mkw 0x0018004801400110 0x000c002400a00088 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z71 : W := mkw 0x4582dbb5feaf7eea 0x22c16ddaff57bf75 0xfd87ffffffffffff 0xfec3ffffffffffff

def z72 : W := mkw 0x88236d00002db000 0x4411b6800016d800 0x0803ff000007f800 0x0401ff800003fc00

def z73 : W := mkw 0xa9ff6dda03fdb354 0x54ffb6ed01fed9aa 0xffffffff03ffffff 0xffffffff81ffffff

def z74 : W := mkw 0x4ff7f6fffe836ee0 0xa7fbfb7fff41b770 0xffffffffff87ffe0 0x7fffffffffc3fff0

def z75 : W := mkw 0x89c6450002993000 0x44e32280014c9800 0x0084470000983800 0x00422380004c1c00

def z76 : W := mkw 0x061092ffd8000000 0x8308497fec000000 0x040000fffc000000 0x0200007ffe000000

def z77 : W := mkw 0x0231b86ce0260408 0x0118dc3670130204 0xff7bb8ece0660419 0x7fbddc767033020c

def z78 : W := mkw 0x20081b056ffe1f7e 0x10040d82b7ff0fbf 0xbc847f1ffffe3fff 0xde423f8fffff1fff

def z79 : W := mkw 0x0582c0b092812000 0x02c1605849409000 0xdd83c0f0ff87f800 0x6ec1e0787fc3fc00

def z80 : W := mkw 0x0018004801400110 0x000c002400a00088 0xf77800ec03600799 0x7bbc007601b003cc

def z81 : W := mkw 0x3008080023f6c7dc 0x1804040011fb63ee 0x1000000003ffc7ff 0x8800000001ffe3ff

def z82 : W := mkw 0x0fa3f6b5d8000000 0x87d1fb5aec000000 0xcd83fff0fc000000 0x66c1fff87e000000

def z83 : W := mkw 0x13fdb86ce3f6c598 0x09fedc3671fb62cc 0xffffb8ece3ffc799 0x7fffdc7671ffe3cc

def z84 : W := mkw 0x01d400da00000000 0x00ea006d00000000 0xf7fc00ff00f8047f 0xfbfe007f807c023f

def z85 : W := mkw 0x21c4009202900244 0x10e2004901480122 0x0084001300980066 0x80420009804c0033

def z86 : W := mkw 0x45abe8b0b7e7eee0 0x22d5f4585bf3f770 0xfffbf8f0ffe7ffe0 0x7ffdfc787ff3fff0

def z87 : W := mkw 0x01d400da02800240 0x00ea006d01400120 0xf7fc00ff038007e0 0x7bfe007f81c003f0

def z88 : W := mkw 0x1ff7fefff826c488 0x8ffbff7ffc136244 0xeffffffffc07c000 0x77fffffffe03e000

def z89 : W := mkw 0x4582409016812a60 0x22c120480b409530 0x008040101c803860 0x004020080e401c30

def z90 : W := mkw 0x57bbf8fcf7e7eff8 0x2bddfc7e7bf3f7fc 0xfffbf8fcffe7fff9 0x7ffdfc7e7ff3fffc

def z91 : W := mkw 0x2ff7f6ffd8000354 0x97fbfb7fec0001aa 0xeffffffffc0007ff 0xf7fffffffe0003ff

def z92 : W := mkw 0x80081b056fffbc2a 0x40040d82b7ffde15 0xbc847f1ffffffc7f 0xde423f8ffffffe3f

def z93 : W := mkw 0x2008090027fe1f7e 0x1004048013ff0fbf 0x1000000003fe3fff 0x8800000001ff1fff

def z94 : W := mkw 0x440080b0900042c0 0x2200405848002160 0x000000e000000380 0x00000070000001c0

def z95 : W := mkw 0x00000900002c1000 0x0000048000160800 0xb8847f0000fe3800 0x5c423f80007f1c00

def z96 : W := mkw 0x2008000003d00354 0x1004000001e801aa 0x1000000003f807ff 0x8800000001fc03ff

def z97 : W := mkw 0x8802450000093000 0x4401228000049800 0x0000470000003800 0x0000238000001c00

def z98 : W := mkw 0x1239384c41648118 0x091c9c2620b2408c 0x2278380c00600019 0x113c1c060030000c

def z99 : W := mkw 0x01cc000003d00000 0x00e6000001e80000 0xf3fc000003f80000 0x79fe000001fc0000

def z100 : W := mkw 0x0ff7e4fa90000000 0x87fbf27d48000000 0x437b80e000000000 0x21bdc07000000000

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0xb400000c00600419 0x5a0000060030020c

def z102 : W := mkw 0x0a75364f48000000 0x853a9b27a4000000 0xaefc7f1ffc000000 0x577e3f8ffe000000

def z103 : W := mkw 0x0a75364f48000000 0x853a9b27a4000000 0x227c3f0f00000000 0x113e1f8780000000

def z104 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7bffecff67ff99 0x7fbdfff67fb3ffcc

def z105 : W := mkw 0x0180009002800240 0x00c0004801400120 0xf58400ff03f807ff 0xfac2007f81fc03ff

def z106 : W := mkw 0x89ef640003d1a000 0x44f7b20001e8d000 0x437b80000301c000 0x21bdc0000180e000

def z107 : W := mkw 0x1229b824e166c598 0x0914dc1270b362cc 0x1803b800e367c799 0x0c01dc0071b3e3cc

def z108 : W := mkw 0x23fdb0fec3d00354 0x11fed87f61e801aa 0xffffb8ffe3f807ff 0xffffdc7ff1fc03ff

def z109 : W := mkw 0x0c02460118000000 0x860123008c000000 0x000047001c000000 0x000023800e000000

def z110 : W := mkw 0x0ff7f6fff8024480 0x87fbfb7ffc012240 0xffffffffff07c780 0x7fffffffff83e3c0

def z111 : W := mkw 0x21c4009202900244 0x10e2004901480122 0xd58400f3039807e6 0xeac2007981cc03f3

def z112 : W := mkw 0x00008020a4024ca0 0x0000401052012650 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z113 : W := mkw 0xa9ff7fdf6fffbf7e 0x54ffbfefb7ffdfbf 0xffffffffffffffff 0xffffffffffffffff

def z114 : W := mkw 0x00001904642e1c2a 0x00000c8232170e15 0xbc00380ce0fe3c7f 0xde001c06707f1e3f

def z115 : W := mkw 0x0ff7f6ffda812000 0x87fbfb7fed409000 0xffffffffff87f800 0x7fffffffffc3fc00

def z116 : W := mkw 0x00000900242e1c2a 0x0000048012170e15 0x1000000000fe3c7f 0x88000000007f1e3f

def z117 : W := mkw 0x882364000001a000 0x4411b2000000d000 0x000380000001c000 0x0001c0000000e000

def z118 : W := mkw 0x0000000024020c20 0x0000000012010610 0x04000010fc000460 0x020000087e000230

def z119 : W := mkw 0x4582c0b096812a60 0x22c160584b409530 0xcd83c0f0fc803860 0x66c1e0787e401c30

def z120 : W := mkw 0x4de7e4b0b6836ee0 0x26f3f2585b41b770 0xfffffff0ff87ffe0 0x7ffffff87fc3fff0

def z121 : W := mkw 0x89e76d0002bdb000 0x44f3b680015ed800 0x0887ff00009ff800 0x0443ff80004ffc00

def z122 : W := mkw 0x0e33f66dd8000000 0x8719fb36ec000000 0xef7bffecfc000000 0x77bdfff67e000000

def z123 : W := mkw 0x65c6c0b2b6936ee4 0x32e360595b49b772 0xdd87c0f3ff9fffe6 0xeec3e079ffcffff3

def z124 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xb8847f00fcfe3800 0x5c423f807e7f1c00

def z125 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x267838ece0600799 0x133c1c76703003cc

def z126 : W := mkw 0x0000120548000000 0x00000902a4000000 0x0400001ffc000000 0x0200000ffe000000

def z127 : W := mkw 0x1221a0208000c080 0x0910d01040006040 0x000380000001c000 0x0001c0000000e000

def z128 : W := mkw 0x01c4009200000000 0x00e2004900000000 0x0084001300000000 0x0042000980000000

def z129 : W := mkw 0x4000000026836ee0 0x200000001341b770 0x100000000387ffe0 0x0800000001c3fff0

def z130 : W := mkw 0x0231b26dc8000000 0x0118d936e4000000 0xeffffffffc000000 0x77fffffffe000000

def z131 : W := mkw 0x5639b8fcf566cff8 0x2b1cdc7e7ab367fc 0xff7bb8fcff67c7f9 0x7fbddc7e7fb3e3fc

def z132 : W := mkw 0x1239b06cc140c190 0x091cd83660a060c8 0xef7bb8ece301c380 0x77bddc767180e1c0

def z133 : W := mkw 0x0582c0b090000000 0x02c1605848000000 0x410380e000000000 0x2081c07000000000

def z134 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x43fc00f3039803e6 0xa1fe007981cc01f3

def z135 : W := mkw 0x10080900256eddba 0x0804048012b76edd 0x1000000003ffffff 0x8800000001ffffff

def z136 : W := mkw 0x1239b06ce142c598 0x091cd83670a162cc 0x477b80ece301c799 0x23bdc0767180e3cc

def z137 : W := mkw 0x1ffffefff966c598 0x8fffff7ffcb362cc 0xffffffffff67c799 0x7fffffffffb3e3cc

def z138 : W := mkw 0x89ff6d4803fdb110 0x44ffb6a401fed888 0xffffffec03ffff99 0x7ffffff601ffffcc

def z139 : W := mkw 0x03f5b0fec0000000 0x01fad87f60000000 0xefffb8ffe0000000 0x77ffdc7ff0000000

def z140 : W := mkw 0x4582409036832e60 0x22c120481b419730 0x9c804010fc863c60 0x4e4020087e431e30

def z141 : W := mkw 0x0582c0b090000000 0x02c1605848000000 0xcd83c0f0fc000000 0x66c1e0787e000000

def z142 : W := mkw 0x9a7d3d4c417c9118 0x4d3e9ea620be488c 0x227c3f0c00780019 0x113e1f86003c000c

def z143 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x2a7bb80ce067c019 0x153ddc067033e00c

def z144 : W := mkw 0xa1dc09da03fdb354 0x50ee04ed01fed9aa 0xf7fc00ff03ffffff 0xfbfe007f81ffffff

def z145 : W := mkw 0x1221b824e026c488 0x0910dc1270136244 0xdd03b8e0e307c780 0x6e81dc707183e3c0

def z146 : W := mkw 0x000012056c020c2a 0x00000902b6010615 0x0400001ffc00047f 0x8200000ffe00023f

def z147 : W := mkw 0x1239a8688164c190 0x091cd43440b260c8 0xfb7bb8e00367c380 0x7dbddc7001b3e1c0

def z148 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x22fc7f0000f83800 0x117e3f80007c1c00

def z149 : W := mkw 0xa9de45da03d93354 0x54ef22ed01ec99aa 0xf7fc47ff03f83fff 0xfbfe23ff81fc1fff

def z150 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x537b800003fff800 0x29bdc00001fffc00

def z151 : W := mkw 0x8008090003fdb000 0x4004048001fed800 0x1000000003fff800 0x0800000001fffc00

def z152 : W := mkw 0x0ffffeffd9648000 0x87ffff7fecb24000 0xffffffffff67c000 0x7fffffffffb3e000

def z153 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x4b7bff000307f800 0x25bdff800183fc00

def z154 : W := mkw 0x0008000001400000 0x0004000000a00000 0xf378000003600000 0x79bc000001b00000

def z155 : W := mkw 0x89ef7f056fffbc2a 0x44f7bf82b7ffde15 0xffffff1ffffffc7f 0xffffff8ffffffe3f

def z156 : W := mkw 0x89ef6d9003fdb240 0x44f7b6c801fed920 0xfffffff003ffffe0 0x7ffffff801fffff0

def z157 : W := mkw 0x21c4009202900244 0x10e2004901480122 0xb484001f00f8047f 0xda42000f807c023f

def z158 : W := mkw 0x1210806880004190 0x09084034400020c8 0x000000e000000380 0x00000070000001c0

def z159 : W := mkw 0x21dc00da27d20f74 0x10ee006d13e907ba 0xfffc40fffffe3fff 0xfffe207fffff1fff

def z160 : W := mkw 0x0010004800000000 0x0008002400000000 0xe77800ec00000000 0x73bc007600000000

def z161 : W := mkw 0x00008020a0024480 0x0000401050012240 0x040000e0e0000780 0x02000070700003c0

def z162 : W := mkw 0x13b9b8fce3e6c7d8 0x09dcdc7e71f363ec 0xfffbb8fce3e7c7f9 0x7ffddc7e71f3e3fc

def z163 : W := mkw 0x0180009002800240 0x00c0004801400120 0xd58000f0038007e0 0x6ac0007801c003f0

def z164 : W := mkw 0x09e7640002812000 0x04f3b20001409000 0xfbffff000387f800 0x7dffff8001c3fc00

def z165 : W := mkw 0x882b6d00016db000 0x4415b68000b6d800 0xfb7bff000367f800 0x7dbdff8001b3fc00

def z166 : W := mkw 0xc008090027fffee0 0x6004048013ffff70 0x1000000003ffffe0 0x0800000001fffff0

def z167 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x537800e003f807ff 0xa9bc007001fc03ff

def z168 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xf77b80ec0361c799 0x7bbdc07601b0e3cc

def z169 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x4b7bffe0fc000000 0x25bdfff07e000000

def z170 : W := mkw 0x000013054c081822 0x00000982a6040c11 0xac847f1ffc983866 0xd6423f8ffe4c1c33

def z171 : W := mkw 0x81cc090003fdb000 0x40e6048001fed800 0xf3fc000003fff800 0x79fe000001fffc00

def z172 : W := mkw 0x3239b8fee166c7dc 0x191cdc7f70b363ee 0xff7bb8ffe367c7ff 0xffbddc7ff1b3e3ff

def z173 : W := mkw 0x0000080020260408 0x0000040010130204 0x1000000000660419 0x080000000033020c

def z174 : W := mkw 0x0582c0b092800240 0x02c1605849400120 0xdd83c0f0ff8007e0 0x6ec1e0787fc003f0

def z175 : W := mkw 0x0de7e4b090000000 0x06f3f25848000000 0xeffffff0fc000000 0x77fffff87e000000

def z176 : W := mkw 0x89ef7f054bfdb000 0x44f7bf82a5fed800 0xffffff1ffffff800 0x7fffff8ffffffc00

def z177 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xfd87c0ffffffffff 0xfec3e07fffffffff

def z178 : W := mkw 0x0ff7ffffd82c100a 0x87fbffffec160805 0xeffffffffc78001f 0xf7fffffffe3c000f

def z179 : W := mkw 0x0a75244a00000000 0x853a922500000000 0x0278000000000000 0x013c000000000000

def z180 : W := mkw 0x89ef7d0463ffb408 0x44f7be8231ffda04 0xffffff0ce3fffc19 0x7fffff8671fffe0c

def z181 : W := mkw 0x89ef6d00017c9000 0x44f7b68000be4800 0xebffff0000780000 0x75ffff80003c0000

def z182 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xe7fc00ff03000380 0x73fe007f818001c0

def z183 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xfffffffffcf8047f 0xfffffffffe7c023f

def z184 : W := mkw 0x0210906cc0000000 0x0108483660000000 0x040000ece0000000 0x0200007670000000

def z185 : W := mkw 0x4dc646931e812a60 0xa6e323498f409530 0x008447131c803860 0x004223898e401c30

def z186 : W := mkw 0x9ffffffffbfff598 0xcffffffffdfffacc 0xffffffffffffff99 0x7fffffffffffffcc

def z187 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xf3fc00e003f80380 0x79fe007001fc01c0

def z188 : W := mkw 0x1231b86ce026c598 0x0918dc36701362cc 0x0c03b8ece007c799 0x0601dc767003e3cc

def z189 : W := mkw 0x4582c0b096816ae0 0x22c160584b40b570 0x4183c0f01f81fbe0 0x20c1e0780fc0fdf0

def z190 : W := mkw 0x01d412df48000000 0x00ea096fa4000000 0xeffc7ffffc000000 0x77fe3ffffe000000

def z191 : W := mkw 0x0182400002812000 0x00c1200001409000 0x0080400000803800 0x0040200000401c00

def z192 : W := mkw 0x1221bb25ec2edcaa 0x0910dd92f6176e55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z193 : W := mkw 0x00293b056d6e9c2a 0x00149d82b6b74e15 0xffffff1ffffffc7f 0xffffff8ffffffe3f

def z194 : W := mkw 0x886f6d00017db000 0x4437b68000bed800 0x2a7fff00007ff800 0x153fff80003ffc00

def z195 : W := mkw 0x4ff7f6ffda8162c0 0xa7fbfb7fed40b160 0xefffffffff01c380 0x77ffffffff80e1c0

def z196 : W := mkw 0x886d2d00017c9000 0x4436968000be4800 0xbafc7f0000fe3800 0x5d7e3f80007f1c00

def z197 : W := mkw 0x88237f056c2fbc2a 0x4411bf82b617de15 0x0803ff00fc07f800 0x0401ff807e03fc00

def z198 : W := mkw 0x99ef6d0023fff598 0x4cf7b68011fffacc 0xfbffff0003ffff99 0x7dffff8001ffffcc

def z199 : W := mkw 0x01ed280003f48000 0x00f6940001fa4000 0xfbffb80003ffc000 0x7dffdc0001ffe000

def z200 : W := mkw 0x4000000026836ee0 0x200000001341b770 0x9c804010ff87ffe0 0x4e4020087fc3fff0

def z201 : W := mkw 0x0ff7fffffc2e1c2a 0x87fbfffffe170e15 0xeffffffffc063800 0x77fffffffe031c00

def z202 : W := mkw 0x1239384c61668518 0x091c9c2630b3428c 0xbe78380ce0660419 0x5f3c1c067033020c

def z203 : W := mkw 0x0dc65f977c2e1c2a 0x86e32fcbbe170e15 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z204 : W := mkw 0x89c64d0002bd3000 0x44e32680015e9800 0xb8847f0000fe3800 0x5c423f80007f1c00

def z205 : W := mkw 0x0231304c40000000 0x0118982620000000 0x2278380c00000000 0x113c1c0600000000

def z206 : W := mkw 0x0dc6469318000000 0x86e323498c000000 0x008447131c000000 0x004223898e000000

def z207 : W := mkw 0x06009225d8000000 0x83004912ec000000 0x00000000fc000000 0x000000007e000000

def z208 : W := mkw 0x10088820a166c598 0x0804441050b362cc 0xdd0380e0e367c799 0x6e81c07071b3e3cc

def z209 : W := mkw 0x00000900242e1c2a 0x0000048012170e15 0xb8847f0000fe3c7f 0xdc423f80007f1e3f

def z210 : W := mkw 0xcdef6d9017fdba60 0x66f7b6c80bfedd30 0xfbffff101ffff860 0x7dffff880ffffc30

def z211 : W := mkw 0x4402db25fc2f7caa 0x22016d92fe17be55 0xbc87ff1ffcfffc7f 0xde43ff8ffe7ffe3f

def z212 : W := mkw 0x0000000000000000 0x0000000000000000 0x0400001f0000047f 0x8200000f8000023f

def z213 : W := mkw 0x00001b05482c100a 0x00000d82a4160805 0xb8847f0f00fe381f 0xdc423f87807f1c0f

def z214 : W := mkw 0x0000020108000000 0x0000010084000000 0x008447131c000000 0x004223898e000000

def z215 : W := mkw 0x1239b86cc164c198 0x091cdc3660b260cc 0x637bb8ec0361c399 0x31bddc7601b0e1cc

def z216 : W := mkw 0x1e23fe25f826c488 0x8f11ff12fc136244 0x0803ff00fc07c000 0x0401ff807e03e000

def z217 : W := mkw 0x4e23f625fc036ca0 0xa711fb12fe01b650 0x0803ff00fc07f800 0x0401ff807e03fc00

def z218 : W := mkw 0x01801b956eae1e6a 0x00c00dcab7570f35 0xfd847ffffffe3fff 0xfec23fffffff1fff

def z219 : W := mkw 0x65dc80fab7d24ff4 0x32ee407d5be927fa 0xf7fc00fffff807ff 0xfbfe007ffffc03ff

def z220 : W := mkw 0x21c403930e981a66 0x10e201c9874c0d33 0x008447131c983866 0x804223898e4c1c33

def z221 : W := mkw 0x205c004a01500114 0x102e002500a8008a 0xb6fc001f00f8047f 0xdb7e000f807c023f

def z222 : W := mkw 0x0402c02090000000 0x0201601048000000 0x0803c000fc000000 0x0401e0007e000000

def z223 : W := mkw 0x1239b86cc1648118 0x091cdc3660b2408c 0xef7bb8ece0600019 0x77bddc767030000c

def z224 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x08847f13fc9e3866 0x84423f89fe4f1c33

def z225 : W := mkw 0x8844050000181000 0x44220280000c0800 0x0004070000180000 0x00020380000c0000

def z226 : W := mkw 0x886d3f056d7e9c2a 0x44369f82b6bf4e15 0xbefc7f1ffcfe3c7f 0xdf7e3f8ffe7f1e3f

def z227 : W := mkw 0x205c004a01500114 0x102e002500a8008a 0x0278000000000000 0x013c000000000000

def z228 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x637fbfef00000000 0x31bfdff780000000

def z229 : W := mkw 0x100008002026c488 0x0800040010136244 0x000000000007c000 0x000000000003e000

def z230 : W := mkw 0x8bff7f4f4bfdb000 0xc5ffbfa7a5fed800 0xfbffff0f03fff800 0x7dffff8781fffc00

def z231 : W := mkw 0x4582c020b6836ca0 0x22c160105b41b650 0xd983c000ff87f800 0x6cc1e0007fc3fc00

def z232 : W := mkw 0x1239ba6de966c598 0x091cdd36f4b362cc 0xffffffffff67c799 0x7fffffffffb3e3cc

def z233 : W := mkw 0x4582dbb5feaf7eea 0x22c16ddaff57bf75 0xdd83fff0ff87ffe0 0x6ec1fff87fc3fff0

def z234 : W := mkw 0x65dec0fab7d36ff4 0x32ef607d5be9b7fa 0xffffc0ffffffffff 0xffffe07fffffffff

def z235 : W := mkw 0x0182400002812000 0x00c1200001409000 0x410380000301c000 0x2081c0000180e000

def z236 : W := mkw 0x33fdb8fee3f6c7dc 0x19fedc7f71fb63ee 0xffffb8ffe3ffc7ff 0xffffdc7ff1ffe3ff

def z237 : W := mkw 0x4402c02090016080 0x220160104800b040 0x000380000001c000 0x0001c0000000e000

def z238 : W := mkw 0x0029380461668408 0x00149c0230b34204 0xff7bb80ce367c419 0x7fbddc0671b3e20c

def z239 : W := mkw 0x01cc009003d00240 0x00e6004801e80120 0xf7fc00f003f807e0 0x7bfe007801fc03f0

def z240 : W := mkw 0x0e75b6ffd8000000 0x873adb7fec000000 0x267c3ffffc000000 0x133e1ffffe000000

def z241 : W := mkw 0x0582c0b0b4020c20 0x02c160585a010610 0xdd83c0f0fc863c60 0x6ec1e0787e431e30

def z242 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x637c00ef0378039f 0xb1be007781bc01cf

def z243 : W := mkw 0x0182490002ad3000 0x00c1248001569800 0xf987ff0003fff800 0x7cc3ff8001fffc00

def z244 : W := mkw 0x5ffffeffffe7eff8 0xafffff7ffff3f7fc 0xffffffffffe7fff9 0x7ffffffffff3fffc

def z245 : W := mkw 0x101808482166c598 0x080c042410b362cc 0xf77800ec0367c799 0x7bbc007601b3e3cc

def z246 : W := mkw 0x2044000200100004 0x1022000100080002 0x0004000300180006 0x80020001800c0003

def z247 : W := mkw 0x00009b25ec2e5caa 0x00004d92f6172e55 0xfd87ffffffffffff 0xfec3ffffffffffff

def z248 : W := mkw 0x57bbfbfdffeffffa 0x2bddfdfefff7fffd 0xffffffffffffffff 0xffffffffffffffff

def z249 : W := mkw 0xa87d2d4a017c9114 0x543e96a500be488a 0x227c3f0f0078001f 0x913e1f87803c000f

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0xa484001f00000000 0x5242000f80000000

def z251 : W := mkw 0x4582c0b0928162c0 0x22c160584940b160 0xcd83c0f0ff01c380 0x66c1e0787f80e1c0

def z252 : W := mkw 0x09e7640000000000 0x04f3b20000000000 0x437b800000000000 0x21bdc00000000000

def z253 : W := mkw 0x65dec0fa93d163d4 0x32ef607d49e8b1ea 0xf7ff80ff03f9c7ff 0xfbffc07f81fce3ff

def z254 : W := mkw 0x89ef6d0027ffbc20 0x44f7b68013ffde10 0xffffff10fffffc60 0x7fffff887ffffe30

def z255 : W := mkw 0x8bfffd6cc3fdb000 0x45fffeb661fed800 0xffffffece3fff800 0x7ffffff671fffc00

def z256 : W := mkw 0x09ef6c0001648000 0x04f7b60000b24000 0xfbffff000367c000 0x7dffff8001b3e000

def z257 : W := mkw 0x00000b010c2c1822 0x0000058086160c11 0xb8847f131cfe3866 0xdc423f898e7f1c33

def z258 : W := mkw 0x01cc090003fc1000 0x00e6048001fe0800 0xfbfc7f0003fe3800 0x7dfe3f8001ff1c00

def z259 : W := mkw 0x0582d2b5d8000000 0x02c1695aec000000 0xed87fffffc000000 0x76c3fffffe000000

def z260 : W := mkw 0x4582d2b5fe836ee0 0x22c1695aff41b770 0xfd87ffffff87ffe0 0x7ec3ffffffc3fff0

def z261 : W := mkw 0x0000000020024480 0x0000000010012240 0x100000000307c780 0x080000000183e3c0

def z262 : W := mkw 0x44009bb5fc2e5eea 0x22004ddafe172f75 0xbc847ffffcfe3fff 0xde423ffffe7f1fff

def z263 : W := mkw 0x09e76d00002c1000 0x04f3b68000160800 0xfbffff0000fe3800 0x7dffff80007f1c00

def z264 : W := mkw 0x21c4009202900244 0x10e2004901480122 0x0000000000000000 0x0000000000000000

def z265 : W := mkw 0x00008020a0024480 0x0000401050012240 0x08038000e007c000 0x0401c0007003e000

def z266 : W := mkw 0x8008090003fdb000 0x4004048001fed800 0xb8847f0003fff800 0x5c423f8001fffc00

def z267 : W := mkw 0x1239bb6de96ed59a 0x091cddb6f4b76acd 0xff7fbfefe37fc79f 0xffbfdff7f1bfe3cf

def z268 : W := mkw 0x89e76d00002db000 0x44f3b6800016d800 0xebffff000007f800 0x75ffff800003fc00

def z269 : W := mkw 0x0182400000000000 0x00c1200000000000 0xc983c00000000000 0x64c1e00000000000

def z270 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x048040f0fc803fe0 0x024020787e401ff0

def z271 : W := mkw 0x21c41b976ebe1e6e 0x10e20dcbb75f0f37 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z272 : W := mkw 0x2ffff6ffd9500114 0x97fffb7feca8008a 0xeffffffffc78001f 0xf7fffffffe3c000f

def z273 : W := mkw 0x1ffffffffd6eddba 0x8ffffffffeb76edd 0xffffffffffffffff 0xffffffffffffffff

def z274 : W := mkw 0x4402db25fc2f7caa 0x22016d92fe17be55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z275 : W := mkw 0x00001b054c2c182a 0x00000d82a6160c15 0x20847f1f1cf8387f 0x90423f8f8e7c1c3f

def z276 : W := mkw 0x1210104c40000118 0x090808262000008c 0x0000000c00000019 0x000000060000000c

def z277 : W := mkw 0x4182400026836ee0 0x20c120001341b770 0xd983c0000387ffe0 0x6cc1e00001c3fff0

def z278 : W := mkw 0x2008000003d00354 0x1004000001e801aa 0xb484001f03f807ff 0xda42000f81fc03ff

def z279 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x477b80fffc000000 0x23bdc07ffe000000

def z280 : W := mkw 0x4fa3f6b5fe836ee0 0xa7d1fb5aff41b770 0xdd83fff0ff87ffe0 0x6ec1fff87fc3fff0

def z281 : W := mkw 0x0fe7f6b7d8000000 0x87f3fb5bec000000 0x0887ff13fc000000 0x0443ff89fe000000

def z282 : W := mkw 0x9bffed6883fdf190 0x4dfff6b441fef8c8 0xfbffffe003fffb80 0x7dfffff001fffdc0

def z283 : W := mkw 0x1239ba6ded66cdba 0x091cdd36f6b366dd 0xff7bb8ffff67c7ff 0xffbddc7fffb3e3ff

def z284 : W := mkw 0x440080b0b6836ee0 0x220040585b41b770 0x140000f0ff87ffe0 0x0a0000787fc3fff0

def z285 : W := mkw 0x2008000003d00354 0x1004000001e801aa 0x0000000003000380 0x00000000018001c0

def z286 : W := mkw 0x00001a0568260408 0x00000d02b4130204 0xbc847f1ffc660419 0x5e423f8ffe33020c

def z287 : W := mkw 0x33fda0fa83d0c3d4 0x19fed07d41e861ea 0x437b80e00301c380 0x21bdc0700180e1c0

def z288 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x24043f1ffc78047f 0x92021f8ffe3c023f

def z289 : W := mkw 0x1221bb25ec2edcaa 0x0910dd92f6176e55 0xbc87ff1ffcfffc7f 0xde43ff8ffe7ffe3f

def z290 : W := mkw 0x8ff7f7ffda993000 0xc7fbfbffed4c9800 0xeffffffffc983800 0x77fffffffe4c1c00

def z291 : W := mkw 0x0000180460260408 0x00000c0230130204 0xbc00380ce0660419 0x5e001c067033020c

def z292 : W := mkw 0x1218986ce166c598 0x090c4c3670b362cc 0x140000ece367c799 0x0a00007671b3e3cc

def z293 : W := mkw 0x8008090027ffbc2a 0x4004048013ffde15 0x1000000003fffc7f 0x8800000001fffe3f

def z294 : W := mkw 0x1e3bfe6df966c598 0x8f1dff36fcb362cc 0xff7bffecff67c799 0x7fbdfff67fb3e3cc

def z295 : W := mkw 0x0792d2ffd8000000 0x83c9697fec000000 0xcd83c0fffc000000 0x66c1e07ffe000000

def z296 : W := mkw 0x10081b056d6eddba 0x08040d82b6b76edd 0xbc847f1fffffffff 0xde423f8fffffffff

def z297 : W := mkw 0x09ef640003d00000 0x04f7b20001e80000 0xfbffff0003f80000 0x7dffff8001fc0000

def z298 : W := mkw 0x2fffe4fa93d00354 0x97fff27d49e801aa 0xf7ff80ff03f807ff 0xfbffc07f81fc03ff

def z299 : W := mkw 0x57bbf8fcf3e7e7d8 0x2bddfc7e79f3f3ec 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z300 : W := mkw 0x21d400da00000354 0x10ea006d000001aa 0xe7fc00ff000007ff 0xf3fe007f800003ff

def z301 : W := mkw 0x0000000024020c20 0x0000000012010610 0x1000000000863c60 0x0800000000431e30

def z302 : W := mkw 0x89ef640003d1a000 0x44f7b20001e8d000 0xebffff000301c000 0x75ffff800180e000

def z303 : W := mkw 0x000003010c081822 0x0000018086040c11 0x000047001c003800 0x000023800e001c00

def z304 : W := mkw 0x2000009200000244 0x1000004900000122 0x0000001300000066 0x8000000980000033

def z305 : W := mkw 0x21fd28da03f48354 0x10fe946d01fa41aa 0xffffb8ff03ffc7ff 0xffffdc7f81ffe3ff

def z306 : W := mkw 0x0e77f66fd8000000 0x873bfb37ec000000 0x2a7fff0ffc000000 0x153fff87fe000000

def z307 : W := mkw 0xa9ef6d9203fdb244 0x54f7b6c901fed922 0xfbffff1303fff866 0xfdffff8981fffc33

def z308 : W := mkw 0x89ed2d0003fc9000 0x44f6968001fe4800 0xf3fc3f0003f80000 0x79fe1f8001fc0000

def z309 : W := mkw 0x4582c0b0b4036ca0 0x22c160585a01b650 0xcd83c0f0fc07f800 0x66c1e0787e03fc00

def z310 : W := mkw 0x0018004801400110 0x000c002400a00088 0x2278000c00600019 0x113c00060030000c

def z311 : W := mkw 0x4402400014012820 0x220120000a009410 0x000040001c003800 0x000020000e001c00

def z312 : W := mkw 0x4400009014000a60 0x220000480a000530 0x000000101c000060 0x000000080e000030

def z313 : W := mkw 0x0ff7f6ffda800240 0x87fbfb7fed400120 0xffffffffff8007e0 0x7fffffffffc003f0

def z314 : W := mkw 0x0000120548000000 0x00000902a4000000 0x20043f0f00000000 0x10021f8780000000

def z315 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x4b7bb8e0e307c380 0x25bddc707183e1c0

def z316 : W := mkw 0x886d3f05497c900a 0x44369f82a4be4805 0x227c3f0f0078001f 0x913e1f87803c000f

def z317 : W := mkw 0x8029290003fdb000 0x4014948001fed800 0xfb7bb80003fff800 0x7dbddc0001fffc00

def z318 : W := mkw 0x12109b6dec2e5dba 0x09084db6f6172edd 0xbc847ffffcfe3fff 0xde423ffffe7f1fff

def z319 : W := mkw 0x219000da02800354 0x10c8006d014001aa 0xd58000ff038007ff 0xeac0007f81c003ff

def z320 : W := mkw 0x459ac0f8b7c36ff0 0x22cd607c5be1b7f8 0xfffbc0fcffe7fff9 0x7ffde07e7ff3fffc

def z321 : W := mkw 0x0021280000248000 0x0010940000124000 0x0803b8000007c000 0x0401dc000003e000

def z322 : W := mkw 0xcdefe4b093d1e2c0 0x66f7f25849e8f160 0x437b80e00301c380 0x21bdc0700180e1c0

def z323 : W := mkw 0xa008090003fdb354 0x5004048001fed9aa 0x1000000003ffffff 0x8800000001ffffff

def z324 : W := mkw 0x100800000140c190 0x0804000000a060c8 0x000000000301c380 0x000000000180e1c0

def z325 : W := mkw 0x17bbf8fcf166c598 0x0bddfc7e78b362cc 0xfffbf8fcff67c799 0x7ffdfc7e7fb3e3cc

def z326 : W := mkw 0x9beffd24e3fff488 0x4df7fe9271fffa44 0xfbffff00e3fff800 0x7dffff8071fffc00

def z327 : W := mkw 0x8008000003d1a000 0x4004000001e8d000 0x000000000301c000 0x000000000180e000

def z328 : W := mkw 0x1239b96ce16ed598 0x091cdcb670b76acc 0xffffffece3ffff99 0x7ffffff671ffffcc

def z329 : W := mkw 0x461092fffc024ee0 0xa308497ffe012770 0x040000fffc0007e0 0x0200007ffe0003f0

def z330 : W := mkw 0x563bf86cf567edb8 0x2b1dfc367ab3f6dc 0xff7bf8ecff67ff99 0x7fbdfc767fb3ffcc

def z331 : W := mkw 0x0000030108081002 0x0000018084040801 0x0004070300180006 0x80020381800c0003

def z332 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xffffb8ffe3ffc7ff 0xffffdc7ff1ffe3ff

def z333 : W := mkw 0x65dedbffffff7ffe 0x32ef6dffffffbfff 0xffffffffffffffff 0xffffffffffffffff

def z334 : W := mkw 0x0ff7e4fa90000000 0x87fbf27d48000000 0xebffffe000000000 0x75fffff000000000

def z335 : W := mkw 0x201000da00000354 0x1008006d000001aa 0xb48400ff00f807ff 0xda42007f807c03ff

def z336 : W := mkw 0x9bffff6deffffdba 0x4dffffb6f7fffedd 0xffffffffffffffff 0xffffffffffffffff

def z337 : W := mkw 0x201000da00000354 0x1008006d000001aa 0x000000e000000380 0x00000070000001c0

def z338 : W := mkw 0x45825b957eaf3e6a 0x22c12dcabf579f35 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z339 : W := mkw 0x4ff7f6ffde812a60 0xa7fbfb7fef409530 0xeffffffffc803860 0x77fffffffe401c30

def z340 : W := mkw 0x4582d2b5fe836eea 0x22c1695aff41b775 0xdd83c0ffff87ffff 0xeec1e07fffc3ffff

def z341 : W := mkw 0x4582c0b0928162c0 0x22c160584940b160 0xd983c0e00387fb80 0x6cc1e07001c3fdc0

def z342 : W := mkw 0x0054004a00000000 0x002a002500000000 0x227c000f00000000 0x113e000780000000

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0xd90380000307c000 0x6c81c0000183e000

def z344 : W := mkw 0x0dc6449210000000 0x86e3224908000000 0x0000000000000000 0x0000000000000000

def z345 : W := mkw 0x4000000006812a60 0x2000000003409530 0x0000000000803860 0x0000000000401c30

def z346 : W := mkw 0x80000900002db000 0x400004800016d800 0x000000000007f800 0x000000000003fc00

def z347 : W := mkw 0x1239384c6166c598 0x091c9c2630b362cc 0x3278380c0367c799 0x193c1c0601b3e3cc

def z348 : W := mkw 0x21cc009203d00244 0x10e6004901e80122 0xf3fc001303f80066 0xf9fe000981fc0033

def z349 : W := mkw 0x89c65f056ebf3c2a 0x44e32f82b75f9e15 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z350 : W := mkw 0x00188068a1424590 0x000c403450a122c8 0xff7b80ece367c799 0x7fbdc07671b3e3cc

def z351 : W := mkw 0x0ff7f6fffc020c2a 0x87fbfb7ffe010615 0xeffffffffc00047f 0xf7fffffffe00023f

def z352 : W := mkw 0x21dc12df6fd20f7e 0x10ee096fb7e907bf 0xf7fc00fffff807ff 0xfbfe007ffffc03ff

def z353 : W := mkw 0x01dc00da01400110 0x00ee006d00a00088 0xf7fc00ff03600799 0x7bfe007f81b003cc

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0x9480001000800460 0x4a40000800400230

def z355 : W := mkw 0x0ff7f7ffdc081822 0x87fbfbffee040c11 0xeffffffffc983866 0xf7fffffffe4c1c33

def z356 : W := mkw 0x4582409016812a60 0x22c120480b409530 0xd58040f01f803fe0 0x6ac020780fc01ff0

def z357 : W := mkw 0x2188009003d00354 0x10c4004801e801aa 0xd58000f003f807ff 0xeac0007801fc03ff

def z358 : W := mkw 0x8fffffffd97c9000 0xc7ffffffecbe4800 0xeffffffffc780000 0x77fffffffe3c0000

def z359 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x510380e00387ffe0 0x2881c07001c3fff0

def z360 : W := mkw 0x0ffff6ffd9400110 0x87fffb7feca00088 0xffffffffff600799 0x7fffffffffb003cc

def z361 : W := mkw 0x0bf7764f48000000 0x85fbbb27a4000000 0xebffff0f00000000 0x75ffff8780000000

def z362 : W := mkw 0x21cc009203d00354 0x10e6004901e801aa 0x1084001303f807ff 0x8842000981fc03ff

def z363 : W := mkw 0x89ff6dda03fdb000 0x44ffb6ed01fed800 0xffffffff03fff800 0x7fffffff81fffc00

def z364 : W := mkw 0x01dc00da03d00000 0x00ee006d01e80000 0xf7fc00ff03f80000 0x7bfe007f81fc0000

def z365 : W := mkw 0x0182c020a2836480 0x00c160105141b240 0xdd83c0e0e387ff80 0x6ec1e07071c3ffc0

def z366 : W := mkw 0x440080b0b4024ee0 0x220040585a012770 0x9c8040f0fc863fe0 0x4e4020787e431ff0

def z367 : W := mkw 0x0000000024020c2a 0x0000000012010615 0x000000000000047f 0x800000000000023f

def z368 : W := mkw 0x4582409012812240 0x22c1204809409120 0x0000000000000000 0x0000000000000000

def z369 : W := mkw 0x061092fffc020c2a 0x8308497ffe010615 0x040000fffc00047f 0x8200007ffe00023f

def z370 : W := mkw 0x89c6440002912000 0x44e3220001489000 0x0000000000000000 0x0000000000000000

def z371 : W := mkw 0x000012054800000a 0x00000902a4000005 0x0000000f0000001f 0x800000078000000f

def z372 : W := mkw 0x205c00da01500354 0x102e006d00a801aa 0x267c00ff007807ff 0x933e007f803c03ff

def z373 : W := mkw 0x1239204801408110 0x091c902400a04088 0x0278000000000000 0x013c000000000000

def z374 : W := mkw 0x2fffe4fa93d00354 0x97fff27d49e801aa 0x437b80e003000380 0x21bdc070018001c0

def z375 : W := mkw 0x1231b06ce0024598 0x0918d836700122cc 0xef7bb8ece0000799 0x77bddc76700003cc

def z376 : W := mkw 0x57bbe0f8b7c3eff0 0x2bddf07c5be1f7f8 0xdffbc0f0ff87ffe0 0x6ffde0787fc3fff0

def z377 : W := mkw 0x21dc00da01500114 0x10ee006d00a8008a 0xe7fc00ff0078001f 0xf3fe007f803c000f

def z378 : W := mkw 0x27dc92ffdbd00354 0x93ee497fede801aa 0xf7fc00fffff807ff 0xfbfe007ffffc03ff

def z379 : W := mkw 0x00181b4d6d6e1d3a 0x000c0da6b6b70e9d 0xfffc7ffffffe3fff 0xfffe3fffffff1fff

def z380 : W := mkw 0x89ef6c0003f5a000 0x44f7b60001fad000 0xfb7bb8000367c000 0x7dbddc0001b3e000

def z381 : W := mkw 0x0231a06880000000 0x0118d03440000000 0x437b80e000000000 0x21bdc07000000000

def z382 : W := mkw 0x0e23f625d8000000 0x8711fb12ec000000 0xac87ff1ffc000000 0x5643ff8ffe000000

def z383 : W := mkw 0x09e7760548000000 0x04f3bb02a4000000 0xefffff1ffc000000 0x77ffff8ffe000000

def z384 : W := mkw 0x6ffff6ffffd36ff4 0xb7fffb7fffe9b7fa 0xffffffffffffffff 0xffffffffffffffff

def z385 : W := mkw 0x8dc647931a993000 0xc6e323c98d4c9800 0x008447131c983800 0x004223898e4c1c00

def z386 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xbc007f0cfc663c19 0x5e003f867e331e0c

def z387 : W := mkw 0x4402c020b4036ca0 0x220160105a01b650 0xdd03c0e0ff07ff80 0x6e81e0707f83ffc0

def z388 : W := mkw 0xcda3edb0b6affee0 0x66d1f6d85b57ff70 0xdd83fff0ff87ffe0 0x6ec1fff87fc3fff0

def z389 : W := mkw 0x01d41bdf6c2e1c2a 0x00ea0defb6170e15 0xfffc7ffffcfe3c7f 0xfffe3ffffe7f1e3f

def z390 : W := mkw 0x80080900017c9000 0x4004048000be4800 0x0000000000780000 0x00000000003c0000

def z391 : W := mkw 0x06109bfffc2e1c2a 0x83084dfffe170e15 0xbc847ffffcfe3c7f 0xde423ffffe7f1e3f

def z392 : W := mkw 0x0ff7fefff8260408 0x87fbff7ffc130204 0xfffffffffc660419 0x7ffffffffe33020c

def z393 : W := mkw 0x25dec0fa93d00354 0x12ef607d49e801aa 0xffffc0fffff807ff 0xffffe07ffffc03ff

def z394 : W := mkw 0x0ffff6ffdbd00000 0x87fffb7fede80000 0xfffffffffff80000 0x7ffffffffffc0000

def z395 : W := mkw 0x0a753f4f482c100a 0x853a9fa7a4160805 0x227c3f0f0078001f 0x913e1f87803c000f

def z396 : W := mkw 0x0ff7e4fa90000000 0x87fbf27d48000000 0xcffbc0f0fc000000 0x67fde0787e000000

def z397 : W := mkw 0x01c4000002900000 0x00e2000001480000 0x0084000000980000 0x00420000004c0000

def z398 : W := mkw 0x1239a868a166c598 0x091cd43450b362cc 0x537b80e00367c799 0x29bdc07001b3e3cc

def z399 : W := mkw 0x0ff7ffffd82c1000 0x87fbffffec160800 0xfffffffffcfe3800 0x7ffffffffe7f1c00

def z400 : W := mkw 0x558ac8b0b7e7eff8 0x2ac564585bf3f7fc 0xdd83c0f0ffe7fff9 0x6ec1e0787ff3fffc

def z401 : W := mkw 0xcdc6c5b0b69b7ee0 0x66e362d85b4dbf70 0xdd87c7f0ff9fffe0 0x6ec3e3f87fcffff0

def z402 : W := mkw 0x641080fab4024ff4 0x3208407d5a0127fa 0x040000fffc0007ff 0x8200007ffe0003ff

def z403 : W := mkw 0x65c6409216912a64 0x32e320490b489532 0x008440131c983866 0x804220098e4c1c33

def z404 : W := mkw 0x21de40da03d12354 0x10ef206d01e891aa 0xffffc0ff03ffffff 0xffffe07f81ffffff

def z405 : W := mkw 0xa9ff6dda03fdb354 0x54ffb6ed01fed9aa 0xfbffffe003fffb80 0x7dfffff001fffdc0

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z407 : W := mkw 0x1ffff6ffd940c190 0x8ffffb7feca060c8 0xefffffffff01c380 0x77ffffffff80e1c0

def z408 : W := mkw 0x33fda0fa83d0c3d4 0x19fed07d41e861ea 0xf7ff80ff03f9c7ff 0xfbffc07f81fce3ff

def z409 : W := mkw 0x21dc18de63f6075c 0x10ee0c6f31fb03ae 0xfffc38ffe3fe07ff 0xfffe1c7ff1ff03ff

def z410 : W := mkw 0x00001b05682e140a 0x00000d82b4170a05 0xbc043f0fe07e041f 0xde021f87f03f020f

def z411 : W := mkw 0x9a23fd24e02ff488 0x4d11fe927017fa44 0x0803ff00e007f800 0x0401ff807003fc00

def z412 : W := mkw 0x327db86ee176c59c 0x193edc3770bb62ce 0xff7fb8efe37fc79f 0xffbfdc77f1bfe3cf

def z413 : W := mkw 0x0a21360548000000 0x85109b02a4000000 0x00003f0000000000 0x00001f8000000000

def z414 : W := mkw 0x13bbf86ce3e7e598 0x09ddfc3671f3f2cc 0xfffbf8ece3e7ff99 0x7ffdfc7671f3ffcc

def z415 : W := mkw 0xcdefffb5fffffeea 0x66f7ffdaffffff75 0xffffffffffffffff 0xffffffffffffffff

def z416 : W := mkw 0x440092b5fc024eea 0x2200495afe012775 0x040000fffc0007ff 0x8200007ffe0003ff

def z417 : W := mkw 0xc58ac9b0b7fffee0 0x62c564d85bffff70 0xdd83c0f0ffffffe0 0x6ec1e0787ffffff0

def z418 : W := mkw 0x0582409010000000 0x02c1204808000000 0x008040101c000000 0x004020080e000000

def z419 : W := mkw 0x21d400da02900244 0x10ea006d01480122 0xe7fc00ff00980066 0xf3fe007f804c0033

def z420 : W := mkw 0x000002010c000822 0x0000010086000411 0x000000131c000066 0x800000098e000033

def z421 : W := mkw 0x0823640000000000 0x0411b20000000000 0x0803ff0000000000 0x0401ff8000000000

def z422 : W := mkw 0x0018184c61660518 0x000c0c2630b3028c 0xff7838ece3660799 0x7fbc1c7671b303cc

def z423 : W := mkw 0xa9ef6d0003fdb354 0x54f7b68001fed9aa 0xfbffff0003ffffff 0xfdffff8001ffffff

def z424 : W := mkw 0x0000000000000000 0x0000000000000000 0x2004000f0078001f 0x90020007803c000f

def z425 : W := mkw 0x000012056c020c20 0x00000902b6010610 0xbc847f1ffc863c60 0x5e423f8ffe431e30

def z426 : W := mkw 0x47b3f0fcf6836ee0 0x23d9f87e7b41b770 0xfffbf8fcff87ffe0 0x7ffdfc7e7fc3fff0

def z427 : W := mkw 0x161092fff8024598 0x8b08497ffc0122cc 0x040000fffc000799 0x0200007ffe0003cc

def z428 : W := mkw 0x65de40da17d12b74 0x32ef206d0be895ba 0xf7fc40ff1ff83fff 0xfbfe207f8ffc1fff

def z429 : W := mkw 0x01cc000003d00000 0x00e6000001e80000 0x4378000003000000 0x21bc000001800000

def z430 : W := mkw 0x21d400da02900354 0x10ea006d014801aa 0x048400ff009807ff 0x8242007f804c03ff

def z431 : W := mkw 0x4ff7f6fffc036ca0 0xa7fbfb7ffe01b650 0xeffffffffc07f800 0x77fffffffe03fc00

def z432 : W := mkw 0x8ff7ffffd82db000 0xc7fbffffec16d800 0xeffffffffc07f800 0x77fffffffe03fc00

def z433 : W := mkw 0x1239384c41648118 0x091c9c2620b2408c 0xfb7bb80c0367c019 0x7dbddc0601b3e00c

def z434 : W := mkw 0x0e23e42090000000 0x8711f21048000000 0x0003800000000000 0x0001c00000000000

def z435 : W := mkw 0x000003012c0a1c22 0x0000018096050e11 0x9c844713fc9e3c66 0xce422389fe4f1e33

def z436 : W := mkw 0x0029a820a166c480 0x0014d41050b36240 0xff7bb8e0e367c780 0x7fbddc7071b3e3c0

def z437 : W := mkw 0x886d240001508000 0x4436920000a84000 0x0278000000000000 0x013c000000000000

def z438 : W := mkw 0x4582d8b4f6a76ee8 0x22c16c5a7b53b774 0xfd83f8fcffe7fff9 0x7ec1fc7e7ff3fffc

def z439 : W := mkw 0x2dc646931a900244 0x96e323498d480122 0x008447131c980066 0x804223898e4c0033

def z440 : W := mkw 0x8fffffffffffbc2a 0xc7ffffffffffde15 0xfffffffffffffc7f 0xfffffffffffffe3f

def z441 : W := mkw 0x09c6440000000000 0x04e3220000000000 0x0084470000000000 0x0042238000000000

def z442 : W := mkw 0x21cc000003d00354 0x10e6000001e801aa 0xf3fc000003f807ff 0xf9fe000001fc03ff

def z443 : W := mkw 0x2010004a00000114 0x100800250000008a 0x0000000f0000001f 0x800000078000000f

def z444 : W := mkw 0x0000120548000000 0x00000902a4000000 0x08007f00fc000000 0x04003f807e000000

def z445 : W := mkw 0x0dd646db18000000 0x86eb236d8c000000 0xe7fc47ff1c000000 0x73fe23ff8e000000

def z446 : W := mkw 0x12009024e0024488 0x0900481270012244 0x00000000e0000000 0x0000000070000000

def z447 : W := mkw 0x0bf7f46cc0000000 0x05fbfa3660000000 0xefffffece0000000 0x77fffff670000000

def z448 : W := mkw 0x65dec0fab7d36ff4 0x32ef607d5be9b7fa 0xdffbc0f0ff87ffe0 0x6ffde0787fc3fff0

def z449 : W := mkw 0x000013056c0a1c2a 0x00000982b6050e15 0x0484471ffc983c7f 0x8242238ffe4c1e3f

def z450 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x450380f0ff01c7e0 0x2281c0787f80e3f0

def z451 : W := mkw 0x0000802080000000 0x0000401040000000 0xcd0380e0e0000000 0x6681c07070000000

def z452 : W := mkw 0x8a7d3f4f497c9000 0xc53e9fa7a4be4800 0x227c3f0f00780000 0x113e1f87803c0000

def z453 : W := mkw 0xdffffdfcf7fffff8 0x6ffffefe7bfffffc 0xfffffffcfffffff9 0x7ffffffe7ffffffc

def z454 : W := mkw 0x89ef6f010ffdb822 0x44f7b78087fedc11 0xfbffff131ffff866 0xfdffff898ffffc33

def z455 : W := mkw 0x0582dbb5fc2e1c2a 0x02c16ddafe170e15 0xfd87fffffcfe3c7f 0xfec3fffffe7f1e3f

def z456 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x0883c010fc87f860 0x0441e0087e43fc30

def z457 : W := mkw 0x1fffe4fa9140c190 0x8ffff27d48a060c8 0x437b80e00301c380 0x21bdc0700180e1c0

def z458 : W := mkw 0x1008080001648118 0x0804040000b2408c 0x0000000000600019 0x000000000030000c

def z459 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x1400001ffcfe3c7f 0x8a00000ffe7f1e3f

def z460 : W := mkw 0x21dc09da27fe1f7e 0x10ee04ed13ff0fbf 0xf7fc00ff03fe3fff 0xfbfe007f81ff1fff

def z461 : W := mkw 0x000012056c020c2a 0x00000902b6010615 0x00000000fc000000 0x000000007e000000

def z462 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x30043f0f00fe3c7f 0x98021f87807f1e3f

def z463 : W := mkw 0x40000000028162c0 0x200000000140b160 0x000000000301c380 0x000000000180e1c0

def z464 : W := mkw 0x1239a068a142c590 0x091cd03450a162c8 0xdf7b80e0e307c780 0x6fbdc0707183e3c0

def z465 : W := mkw 0x57bbe0f893c1e3d0 0x2bddf07c49e0f1e8 0x437b80e00301c380 0x21bdc0700180e1c0

def z466 : W := mkw 0x000012056c020c2a 0x00000902b6010615 0xb484001ffcf8047f 0xda42000ffe7c023f

def z467 : W := mkw 0x0fd6d6ffd8000000 0x87eb6b7fec000000 0x048447fffc000000 0x024223fffe000000

def z468 : W := mkw 0x004c000001500000 0x0026000000a80000 0x227c000000780000 0x113e0000003c0000

def z469 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffff1f03fffc7f 0xffffff8f81fffe3f

def z470 : W := mkw 0x201012df6c020f7e 0x1008096fb60107bf 0x040000fffc0007ff 0x8200007ffe0003ff

def z471 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x0c007f1ffc063c7f 0x86003f8ffe031e3f

def z472 : W := mkw 0x1218906ce1424598 0x090c483670a122cc 0xf77800ece3600799 0x7bbc007671b003cc

def z473 : W := mkw 0x00009824e0264488 0x00004c1270132244 0xfd03b8ece367c799 0x7e81dc7671b3e3cc

def z474 : W := mkw 0x4dc6c6b3be836ee0 0xa6e36359df41b770 0xdd87c7f3ff87ffe0 0x6ec3e3f9ffc3fff0

def z475 : W := mkw 0x001000da00000000 0x0008006d00000000 0x040000ff00000000 0x0200007f80000000

def z476 : W := mkw 0x4582c3b1be8b7ee2 0x22c161d8df45bf71 0xdd87c7f3ff9fffe6 0xeec3e3f9ffcffff3

def z477 : W := mkw 0x2008000001500114 0x1004000000a8008a 0x000000000078001f 0x80000000003c000f

def z478 : W := mkw 0x21dc004a03d00114 0x10ee002501e8008a 0xf3fc000f03f8001f 0xf9fe000781fc000f

def z479 : W := mkw 0x0021200000000000 0x0010900000000000 0xeb7bb80000000000 0x75bddc0000000000

def z480 : W := mkw 0x000012056c020c2a 0x00000902b6010615 0xac847f1ffc00047f 0xd6423f8ffe00023f

def z481 : W := mkw 0x88212d00002c9000 0x4410968000164800 0x00003f0000000000 0x00001f8000000000

def z482 : W := mkw 0x4000090026af7eea 0x200004801357bf75 0x1000000003ffffff 0x8800000001ffffff

def z483 : W := mkw 0xa9c6459202993244 0x54e322c9014c9922 0x0084471300983866 0x80422389804c1c33

def z484 : W := mkw 0x0000100440000000 0x0000080220000000 0xac00380ce0000000 0x56001c0670000000

def z485 : W := mkw 0x21dc03db0fd81b76 0x10ee01ed87ec0dbb 0xf7fc47ff1ff83fff 0xfbfe23ff8ffc1fff

def z486 : W := mkw 0x4402c020b4036ca0 0x220160105a01b650 0x9c83c010fc87fc60 0x4e41e0087e43fe30

def z487 : W := mkw 0x000003010c081822 0x0000018086040c11 0xb484471f1cf83c7f 0xda42238f8e7c1e3f

def z488 : W := mkw 0x00001a056c260c2a 0x00000d02b6130615 0xbc00381ffc66047f 0xde001c0ffe33023f

def z489 : W := mkw 0x01ce400003d12000 0x00e7200001e89000 0xfbffc00003fff800 0x7dffe00001fffc00

def z490 : W := mkw 0x57a3f8b4f6a7eee8 0x2bd1fc5a7b53f774 0xdd83f8f0ff87ffe0 0x6ec1fc787fc3fff0

def z491 : W := mkw 0x9a3bfd6ce16ff598 0x4d1dfeb670b7facc 0xff7bffece367ff99 0x7fbdfff671b3ffcc

def z492 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x637fbf000379c000 0x31bfdf8001bce000

def z493 : W := mkw 0x0a753f4f6c2e1c2a 0x853a9fa7b6170e15 0xbefc7f1ffcfe3c7f 0xdf7e3f8ffe7f1e3f

def z494 : W := mkw 0x0ff776df58000000 0x87fbbb6fac000000 0x22fc7f1f1c000000 0x117e3f8f8e000000

def z495 : W := mkw 0x561090fcf4024ff8 0x2b08487e7a0127fc 0x040000fcfc0007f9 0x0200007e7e0003fc

def z496 : W := mkw 0x33dc90fee3d247dc 0x19ee487f71e923ee 0xf7fc00ffe3f807ff 0xfbfe007ff1fc03ff

def z497 : W := mkw 0x31dc08da23f6c7dc 0x18ee046d11fb63ee 0xf7fc00ff03ffc7ff 0xfbfe007f81ffe3ff

def z498 : W := mkw 0x00001b05482c100a 0x00000d82a4160805 0x00003f0000000000 0x00001f8000000000

def z499 : W := mkw 0x0400029318000000 0x820001498c000000 0x000000131c000000 0x000000098e000000

def z500 : W := mkw 0x2ffff6ffdbd00354 0x97fffb7fede801aa 0xefffffffff000380 0x77ffffffff8001c0

def z501 : W := mkw 0x00001b05482c100a 0x00000d82a4160805 0xb4843f1f00f8047f 0xda421f8f807c023f

def z502 : W := mkw 0x01c4000000000000 0x00e2000000000000 0xe3fc000000000000 0x71fe000000000000

def z503 : W := mkw 0x0631b2ffd8000000 0x8318d97fec000000 0xef7bb8fffc000000 0x77bddc7ffe000000

def z504 : W := mkw 0x0018004801400110 0x000c002400a00088 0x437800e003000380 0x21bc0070018001c0

def z505 : W := mkw 0x205c004a01500114 0x102e002500a8008a 0xf77c00ef0378079f 0xfbbe007781bc03cf

def z506 : W := mkw 0x4ff7fffffeaf7eea 0xa7fbffffff57bf75 0xffffffffffffffff 0xffffffffffffffff

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000f8047f 0x88000000007c023f

def z508 : W := mkw 0x1ffffcfef166c598 0x8ffffe7f78b362cc 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z509 : W := mkw 0x0029200001408000 0x0014900000a04000 0x437b80000301c000 0x21bdc0000180e000

def z510 : W := mkw 0x201800da03d00354 0x100c006d01e801aa 0x140000ff03f807ff 0x8a00007f81fc03ff

def z511 : W := mkw 0xcdc6459016993a60 0x66e322c80b4c9d30 0x008447101c983860 0x004223880e4c1c30

def z512 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x4903c0e0ff07fb80 0x2481e0707f83fdc0

def z513 : W := mkw 0x2000000002900244 0x1000000001480122 0x0000000000980066 0x80000000004c0033

def z514 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xac847f1ffc063800 0x56423f8ffe031c00

def z515 : W := mkw 0xcdefed20b7fffca0 0x66f7f6905bfffe50 0xfbffff00fffff800 0x7dffff807ffffc00

def z516 : W := mkw 0x658ac0b0b7d36ff4 0x32c560585be9b7fa 0xdd83c0f0ffffffff 0xeec1e0787fffffff

def z517 : W := mkw 0x886d2d0003fdb000 0x4436968001fed800 0x327c3f0003fff800 0x193e1f8001fffc00

def z518 : W := mkw 0x2ffffffffffe1f7e 0x97ffffffffff0fbf 0xfffffffffffe3fff 0xffffffffffff1fff

def z519 : W := mkw 0x6008000027d36ff4 0x3004000013e9b7fa 0x1000000003ffffff 0x8800000001ffffff

def z520 : W := mkw 0x0000000024020c20 0x0000000012010610 0x08004000fc063800 0x040020007e031c00

def z521 : W := mkw 0x4000000024036ca0 0x200000001201b650 0x000000000007f800 0x000000000003fc00

def z522 : W := mkw 0x2bfd36df4bd00354 0x95fe9b6fa5e801aa 0xf7fc3fff03f807ff 0xfbfe1fff81fc03ff

def z523 : W := mkw 0x0182400026832c20 0x00c1200013419610 0xdd83c010ff87fc60 0x6ec1e0087fc3fe30

def z524 : W := mkw 0x1bfffc6ce166c598 0x0dfffe3670b362cc 0xffffffece367c799 0x7ffffff671b3e3cc

def z525 : W := mkw 0x12393b4d6d6e9d3a 0x091c9da6b6b74e9d 0xbefc7f1ffcfe3c7f 0xdf7e3f8ffe7f1e3f

def z526 : W := mkw 0x0000000024020c20 0x0000000012010610 0xbc84401ffcfe3c7f 0xde42200ffe7f1e3f

def z527 : W := mkw 0x0e23ff25fc2e1c2a 0x8711ff92fe170e15 0x0803ff00fc063800 0x0401ff807e031c00

def z528 : W := mkw 0x9239b96ce3fff598 0x491cdcb671fffacc 0xff7bb8ece3ffff99 0x7fbddc7671ffffcc

def z529 : W := mkw 0x0dc647931c081822 0x86e323c98e040c11 0x008447131c983866 0x804223898e4c1c33

def z530 : W := mkw 0x8fefff25dbfdb000 0xc7f7ff92edfed800 0xfbffff00fffff800 0x7dffff807ffffc00

def z531 : W := mkw 0x1639bafff966c598 0x8b1cdd7ffcb362cc 0xff7bb8ffff67c799 0x7fbddc7fffb3e3cc

def z532 : W := mkw 0x4582c0b0b4024ee0 0x22c160585a012770 0xcd83c0f0fc0007e0 0x66c1e0787e0003f0

def z533 : W := mkw 0x0844060308000000 0x8422030184000000 0x0004070300000000 0x0002038180000000

def z534 : W := mkw 0x29ff64da03d00354 0x14ffb26d01e801aa 0xffffffff03f807ff 0xffffffff81fc03ff

def z535 : W := mkw 0x8fffe4fa93d1a000 0xc7fff27d49e8d000 0x437b80e00301c000 0x21bdc0700180e000

def z536 : W := mkw 0x4582409016812a60 0x22c120480b409530 0xd983c0101f87f860 0x6cc1e0080fc3fc30

def z537 : W := mkw 0x07d492ffd8000000 0x83ea497fec000000 0xe7fc00fffc000000 0x73fe007ffe000000

def z538 : W := mkw 0x1210906ce0024598 0x09084836700122cc 0xdd0380ece307c799 0x6e81c0767183e3cc

def z539 : W := mkw 0x45cec0b0b7d36ee0 0x22e760585be9b770 0xffffc0f0ffffffe0 0x7fffe0787ffffff0

def z540 : W := mkw 0x0000180460260408 0x00000c0230130204 0x08003800e0060000 0x04001c0070030000

def z541 : W := mkw 0x0000010000081000 0x0000008000040800 0x0084470000983800 0x00422380004c1c00

def z542 : W := mkw 0x0a75b66fc8000000 0x853adb37e4000000 0xef7fbfefe0000000 0x77bfdff7f0000000

def z543 : W := mkw 0x4ff7f6fffc024ee0 0xa7fbfb7ffe012770 0xeffffffffc0007e0 0x77fffffffe0003f0

def z544 : W := mkw 0x00000b012c2e1c2a 0x0000058096170e15 0x108447131cfe3c7f 0x884223898e7f1e3f

def z545 : W := mkw 0x5239b86ce7e7eff8 0x291cdc3673f3f7fc 0xff7bb8ece3e7fff9 0x7fbddc7671f3fffc

def z546 : W := mkw 0x440080b0b4024ee0 0x220040585a012770 0xdd0380f0ff07c7e0 0x6e81c0787f83e3f0

def z547 : W := mkw 0x65dec0fa93d163d4 0x32ef607d49e8b1ea 0x437b80e00301c380 0x21bdc0700180e1c0

def z548 : W := mkw 0x05d6c0fa90000000 0x02eb607d48000000 0xefffc0fffc000000 0x77ffe07ffe000000

def z549 : W := mkw 0x00000900002c1000 0x0000048000160800 0x1000000000fe3800 0x08000000007f1c00

def z550 : W := mkw 0x886d2d00017c9000 0x4436968000be4800 0xfb7fbf00037fc000 0x7dbfdf8001bfe000

def z551 : W := mkw 0x205c1b4f6d7e1d3e 0x102e0da7b6bf0e9f 0xbefc7f1ffcfe3c7f 0xdf7e3f8ffe7f1e3f

def z552 : W := mkw 0x1a7dbe6fe966c598 0x8d3edf37f4b362cc 0xff7fbfefe367c799 0x7fbfdff7f1b3e3cc

def z553 : W := mkw 0xbbfffdfee3fff7dc 0x5dfffeff71fffbee 0xffffffffe3ffffff 0xfffffffff1ffffff

def z554 : W := mkw 0x01825b056eaf3c2a 0x00c12d82b7579e15 0xfd87ff1ffffffc7f 0xfec3ff8ffffffe3f

def z555 : W := mkw 0x0000000000000000 0x0000000000000000 0xb084000000f80000 0x58420000007c0000

def z556 : W := mkw 0x0ff7f6fffc020c20 0x87fbfb7ffe010610 0xfffffffffc863c60 0x7ffffffffe431e30

def z557 : W := mkw 0x00000900002c1000 0x0000048000160800 0x20043f0000780000 0x10021f80003c0000

def z558 : W := mkw 0x89ef7f054bfdb00a 0x44f7bf82a5fed805 0xfbffff0f03fff81f 0xfdffff8781fffc0f

def z559 : W := mkw 0x3ffffefffbf6c7dc 0x9fffff7ffdfb63ee 0xffffffffffffc7ff 0xffffffffffffe3ff

def z560 : W := mkw 0x0182409002812240 0x00c1204801409120 0xdd83c0f00387ffe0 0x6ec1e07801c3fff0

def z561 : W := mkw 0x00000900002c1000 0x0000048000160800 0x08007f0000063800 0x04003f8000031c00

def z562 : W := mkw 0x4180009026836ee0 0x20c000481341b770 0xd58000f00387ffe0 0x6ac0007801c3fff0

def z563 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c804010fc000000 0x464020087e000000

def z564 : W := mkw 0xedffedfab7fffff4 0x76fff6fd5bfffffa 0xffffffffffffffff 0xffffffffffffffff

def z565 : W := mkw 0x00000900002c1000 0x0000048000160800 0xbc847f1f00fe3c7f 0xde423f8f807f1e3f

def z566 : W := mkw 0x0000802080004080 0x0000401040002040 0x410380e00301c380 0x2081c0700180e1c0

def z567 : W := mkw 0x8ffff6ffdbd1a000 0xc7fffb7fede8d000 0xefffffffff01c000 0x77ffffffff80e000

def z568 : W := mkw 0x1ff7f6fff8024598 0x8ffbfb7ffc0122cc 0xeffffffffc000799 0x77fffffffe0003cc

def z569 : W := mkw 0x201800da01400354 0x100c006d00a001aa 0xf77800ff036007ff 0xfbbc007f81b003ff

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0xa8847f0000000000 0x54423f8000000000

def z571 : W := mkw 0x01d400da00000000 0x00ea006d00000000 0x437800e000000000 0x21bc007000000000

def z572 : W := mkw 0x09e77f056c2e1c2a 0x04f3bf82b6170e15 0xffffff1ffcfe3c7f 0xffffff8ffe7f1e3f

def z573 : W := mkw 0x5008080027e7eff8 0x2804040013f3f7fc 0x1000000003e7fff9 0x0800000001f3fffc

def z574 : W := mkw 0x40008020a6836ee0 0x200040105341b770 0xdd0380e0e387ffe0 0x6e81c07071c3fff0

def z575 : W := mkw 0x1221380440248008 0x09109c0220124004 0x0000380000000000 0x00001c0000000000

def z576 : W := mkw 0x9a7dbd6ce17ed598 0x4d3edeb670bf6acc 0xff7fbfece37fc799 0x7fbfdff671bfe3cc

def z577 : W := mkw 0x0000080000240000 0x0000040000120000 0xb800380000660000 0x5c001c0000330000

def z578 : W := mkw 0x0582c0b0b0024480 0x02c1605858012240 0xdd83c0f0ff07c780 0x6ec1e0787f83e3c0

def z579 : W := mkw 0x00000900242e1c2a 0x0000048012170e15 0x0000000000063800 0x0000000000031c00

def z580 : W := mkw 0x0ff7e4fa90000000 0x87fbf27d48000000 0xe7ff80ff00000000 0x73ffc07f80000000

def z581 : W := mkw 0x88236d00002db000 0x4411b6800016d800 0xb887ff0000fff800 0x5c43ff80007ffc00

def z582 : W := mkw 0xafffffffdbfdb354 0xd7ffffffedfed9aa 0xffffffffffffffff 0xffffffffffffffff

def z583 : W := mkw 0x0ff7f4fed0000000 0x87fbfa7f68000000 0xef7bb8ece0000000 0x77bddc7670000000

def z584 : W := mkw 0x9bfffc6ce3f7e598 0x4dfffe3671fbf2cc 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z585 : W := mkw 0x13fdb8fee166c598 0x09fedc7f70b362cc 0xffffb8ffe367c799 0x7fffdc7ff1b3e3cc

def z586 : W := mkw 0x00000900242e1c2a 0x0000048012170e15 0xb484001f00fe3c7f 0xda42000f807f1e3f

def z587 : W := mkw 0x0180009002800240 0x00c0004801400120 0x410000e003000380 0x20800070018001c0

def z588 : W := mkw 0x2000000000000354 0x10000000000001aa 0x00000000000007ff 0x80000000000003ff

def z589 : W := mkw 0x818a490003fdb000 0x40c5248001fed800 0xd983c00003fff800 0x6cc1e00001fffc00

def z590 : W := mkw 0x77fff8fef7f7effc 0x3bfffc7f7bfbf7fe 0xfffff8ffffffffff 0xfffffc7fffffffff

def z591 : W := mkw 0x0000180440240008 0x00000c0220120004 0x2000380c00600019 0x10001c060030000c

def z592 : W := mkw 0x040080b090000000 0x0200405848000000 0x040000f0fc000000 0x020000787e000000

def z593 : W := mkw 0xcc23ed20b42ffca0 0x6611f6905a17fe50 0x0803ff00fc07f800 0x0401ff807e03fc00

def z594 : W := mkw 0x2018004803d00354 0x100c002401e801aa 0xf77800ec03f807ff 0xfbbc007601fc03ff

def z595 : W := mkw 0x0000000002800240 0x0000000001400120 0x10000000038007e0 0x0800000001c003f0

def z596 : W := mkw 0x21dc80faa3d247d4 0x10ee407d51e923ea 0xffff80ffe3ffc7ff 0xffffc07ff1ffe3ff

def z597 : W := mkw 0x07b3f0fcd0000000 0x03d9f87e68000000 0xeffbf8fcfc000000 0x77fdfc7e7e000000

def z598 : W := mkw 0x01dc004803d00110 0x00ee002401e80088 0xf7fc00ec03f80799 0x7bfe007601fc03cc

def z599 : W := mkw 0x4582c0b0b28366c0 0x22c160585941b360 0xdd0380e0e307c780 0x6e81c0707183e3c0

def z600 : W := mkw 0x1239384c41648118 0x091c9c2620b2408c 0xf77838ec03600799 0x7bbc1c7601b003cc

def z601 : W := mkw 0x6592c0fab6836ff4 0x32c9607d5b41b7fa 0xdd83c0ffff87ffff 0xeec1e07fffc3ffff

def z602 : W := mkw 0x9bff7d4c43fdb118 0x4dffbea621fed88c 0xfbffff0c03fff819 0x7dffff8601fffc0c

def z603 : W := mkw 0x88237f056c2fbc2a 0x4411bf82b617de15 0xbc87ff1ffcfffc7f 0xde43ff8ffe7ffe3f

def z604 : W := mkw 0x21dc12df4bd00354 0x10ee096fa5e801aa 0xfffc7ffffff807ff 0xfffe3ffffffc03ff

def z605 : W := mkw 0x205c004a03d00354 0x102e002501e801aa 0x327c000f03f807ff 0x993e000781fc03ff

def z606 : W := mkw 0x00000900002c100a 0x0000048000160805 0x000000000078001f 0x80000000003c000f

def z607 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xd7f800f0038007e0 0x6bfc007801c003f0

def z608 : W := mkw 0x5623f824f427eca8 0x2b11fc127a13f654 0x0803f800fc07f800 0x0401fc007e03fc00

def z609 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x9c807f10fc863c60 0x4e403f887e431e30

def z610 : W := mkw 0x1000000020024598 0x08000000100122cc 0x0000000000000799 0x00000000000003cc

def z611 : W := mkw 0x8e23ff25d82db000 0xc711ff92ec16d800 0x0803ff00fc07f800 0x0401ff807e03fc00

def z612 : W := mkw 0x89ce4d0003fdb000 0x44e7268001fed800 0x1084470003fff800 0x0842238001fffc00

def z613 : W := mkw 0x89c6450002993000 0x44e32280014c9800 0xd987c700039ff800 0x6cc3e38001cffc00

def z614 : W := mkw 0x00001904602e1408 0x00000c8230170a04 0xbc847f0ce0fe3c19 0x5e423f86707f1e0c

def z615 : W := mkw 0x9bffe46883d1e190 0x4dfff23441e8f0c8 0x437b80e00301c380 0x21bdc0700180e1c0

def z616 : W := mkw 0x45d6c0fab6836ee0 0x22eb607d5b41b770 0xffffc0ffff87ffe0 0x7fffe07fffc3fff0

def z617 : W := mkw 0x40001b056eaf7eea 0x20000d82b757bf75 0xbc847f1fffffffff 0xde423f8fffffffff

def z618 : W := mkw 0x9008090023fff598 0x4804048011fffacc 0x1000000003ffff99 0x0800000001ffffcc

def z619 : W := mkw 0x0e33f6ffd8000000 0x8719fb7fec000000 0x0c03fffffc000000 0x0601fffffe000000

def z620 : W := mkw 0x0000000004000820 0x0000000002000410 0x008040101c803860 0x004020080e401c30

def z621 : W := mkw 0x0000120548000000 0x00000902a4000000 0xbc847f1ffcf8047f 0xde423f8ffe7c023f

def z622 : W := mkw 0x8def6f931bfdb000 0xc6f7b7c98dfed800 0xfbffff131ffff800 0x7dffff898ffffc00

def z623 : W := mkw 0x89ce450003d93000 0x44e7228001ec9800 0xf3fc470003f83800 0x79fe238001fc1c00

def z624 : W := mkw 0x4ff7e4fab6836ee0 0xa7fbf27d5b41b770 0xdffbc0f0ff87ffe0 0x6ffde0787fc3fff0

def z625 : W := mkw 0x89ef6d0027ffbc2a 0x44f7b68013ffde15 0xfbffff0003fffc7f 0xfdffff8001fffe3f

def z626 : W := mkw 0xa9ff64da03d1a354 0x54ffb26d01e8d1aa 0xf7ff80ff03f9c7ff 0xfbffc07f81fce3ff

def z627 : W := mkw 0x0000000002812000 0x0000000001409000 0x100000000387f800 0x0800000001c3fc00

def z628 : W := mkw 0x89ef640003d1a000 0x44f7b20001e8d000 0xf3ff800003f9c000 0x79ffc00001fce000

def z629 : W := mkw 0x33fdb8fee3f6c7dc 0x19fedc7f71fb63ee 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z630 : W := mkw 0x0180009000000000 0x00c0004800000000 0xc58000f000000000 0x62c0007800000000

def z631 : W := mkw 0x0dc6569758000000 0x86e32b4bac000000 0xac847f1ffc000000 0x56423f8ffe000000

def z632 : W := mkw 0x89ef640003d1a000 0x44f7b20001e8d000 0xdbfbc0000387f800 0x6dfde00001c3fc00

def z633 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x22fc001f00f8007f 0x917e000f807c003f

def z634 : W := mkw 0x0000000000000000 0x0000000000000000 0x0084001300980066 0x80420009804c0033

def z635 : W := mkw 0x1ffffeffd9648118 0x8fffff7fecb2408c 0xeffffffffc600019 0x77fffffffe30000c

def z636 : W := mkw 0x4582c9b0b6af7eea 0x22c164d85b57bf75 0xdd83c0f0ffffffff 0xeec1e0787fffffff

def z637 : W := mkw 0x01cc000003d00000 0x00e6000001e80000 0xf7fc001f03f8047f 0xfbfe000f81fc023f

def z638 : W := mkw 0x0865240000000000 0x0432920000000000 0x227c3f0000000000 0x113e1f8000000000

def z639 : W := mkw 0x321090fee00247dc 0x1908487f700123ee 0x040000ffe00007ff 0x8200007ff00003ff

def z640 : W := mkw 0x000012056c020c2a 0x00000902b6010615 0x9c80401ffc863c7f 0xce40200ffe431e3f

def z641 : W := mkw 0x89e7650002993000 0x44f3b280014c9800 0xebffff0000983800 0x75ffff80004c1c00

def z642 : W := mkw 0x1221b824e026c488 0x0910dc1270136244 0xbc03b80ce067c419 0x5e01dc067033e20c

def z643 : W := mkw 0x20101bdf6c2e1f7e 0x10080defb6170fbf 0xbc847ffffcfe3fff 0xde423ffffe7f1fff

def z644 : W := mkw 0x00000900242e1c20 0x0000048012170e10 0xbc847f10fcfe3c60 0x5e423f887e7f1e30

def z645 : W := mkw 0x00001b05482c1000 0x00000d82a4160800 0xbc847f1ffcfe3800 0x5e423f8ffe7f1c00

def z646 : W := mkw 0x458243911e893a62 0x22c121c88f449d31 0x008447131c983866 0x804223898e4c1c33

def z647 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x477800ff030007ff 0xa3bc007f818003ff

def z648 : W := mkw 0x2a7d364f49500114 0x953e9b27a4a8008a 0x227c3f0f0078001f 0x913e1f87803c000f

def z649 : W := mkw 0x8defedb093fdb000 0x46f7f6d849fed800 0xfffffff0fffff800 0x7ffffff87ffffc00

def z650 : W := mkw 0x100818046166c598 0x08040c0230b362cc 0xbc00380ce367c799 0x5e001c0671b3e3cc

def z651 : W := mkw 0xcdefe4b0b7d3eee0 0x66f7f2585be9f770 0xdffbc0f0ff87ffe0 0x6ffde0787fc3fff0

def z652 : W := mkw 0x1231b86ce026c488 0x0918dc3670136244 0xef7bb8ece007c000 0x77bddc767003e000

def z653 : W := mkw 0x4582409036836ee0 0x22c120481b41b770 0x108040101f87ffe0 0x084020080fc3fff0

def z654 : W := mkw 0x8000010002993000 0x40000080014c9800 0x0000000000983800 0x00000000004c1c00

def z655 : W := mkw 0x327d384e4174811c 0x193e9c2720ba408e 0x227c380f0078001f 0x913e1c07803c000f

def z656 : W := mkw 0xcdefedb093fdf2c0 0x66f7f6d849fef960 0xfbffffe003fffb80 0x7dfffff001fffdc0

def z657 : W := mkw 0x0029280001648000 0x0014940000b24000 0x2278380000600000 0x113c1c0000300000

def z658 : W := mkw 0x0221b024c0000000 0x0110d81260000000 0x0803b800e0000000 0x0401dc0070000000

def z659 : W := mkw 0x0008080001648000 0x0004040000b24000 0x100000000367c000 0x0800000001b3e000

def z660 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x28047f0ffc7e381f 0x94023f87fe3f1c0f

def z661 : W := mkw 0x89c647010e993822 0x44e32380874c9c11 0x008447131c983866 0x804223898e4c1c33

def z662 : W := mkw 0x1210986ce0264598 0x09084c36701322cc 0xbc0038ece0660799 0x5e001c76703303cc

def z663 : W := mkw 0x0239b86cc1648000 0x011cdc3660b24000 0xff7bb8ece367c000 0x7fbddc7671b3e000

def z664 : W := mkw 0x4402c020b6836ee0 0x220160105b41b770 0x1803c000ff87ffe0 0x0c01e0007fc3fff0

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0xd50000e003000780 0x6a800070018003c0

def z666 : W := mkw 0x89a36d0002adb000 0x44d1b6800156d800 0xd983ff000387f800 0x6cc1ff8001c3fc00

def z667 : W := mkw 0x44008020b4024ca0 0x220040105a012650 0x00000000fc000000 0x000000007e000000

def z668 : W := mkw 0x0180009026820e60 0x00c0004813410730 0xdd8040f0ff863fe0 0x6ec020787fc31ff0

def z669 : W := mkw 0x061092ffd8000000 0x8308497fec000000 0xac847ffffc000000 0x56423ffffe000000

def z670 : W := mkw 0x0000180464260c28 0x00000c0232130614 0xbc80781cfce63c79 0x5e403c0e7e731e3c

def z671 : W := mkw 0x01ab680003e5a000 0x00d5b40001f2d000 0xfbfbf80003e7f800 0x7dfdfc0001f3fc00

def z672 : W := mkw 0x0008000001400110 0x0004000000a00088 0x1000000003600799 0x0800000001b003cc

def z673 : W := mkw 0x5792d0fcf6836ff8 0x2bc9687e7b41b7fc 0xdd83c0fcff87fff9 0x6ec1e07e7fc3fffc

def z674 : W := mkw 0x261092ffd8000354 0x9308497fec0001aa 0x040000fffc0007ff 0x8200007ffe0003ff

def z675 : W := mkw 0x0239b06cc1400110 0x011cd83660a00088 0xff7bb8ece3600799 0x7fbddc7671b003cc

def z676 : W := mkw 0x00000900242e1c2a 0x0000048012170e15 0x9c804010fcfe3c7f 0xce4020087e7f1e3f

def z677 : W := mkw 0x0010004800000110 0x0008002400000088 0x040000ec00000799 0x02000076000003cc

def z678 : W := mkw 0xa9ff6d4a03fdb114 0x54ffb6a501fed88a 0xfbffff0f03fff81f 0xfdffff8781fffc0f

def z679 : W := mkw 0x8fffedfa93fdb000 0xc7fff6fd49fed800 0xfbffffe003fff800 0x7dfffff001fffc00

def z680 : W := mkw 0x33fd38de43f4835c 0x19fe9c6f21fa41ae 0xf7fc38ff03f807ff 0xfbfe1c7f81fc03ff

def z681 : W := mkw 0x0ff7e6fb98000000 0x87fbf37dcc000000 0x43ffc7f31c000000 0x21ffe3f98e000000

def z682 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xf77800ec03600799 0x7bbc007601b003cc

def z683 : W := mkw 0x205c1b4f497c111e 0x102e0da7a4be088f 0x227c3f0f0078001f 0x913e1f87803c000f

def z684 : W := mkw 0x0008000003d00000 0x0004000001e80000 0x1000000003f80000 0x0800000001fc0000

def z685 : W := mkw 0x00001b05482c100a 0x00000d82a4160805 0xac847f1ffc78001f 0xd6423f8ffe3c000f

def z686 : W := mkw 0x0000180460260408 0x00000c0230130204 0xbc84381fe0fe047f 0xde421c0ff07f023f

def z687 : W := mkw 0x21dc09da03fc1354 0x10ee04ed01fe09aa 0xfffc7fff03fe3fff 0xfffe3fff81ff1fff

def z688 : W := mkw 0xa9ff64da03d1a354 0x54ffb26d01e8d1aa 0x437b80e00301c380 0x21bdc0700180e1c0

def z689 : W := mkw 0xa9fd2dda03fc9354 0x54fe96ed01fe49aa 0xf7fc3fff03f807ff 0xfbfe1fff81fc03ff

def z690 : W := mkw 0x21dc1bdf4bfc135e 0x10ee0defa5fe09af 0xf7fc3fff03f807ff 0xfbfe1fff81fc03ff

def z691 : W := mkw 0x4ff7e4fa928162c0 0xa7fbf27d4940b160 0x437b80e00301c380 0x21bdc0700180e1c0

def z692 : W := mkw 0x018080b0a28246c0 0x00c0405851412360 0xdd8380f0e387c7e0 0x6ec1c07871c3e3f0

def z693 : W := mkw 0x89efed20a3fff480 0x44f7f69051fffa40 0xffffffe0e3ffff80 0x7ffffff071ffffc0

def z694 : W := mkw 0x0000009000000240 0x0000004800000120 0x040000f0000007e0 0x02000078000003f0

def z695 : W := mkw 0x0bf536df48000000 0x85fa9b6fa4000000 0xe7fc3fff00000000 0x73fe1fff80000000

def z696 : W := mkw 0x458080b0b6824ee0 0x22c040585b412770 0xd58000f0ff8007e0 0x6ac000787fc003f0

def z697 : W := mkw 0x61dc00da27d36ff4 0x30ee006d13e9b7fa 0xf7fc00ff03ffffff 0xfbfe007f81ffffff

def z698 : W := mkw 0x0000010004081822 0x0000008002040c11 0x0000000000983866 0x80000000004c1c33

def z699 : W := mkw 0x0000000000000000 0x0000000000000000 0x9880400000863800 0x4c40200000431c00

def z700 : W := mkw 0x0180009002800240 0x00c0004801400120 0x0080001000800060 0x0040000800400030

def z701 : W := mkw 0x0dc6c6b398000000 0x86e36359cc000000 0xcd87c7f3fc000000 0x66c3e3f9fe000000

def z702 : W := mkw 0x09f764da00000000 0x04fbb26d00000000 0xefffffff00000000 0x77ffffff80000000

def z703 : W := mkw 0x1a7d3e4f49648118 0x8d3e9f27a4b2408c 0x227c3f0f00600019 0x113e1f878030000c

def z704 : W := mkw 0x4000000024024ee0 0x2000000012012770 0x00000000000007e0 0x00000000000003f0

def z705 : W := mkw 0x0231bb6dec2e1c2a 0x0118ddb6f6170e15 0xfffffffffcfe3c7f 0xfffffffffe7f1e3f

def z706 : W := mkw 0x01cc1b056ffe1c2a 0x00e60d82b7ff0e15 0xfffc7f1ffffe3c7f 0xfffe3f8fffff1e3f

def z707 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x4bffff00039ff800 0x25ffff8001cffc00

def z708 : W := mkw 0xcdc6c4b0b6936ee0 0x66e362585b49b770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z709 : W := mkw 0x89e76d0002adb000 0x44f3b6800156d800 0xfbffff000387f800 0x7dffff8001c3fc00

def z710 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xeb7bb8e00301c380 0x75bddc700180e1c0

def z711 : W := mkw 0x0e77f6ffd8000000 0x873bfb7fec000000 0x2e7ffffffc000000 0x173ffffffe000000

def z712 : W := mkw 0x89ef640003d1a000 0x44f7b20001e8d000 0xfbffff000387f800 0x7dffff8001c3fc00

def z713 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xfffffffffcf80000 0x7ffffffffe7c0000

def z714 : W := mkw 0x33e5b8b6e2b6c6cc 0x19f2dc5b715b6366 0x0887b813e09fc066 0x8443dc09f04fe033

def z715 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xebffff000307f800 0x75ffff800183fc00

def z716 : W := mkw 0x9a23ff25ec2ffcaa 0x4d11ff92f617fe55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z717 : W := mkw 0xcdc6459012993240 0x66e322c8094c9920 0x0084470000983800 0x00422380004c1c00

def z718 : W := mkw 0x0fe7f6b7d8000000 0x87f3fb5bec000000 0xebffff13fc000000 0x75ffff89fe000000

def z719 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xeffffffffc78001f 0xf7fffffffe3c000f

def z720 : W := mkw 0x0ff7f6ffd800000a 0x87fbfb7fec000005 0xeffffffffc00001f 0xf7fffffffe00000f

def z721 : W := mkw 0x4dc65f977eaf3e6a 0xa6e32fcbbf579f35 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z722 : W := mkw 0x886f6d0003fdb000 0x4437b68001fed800 0x3a7fff0003fff800 0x1d3fff8001fffc00

def z723 : W := mkw 0x0054124f48000000 0x002a0927a4000000 0xaefc7f1ffc000000 0x577e3f8ffe000000

def z724 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xfffc7fff03f807ff 0xfffe3fff81fc03ff

def z725 : W := mkw 0xa8336dda002db354 0x5419b6ed0016d9aa 0x0c03ffff0007ffff 0x8601ffff8003ffff

def z726 : W := mkw 0x21c6409202912244 0x10e3204901489122 0x0084401300983866 0x80422009804c1c33

def z727 : W := mkw 0x0ff7edfab42e1c2a 0x87fbf6fd5a170e15 0x537b80e000fe3c7f 0xa9bdc070007f1e3f

def z728 : W := mkw 0xa9de44da03d12354 0x54ef226d01e891aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z729 : W := mkw 0x1239ba6ded66cdba 0x091cdd36f6b366dd 0xfffbf8ffffe7ffff 0xfffdfc7ffff3ffff

def z730 : W := mkw 0x1239bb6de96ed59a 0x091cddb6f4b76acd 0xffffffefe3ffff9f 0xfffffff7f1ffffcf

def z731 : W := mkw 0xa9c64d9202bd3244 0x54e326c9015e9922 0xbc847f1f00fe3c7f 0xde423f8f807f1e3f

def z732 : W := mkw 0x4ff7f6ffd8016080 0xa7fbfb7fec00b040 0xeffffffffc01c000 0x77fffffffe00e000

def z733 : W := mkw 0x2ff7f6ffd8100004 0x97fbfb7fec080002 0xeffffffffc180006 0xf7fffffffe0c0003

def z734 : W := mkw 0x1229b824e166c488 0x0914dc1270b36244 0xff7bb8e0e367c780 0x7fbddc7071b3e3c0

def z735 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xfbffff0003fffc7f 0xfdffff8001fffe3f

def z736 : W := mkw 0x29de44da03d00354 0x14ef226d01e801aa 0xf7fc47ff03f807ff 0xfbfe23ff81fc03ff

def z737 : W := mkw 0x0ff7f6ffda800000 0x87fbfb7fed400000 0xffffffffff800000 0x7fffffffffc00000

def z738 : W := mkw 0x1239a868a166c598 0x091cd43450b362cc 0xfb7bb8e00367c799 0x7dbddc7001b3e3cc

def z739 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xff7bb8ece3ffc7ff 0xffbddc7671ffe3ff

def z740 : W := mkw 0x886d2d00017c9000 0x4436968000be4800 0xfbffff0003fff800 0x7dffff8001fffc00

def z741 : W := mkw 0x1dce4e933966c598 0x8ee727499cb362cc 0x108447131f67c799 0x084223898fb3e3cc

def z742 : W := mkw 0x9a7d3f4f497c9118 0xcd3e9fa7a4be488c 0x227c3f0f00780019 0x113e1f87803c000c

def z743 : W := mkw 0x6fffe4fa93d163d4 0xb7fff27d49e8b1ea 0x437b80e00301c380 0x21bdc0700180e1c0

def z744 : W := mkw 0x645ec06ab5536db4 0x322f60355aa9b6da 0x2a7fc00ffc7ff81f 0x953fe007fe3ffc0f

def z745 : W := mkw 0x1239a068a142c590 0x091cd03450a162c8 0xff7b80ece367c799 0x7fbdc07671b3e3cc

def z746 : W := mkw 0x1239b06ce142c598 0x091cd83670a162cc 0xf77b80ece361c799 0x7bbdc07671b0e3cc

def z747 : W := mkw 0x9bd6d56ce29b7598 0x4deb6ab6714dbacc 0x048447ece0983f99 0x024223f6704c1fcc

def z748 : W := mkw 0x01dc004803d00110 0x00ee002401e80088 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z749 : W := mkw 0x4582dbb5daad72ca 0x22c16ddaed56b965 0x6107bfef0379c39f 0xb083dff781bce1cf

def z750 : W := mkw 0x0039204801408110 0x001c902400a04088 0xf77b80ec0361c799 0x7bbdc07601b0e3cc

def z751 : W := mkw 0x0fb3f6fdd8000000 0x87d9fb7eec000000 0xeffbfffcfc000000 0x77fdfffe7e000000

def z752 : W := mkw 0x0ff7f66dd8000000 0x87fbfb36ec000000 0xefffffecfc000000 0x77fffff67e000000

def z753 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xfd87c0ffff87ffe0 0x7ec3e07fffc3fff0

def z754 : W := mkw 0x1239b06cc140c190 0x091cd83660a060c8 0xff7bb8ece361c799 0x7fbddc7671b0e3cc

def z755 : W := mkw 0x0582c0b0b4024ca0 0x02c160585a012650 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z756 : W := mkw 0x0de7769758000000 0x86f3bb4bac000000 0xefffff1ffc000000 0x77ffff8ffe000000

def z757 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xfd87ff1ffffffc7f 0xfec3ff8ffffffe3f

def z758 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xfd83c0fcffe7fff9 0x7ec1e07e7ff3fffc

def z759 : W := mkw 0x65de40da13d12354 0x32ef206d09e891aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z760 : W := mkw 0x2018004803d00354 0x100c002401e801aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z761 : W := mkw 0x0a75364f48000000 0x853a9b27a4000000 0x2a7c7f0ffc000000 0x153e3f87fe000000

def z762 : W := mkw 0x1239b96ce16ed598 0x091cdcb670b76acc 0xff7bffece367ff99 0x7fbdfff671b3ffcc

def z763 : W := mkw 0x86189bffdbfdb000 0xc30c4dffedfed800 0x140000fffffff800 0x0a00007ffffffc00

def z764 : W := mkw 0x1239a868a166c598 0x091cd43450b362cc 0xf77b80ec0367c799 0x7bbdc07601b3e3cc

def z765 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7fffefff7fff9f 0xffbffff7ffbfffcf

def z766 : W := mkw 0x0582c0b0b2836480 0x02c160585941b240 0xdd83c0f0ff87ff80 0x6ec1e0787fc3ffc0

def z767 : W := mkw 0x21dc00da03d12354 0x10ee006d01e891aa 0xf7fc00ff03ffffff 0xfbfe007f81ffffff

def z768 : W := mkw 0x882b6d00016db000 0x4415b68000b6d800 0xfbffff0003fff800 0x7dffff8001fffc00

def z769 : W := mkw 0x1239b86cc164c198 0x091cdc3660b260cc 0xf77bb8ec0361c799 0x7bbddc7601b0e3cc

def z770 : W := mkw 0x4ff7f6ffda8162c0 0xa7fbfb7fed40b160 0xffffffffff81c7e0 0x7fffffffffc0e3f0

def z771 : W := mkw 0x57bb78dc57e5ab78 0x2bddbc6e2bf2d5bc 0x22f8781c1ce03879 0x117c3c0e0e701c3c

def z772 : W := mkw 0x0018004801400110 0x000c002400a00088 0xff7b80ec0367c799 0x7fbdc07601b3e3cc

def z773 : W := mkw 0x8ff7f6ffda912000 0xc7fbfb7fed489000 0xeffffffffc000000 0x77fffffffe000000

def z774 : W := mkw 0x2e2bf625dbd00354 0x9715fb12ede801aa 0x1803ff00fff807ff 0x8c01ff807ffc03ff

def z775 : W := mkw 0x80080900257e9c2a 0x4004048012bf4e15 0x1000000000fe3c7f 0x88000000007f1e3f

def z776 : W := mkw 0x2ff7f6ffda800354 0x97fbfb7fed4001aa 0xffffffffff8007ff 0xffffffffffc003ff

def z777 : W := mkw 0x1239b26dc940c190 0x091cd936e4a060c8 0xefffffffff01c380 0x77ffffffff80e1c0

def z778 : W := mkw 0x9008090027fffdba 0x4804048013fffedd 0x1000000003ffffff 0x8800000001ffffff

def z779 : W := mkw 0x321092ffec024ffe 0x1908497ff60127ff 0x040000fffc0007ff 0x8200007ffe0003ff

def z780 : W := mkw 0x01d409da242e1c2a 0x00ea04ed12170e15 0xf7fc00ff00fe3c7f 0xfbfe007f807f1e3f

def z781 : W := mkw 0x201800da01400354 0x100c006d00a001aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z782 : W := mkw 0x21d400da00000354 0x10ea006d000001aa 0xf7fc00ff00f807ff 0xfbfe007f807c03ff

def z783 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xcd83c0f0ff07fb80 0x66c1e0787f83fdc0

def z784 : W := mkw 0x1239b96ce16ed59a 0x091cdcb670b76acd 0xff7bb8ece37fc79f 0xffbddc7671bfe3cf

def z785 : W := mkw 0x0018806881404190 0x000c403440a020c8 0x437b80e00301c380 0x21bdc0700180e1c0

def z786 : W := mkw 0x0fe7f625d8000000 0x87f3fb12ec000000 0x4b7bff00fc000000 0x25bdff807e000000

def z787 : W := mkw 0x01ab690003edb000 0x00d5b48001f6d800 0xfbffff0003fff800 0x7dffff8001fffc00

def z788 : W := mkw 0xcdc6449016912a60 0x66e322480b489530 0x008040101c803860 0x004020080e401c30

def z789 : W := mkw 0x018080b0a6824ee0 0x00c0405853412770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z790 : W := mkw 0x1239b86cc164c198 0x091cdc3660b260cc 0xfb7bb8ec0367c399 0x7dbddc7601b3e1cc

def z791 : W := mkw 0x205c004a03d00354 0x102e002501e801aa 0xf77c00ef03f807ff 0xfbbe007781fc03ff

def z792 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xffff80ff03ffc7ff 0xffffc07f81ffe3ff

def z793 : W := mkw 0x01d400da02800240 0x00ea006d01400120 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z794 : W := mkw 0x9a7d3f4d497c911a 0x4d3e9fa6a4be488d 0x227c3f0f0078001f 0x913e1f87803c000f

def z795 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x4f7bb8ece307c799 0x27bddc767183e3cc

def z796 : W := mkw 0x89ef6d0003fdb00a 0x44f7b68001fed805 0xfbffff0003fff81f 0xfdffff8001fffc0f

def z797 : W := mkw 0x8029290003fdb000 0x4014948001fed800 0xfbffff0003fff800 0x7dffff8001fffc00

def z798 : W := mkw 0x89e76d0002bdb000 0x44f3b680015ed800 0xebffff00009ff800 0x75ffff80004ffc00

def z799 : W := mkw 0x4ff7f6ffda812240 0xa7fbfb7fed409120 0xeffffffffc000000 0x77fffffffe000000

def z800 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xff7fb8efe37fc79f 0xffbfdc77f1bfe3cf

def z801 : W := mkw 0x09ef6d00016c9000 0x04f7b68000b64800 0xfbffff0003fff800 0x7dffff8001fffc00

def z802 : W := mkw 0x4a75364f6e836ee0 0xa53a9b27b741b770 0x327c3f0f0387ffe0 0x193e1f8781c3fff0

def z803 : W := mkw 0x0ff7f6ffda900000 0x87fbfb7fed480000 0xeffffffffc980000 0x77fffffffe4c0000

def z804 : W := mkw 0x0239b86ce166c480 0x011cdc3670b36240 0xff7bb8ece367c780 0x7fbddc7671b3e3c0

def z805 : W := mkw 0x1239ba6fe966c598 0x891cdd37f4b362cc 0xff7bb8efe367c799 0x7fbddc77f1b3e3cc

def z806 : W := mkw 0x1239bb6de96ed598 0x091cddb6f4b76acc 0xffffffffffffff99 0x7fffffffffffffcc

def z807 : W := mkw 0x0de7e42090000000 0x06f3f21048000000 0xebffff00fc000000 0x75ffff807e000000

def z808 : W := mkw 0x2ff7f6ffda900244 0x97fbfb7fed480122 0xfffffffffcf8047f 0xfffffffffe7c023f

def z809 : W := mkw 0x1239b96ce56eddba 0x091cdcb672b76edd 0xfffbf8fcffffffff 0xfffdfc7e7fffffff

def z810 : W := mkw 0x886f6d00017db000 0x4437b68000bed800 0xfb7fff00037ff800 0x7dbfff8001bffc00

def z811 : W := mkw 0x01dc00da01400110 0x00ee006d00a00088 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z812 : W := mkw 0x89ef76056fd3ac2a 0x44f7bb02b7e9d615 0x477b801fff01c47f 0xa3bdc00fff80e23f

def z813 : W := mkw 0x01ed290003fc9000 0x00f6948001fe4800 0xfbffff0003fff800 0x7dffff8001fffc00

def z814 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xfffffffffc800460 0x7ffffffffe400230

def z815 : W := mkw 0x0029280001648000 0x0014940000b24000 0xff7bb8e00367c780 0x7fbddc7001b3e3c0

def z816 : W := mkw 0x1239a968a56eddba 0x091cd4b452b76edd 0x537b80e003ffffff 0xa9bdc07001ffffff

def z817 : W := mkw 0x49e7640026836ee0 0x24f3b2001341b770 0xfbffff000387ffe0 0x7dffff8001c3fff0

def z818 : W := mkw 0x1239bb6de96ed59a 0x091cddb6f4b76acd 0xff7bbfece367c799 0x7fbddff671b3e3cc

def z819 : W := mkw 0x9239b96ce17ed598 0x491cdcb670bf6acc 0xff7bb8ece37fc799 0x7fbddc7671bfe3cc

def z820 : W := mkw 0x1239b86ce566cdb8 0x091cdc3672b366dc 0xfffff8ffffffffff 0xfffffc7fffffffff

def z821 : W := mkw 0x0e33f66dd8000000 0x8719fb36ec000000 0x4b7bffe0fc000000 0x25bdfff07e000000

def z822 : W := mkw 0x45c6409216812a60 0x22e320490b409530 0x008440131c803860 0x004220098e401c30

def z823 : W := mkw 0x89ef6d0003fdb240 0x44f7b68001fed920 0xfbffff0003ffffe0 0x7dffff8001fffff0

def z824 : W := mkw 0x1ff7f6ffd8004190 0x8ffbfb7fec0020c8 0xeffffffffc000380 0x77fffffffe0001c0

def z825 : W := mkw 0x0e77f66fd8000000 0x873bfb37ec000000 0xef7fffeffc000000 0x77bffff7fe000000

def z826 : W := mkw 0x0e33f6ffd8000000 0x8719fb7fec000000 0xef7bfffffc000000 0x77bdfffffe000000

def z827 : W := mkw 0x0ff776df58000000 0x87fbbb6fac000000 0xaefc7f1ffc000000 0x577e3f8ffe000000

def z828 : W := mkw 0x0231324d48000000 0x01189926a4000000 0xaefc7f1ffc000000 0x577e3f8ffe000000

def z829 : W := mkw 0x1e23ff25fc2edcaa 0x8f11ff92fe176e55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z830 : W := mkw 0x4582c0b0b6836eea 0x22c160585b41b775 0xdd83c0f0ff87ffff 0xeec1e0787fc3ffff

def z831 : W := mkw 0x019800d803c00350 0x00cc006c01e001a8 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z832 : W := mkw 0xcdef6d9013fdb240 0x66f7b6c809fed920 0xfbffff0003fff800 0x7dffff8001fffc00

def z833 : W := mkw 0x561092fdfc024ffa 0x2b08497efe0127fd 0x040000fffc0007ff 0x8200007ffe0003ff

def z834 : W := mkw 0x10080900256eddba 0x0804048012b76edd 0x100000000367ff99 0x0800000001b3ffcc

def z835 : W := mkw 0x00008020a4024ca0 0x0000401052012650 0xdd03c0e0ff07ff80 0x6e81e0707f83ffc0

def z836 : W := mkw 0x4402c020b6836ee0 0x220160105b41b770 0xdd03c0e0ff87ffe0 0x6e81e0707fc3fff0

def z837 : W := mkw 0x1239a8688164c198 0x091cd43440b260cc 0x437b80e00361c399 0x21bdc07001b0e1cc

def z838 : W := mkw 0xcc6dadb0b57edee0 0x6636d6d85abf6f70 0x267c3ff0fc7807e0 0x133e1ff87e3c03f0

def z839 : W := mkw 0x1239ba6de966c598 0x091cdd36f4b362cc 0xff7fbfefe367c799 0x7fbfdff7f1b3e3cc

def z840 : W := mkw 0x3008090027fedffe 0x1804048013ff6fff 0x1000000003ffffff 0x8800000001ffffff

def z841 : W := mkw 0x4402c0b0b4036ee0 0x220160585a01b770 0xdd03c0f0ff07ffe0 0x6e81e0787f83fff0

def z842 : W := mkw 0x1239b86ce566cdba 0x091cdc3672b366dd 0xff7bb8ece367c7ff 0xffbddc7671b3e3ff

def z843 : W := mkw 0xcc23ff25fc2ffcaa 0x6611ff92fe17fe55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z844 : W := mkw 0x0ff7e4fa90000000 0x87fbf27d48000000 0xeffffff0fc000000 0x77fffff87e000000

def z845 : W := mkw 0x201800da03d00354 0x100c006d01e801aa 0xf77800ff03f807ff 0xfbbc007f81fc03ff

def z846 : W := mkw 0x000012056c020c20 0x00000902b6010610 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z847 : W := mkw 0xedffe4fa93d1e3d4 0x76fff27d49e8f1ea 0x437b80e00301c380 0x21bdc0700180e1c0

def z848 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xfffbfffcffe7fff9 0x7ffdfffe7ff3fffc

def z849 : W := mkw 0x4582c0b0928162c0 0x22c160584940b160 0xdd83c0f0ff87fb80 0x6ec1e0787fc3fdc0

def z850 : W := mkw 0x4dc6c4b2b6836ee0 0xa6e362595b41b770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z851 : W := mkw 0x205c00da03d00354 0x102e006d01e801aa 0x367c00ff03f807ff 0x9b3e007f81fc03ff

def z852 : W := mkw 0x00392948016c9110 0x001c94a400b64888 0xffffffff03ffffff 0xffffffff81ffffff

def z853 : W := mkw 0x0231a06880004080 0x0118d03440002040 0x437b80e00301c380 0x21bdc0700180e1c0

def z854 : W := mkw 0x461092fffc024ca0 0xa308497ffe012650 0x040000fffc000000 0x0200007ffe000000

def z855 : W := mkw 0xa9ef6d0003fdb114 0x54f7b68001fed88a 0xfbffff0003fff81f 0xfdffff8001fffc0f

def z856 : W := mkw 0x2ff7f6ffda900244 0x97fbfb7fed480122 0xffffffffff9807e6 0xffffffffffcc03f3

def z857 : W := mkw 0x0029bb25ed6edcaa 0x0014dd92f6b76e55 0xffffffffffffffff 0xffffffffffffffff

def z858 : W := mkw 0x1239b86cc164c198 0x091cdc3660b260cc 0xef7bb8ece361c399 0x77bddc7671b0e1cc

def z859 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xdbfbff000387f800 0x6dfdff8001c3fc00

def z860 : W := mkw 0x1239ba6ded66cdb8 0x091cdd36f6b366dc 0xffffffffffe7fff9 0x7ffffffffff3fffc

def z861 : W := mkw 0x0e75b66fd8000000 0x873adb37ec000000 0x227c3f0ffc000000 0x113e1f87fe000000

def z862 : W := mkw 0x4402c020b4036ca0 0x220160105a01b650 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z863 : W := mkw 0x21dc00da01500354 0x10ee006d00a801aa 0xe7fc00ff007807ff 0xf3fe007f803c03ff

def z864 : W := mkw 0x65c6409216912a64 0x32e320490b489532 0x008040101c803860 0x004020080e401c30

def z865 : W := mkw 0x1239a868a166c590 0x091cd43450b362c8 0xff7bb8e0e367c780 0x7fbddc7071b3e3c0

def z866 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xdd87c0f3ff9fffe6 0xeec3e079ffcffff3

def z867 : W := mkw 0x6008090027ff7ffe 0x3004048013ffbfff 0x1000000003ffffff 0x8800000001ffffff

def z868 : W := mkw 0x0239b06ce1424590 0x011cd83670a122c8 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z869 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xfbffff0f03fff81f 0xfdffff8781fffc0f

def z870 : W := mkw 0x205c004a01500114 0x102e002500a8008a 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z871 : W := mkw 0xaa7d3f4f497c9114 0xd53e9fa7a4be488a 0x227c3f0f0078001f 0x913e1f87803c000f

def z872 : W := mkw 0x4dc647931e893a62 0xa6e323c98f449d31 0x008447131c983866 0x804223898e4c1c33

def z873 : W := mkw 0xa9ef6d0003fdb354 0x54f7b68001fed9aa 0xffffff1f03ffffff 0xffffff8f81ffffff

def z874 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xfffbb8fce3e7c7f9 0x7ffddc7e71f3e3fc

def z875 : W := mkw 0xcdc647911e993a62 0x66e323c88f4c9d31 0x008447131c983866 0x804223898e4c1c33

def z876 : W := mkw 0x00001b054c2c182a 0x00000d82a6160c15 0xac847f1ffcf8387f 0xd6423f8ffe7c1c3f

def z877 : W := mkw 0xa9ef6d0203fdb004 0x54f7b68101fed802 0xfbffff0303fff806 0xfdffff8181fffc03

def z878 : W := mkw 0x65c6c0b2b6936ee4 0x32e360595b49b772 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z879 : W := mkw 0x0ff5b6ffd8000000 0x87fadb7fec000000 0xe7fc3ffffc000000 0x73fe1ffffe000000

def z880 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xfbffff1303fff866 0xfdffff8981fffc33

def z881 : W := mkw 0x1ff7f6ffd800c080 0x8ffbfb7fec006040 0xeffffffffc01c000 0x77fffffffe00e000

def z882 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xfb7bb8e0e367c380 0x7dbddc7071b3e1c0

def z883 : W := mkw 0x4402c0b0b6836ee0 0x220160585b41b770 0x1c03c0f0ff87ffe0 0x0e01e0787fc3fff0

def z884 : W := mkw 0x01c4120548000000 0x00e20902a4000000 0xeffc7f1ffc000000 0x77fe3f8ffe000000

def z885 : W := mkw 0x99ef6d0003fdb118 0x4cf7b68001fed88c 0xfbffff0003fff819 0x7dffff8001fffc0c

def z886 : W := mkw 0x1239a8688164c190 0x091cd43440b260c8 0x537b80e00367c380 0x29bdc07001b3e1c0

def z887 : W := mkw 0x0bf7f66dc8000000 0x05fbfb36e4000000 0xeffffffffc000000 0x77fffffffe000000

def z888 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xdd03c0e0ff07ff80 0x6e81e0707f83ffc0

def z889 : W := mkw 0x20080900257e1d3e 0x1004048012bf0e9f 0x1000000000fe3c7f 0x88000000007f1e3f

def z890 : W := mkw 0x07b3f2fdd8000000 0x03d9f97eec000000 0xeffffffffc000000 0x77fffffffe000000

def z891 : W := mkw 0x1210926dec024dba 0x09084936f60126dd 0x040000ecfc000799 0x020000767e0003cc

def z892 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xffffffffff67ff99 0x7fffffffffb3ffcc

def z893 : W := mkw 0xa9ef6d0003fdb244 0x54f7b68001fed922 0xfbffff0003fff866 0xfdffff8001fffc33

def z894 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xdd83c0ffff87ffff 0xeec1e07fffc3ffff

def z895 : W := mkw 0x0039284801648110 0x001c942400b24088 0xfb7bb8e00367c380 0x7dbddc7001b3e1c0

def z896 : W := mkw 0x0e33f66dd8000000 0x8719fb36ec000000 0x2a7bff0cfc000000 0x153dff867e000000

def z897 : W := mkw 0x1239a968816cd190 0x091cd4b440b668c8 0xfbffffe003fffb80 0x7dfffff001fffdc0

def z898 : W := mkw 0x5623fb25fc2ffcaa 0x2b11fd92fe17fe55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z899 : W := mkw 0x0039204801408110 0x001c902400a04088 0x437b80e00301c380 0x21bdc0700180e1c0

def z900 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0x537b80e00361c799 0x29bdc07001b0e3cc

def z901 : W := mkw 0x89ef6d00016db000 0x44f7b68000b6d800 0xfbffff000367f800 0x7dffff8001b3fc00

def z902 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x2affff0000fff800 0x157fff80007ffc00

def z903 : W := mkw 0x1239b86cc164c190 0x091cdc3660b260c8 0xff7bb8ece367c380 0x7fbddc7671b3e1c0

def z904 : W := mkw 0x2ff7f6ffda900244 0x97fbfb7fed480122 0xeffffffffc000000 0x77fffffffe000000

def z905 : W := mkw 0x65c643931e993a66 0x32e321c98f4c9d33 0x008447131c983866 0x804223898e4c1c33

def z906 : W := mkw 0x1239b96ce16ed598 0x091cdcb670b76acc 0xff7fbfece37fc799 0x7fbfdff671bfe3cc

def z907 : W := mkw 0x6582c0b0b6936ee4 0x32c160585b49b772 0xdd83c0f0ff9fffe6 0xeec1e0787fcffff3

def z908 : W := mkw 0x0631b2ffd8000000 0x8318d97fec000000 0xeffffffffc000000 0x77fffffffe000000

def z909 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0xfd847ffffffe3fff 0xfec23fffffff1fff

def z910 : W := mkw 0x1239b06ce142c598 0x091cd83670a162cc 0xef7bb8ece301c799 0x77bddc767180e3cc

def z911 : W := mkw 0x40008020a6836ee0 0x200040105341b770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z912 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffff0c03fffc19 0x7fffff8601fffe0c

def z913 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x4d03c0f0ff07ffe0 0x2681e0787f83fff0

def z914 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xfffffffffc863800 0x7ffffffffe431c00

def z915 : W := mkw 0x0029a8208164c080 0x0014d41040b26040 0xfb7bb8e00367c380 0x7dbddc7001b3e1c0

def z916 : W := mkw 0x45c6c0b0b6836ee0 0x22e360585b41b770 0xffffc0f0ff87ffe0 0x7fffe0787fc3fff0

def z917 : W := mkw 0x4dc6449212812240 0xa6e3224909409120 0x0000000000000000 0x0000000000000000

def z918 : W := mkw 0x0029a0208140c080 0x0014d01040a06040 0x437b80e00301c380 0x21bdc0700180e1c0

def z919 : W := mkw 0x0231b26dc8000000 0x0118d936e4000000 0xef7bffecfc000000 0x77bdfff67e000000

def z920 : W := mkw 0xc008090027fffeea 0x6004048013ffff75 0x1000000003ffffff 0x8800000001ffffff

def z921 : W := mkw 0x88236d00002db000 0x4411b6800016d800 0xeb7bff000007f800 0x75bdff800003fc00

def z922 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0x477b80ec0301c799 0x23bdc0760180e3cc

def z923 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xffffb8ffe367c799 0x7fffdc7ff1b3e3cc

def z924 : W := mkw 0xa008090027ffbf7e 0x5004048013ffdfbf 0x1000000003ffffff 0x8800000001ffffff

def z925 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0x637b80ec0361c399 0x31bdc07601b0e1cc

def z926 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xfd87fff0ff87ffe0 0x7ec3fff87fc3fff0

def z927 : W := mkw 0xa1dc00da03d1a354 0x50ee006d01e8d1aa 0xf7fc00ff03f9c7ff 0xfbfe007f81fce3ff

def z928 : W := mkw 0x10001b056c2edcaa 0x08000d82b6176e55 0xbc847f1ffcfffc7f 0xde423f8ffe7ffe3f

def z929 : W := mkw 0xcdc6449012912240 0x66e3224809489120 0x0000000000000000 0x0000000000000000

def z930 : W := mkw 0x65c6409212912244 0x32e3204909489122 0x0084001300980066 0x80420009804c0033

def z931 : W := mkw 0x1239b96ce56eddb8 0x091cdcb672b76edc 0xfffffffcfffffff9 0x7ffffffe7ffffffc

def z932 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffff1003fffc60 0x7fffff8801fffe30

def z933 : W := mkw 0x1239b06ce142c598 0x091cd83670a162cc 0xdf7b80ece307c799 0x6fbdc0767183e3cc

def z934 : W := mkw 0xadc647931a993244 0xd6e323c98d4c9922 0x008447131c983866 0x804223898e4c1c33

def z935 : W := mkw 0xa9ef6d9203fdb244 0x54f7b6c901fed922 0xfbffff0003fff800 0x7dffff8001fffc00

def z936 : W := mkw 0x65c6409236932e64 0x32e320491b499732 0xbc84401ffcfe3c7f 0xde42200ffe7f1e3f

def z937 : W := mkw 0x4ff7f6ffda8162c0 0xa7fbfb7fed40b160 0xffffffffff87fb80 0x7fffffffffc3fdc0

def z938 : W := mkw 0x1239ba6de966c598 0x091cdd36f4b362cc 0xffffffffffffc7ff 0xffffffffffffe3ff

def z939 : W := mkw 0x89ef6d0003fdb110 0x44f7b68001fed888 0xfbffff0003ffff99 0x7dffff8001ffffcc

def z940 : W := mkw 0x0231bb6dec2e5caa 0x0118ddb6f6172e55 0xffffffffffffffff 0xffffffffffffffff

def z941 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x28847f1ffcfe387f 0x94423f8ffe7f1c3f

def z942 : W := mkw 0x0ff7f6ffd8000110 0x87fbfb7fec000088 0xeffffffffc000799 0x77fffffffe0003cc

def z943 : W := mkw 0x1239ba6de966c598 0x091cdd36f4b362cc 0xff7bb8ffff67c799 0x7fbddc7fffb3e3cc

def z944 : W := mkw 0x0ff7f6ffd8004080 0x87fbfb7fec002040 0xefffffffff01c380 0x77ffffffff80e1c0

def z945 : W := mkw 0x09e7760548000000 0x04f3bb02a4000000 0xebffff00fc000000 0x75ffff807e000000

def z946 : W := mkw 0x0bf7764f48000000 0x85fbbb27a4000000 0xefffff1ffc000000 0x77ffff8ffe000000

def z947 : W := mkw 0x0231b26dec024ca0 0x0118d936f6012650 0xffffffffff87ffe0 0x7fffffffffc3fff0

def z948 : W := mkw 0x886d2d0003fdb000 0x4436968001fed800 0xfb7fbf0003fff800 0x7dbfdf8001fffc00

def z949 : W := mkw 0x8def6d9213fdb000 0xc6f7b6c909fed800 0xfbffff0003fff800 0x7dffff8001fffc00

def z950 : W := mkw 0x65c6409212912244 0x32e3204909489122 0x0000000000000000 0x0000000000000000

def z951 : W := mkw 0x1239a068a142c590 0x091cd03450a162c8 0x537b80e00307c780 0x29bdc0700183e3c0

def z952 : W := mkw 0x21de40da03d12354 0x10ef206d01e891aa 0xf7fc40ff03f83fff 0xfbfe207f81fc1fff

def z953 : W := mkw 0x161092fffc024dba 0x8b08497ffe0126dd 0x040000fffc0007ff 0x8200007ffe0003ff

def z954 : W := mkw 0x0e77f66fd8000000 0x873bfb37ec000000 0xaeffff1ffc000000 0x577fff8ffe000000

def z955 : W := mkw 0x1239a3698d48d9b2 0x091cd1b4c6a46cd9 0x43ffc7f31f99fbe6 0xa1ffe3f98fccfdf3

def z956 : W := mkw 0x882b6d00016db000 0x4415b68000b6d800 0x4b7bff000307f800 0x25bdff800183fc00

def z957 : W := mkw 0x8008090027ffbc20 0x4004048013ffde10 0x1000000003fffc60 0x0800000001fffe30

def z958 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x550380f0ff87ffe0 0x2a81c0787fc3fff0

def z959 : W := mkw 0x327d3b4f497c911e 0x193e9da7a4be488f 0x227c3f0f0078001f 0x913e1f87803c000f

def z960 : W := mkw 0x0182c020a6836ca0 0x00c160105341b650 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z961 : W := mkw 0x0de7e6b398000000 0x86f3f359cc000000 0xeffffff3fc000000 0x77fffff9fe000000

def z962 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x677fbffffc000000 0x33bfdffffe000000

def z963 : W := mkw 0x1029a820a166c598 0x0814d41050b362cc 0xff7bb8e0e367c799 0x7fbddc7071b3e3cc

def z964 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xd983c0e0ff87fb80 0x6cc1e0707fc3fdc0

def z965 : W := mkw 0x2ff7f6ffd8000354 0x97fbfb7fec0001aa 0xfffffffffcf807ff 0xfffffffffe7c03ff

def z966 : W := mkw 0x0dd656df58000000 0x86eb2b6fac000000 0xeffc7ffffc000000 0x77fe3ffffe000000

def z967 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xfffbf8ece3e7ff99 0x7ffdfc7671f3ffcc

def z968 : W := mkw 0x0010124d48000000 0x00080926a4000000 0xeffc7ffffc000000 0x77fe3ffffe000000

def z969 : W := mkw 0x1239b06ce142c590 0x091cd83670a162c8 0xff7bb8ece307c780 0x7fbddc767183e3c0

def z970 : W := mkw 0x1239bb6de96ed59a 0x091cddb6f4b76acd 0xffffffffff7fc79f 0xffffffffffbfe3cf

def z971 : W := mkw 0x205c00da01500354 0x102e006d00a801aa 0xb6fc00ff00f807ff 0xdb7e007f807c03ff

def z972 : W := mkw 0xa9c6449202912244 0x54e3224901489122 0x0084001300980066 0x80420009804c0033

def z973 : W := mkw 0x21de40da03d00354 0x10ef206d01e801aa 0xffffc0ff03f807ff 0xffffe07f81fc03ff

def z974 : W := mkw 0x89e76d00002db000 0x44f3b6800016d800 0xfbffff0000fff800 0x7dffff80007ffc00

def z975 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffffe003ffff80 0x7ffffff001ffffc0

def z976 : W := mkw 0x1a7d3f4f496c911a 0x8d3e9fa7a4b6488d 0x227c3f0f0078001f 0x913e1f87803c000f

def z977 : W := mkw 0x89ef6d00017db000 0x44f7b68000bed800 0xebffff00007ff800 0x75ffff80003ffc00

def z978 : W := mkw 0x0fe7f6b5d8000000 0x87f3fb5aec000000 0xeffffff0fc000000 0x77fffff87e000000

def z979 : W := mkw 0x0e33f66dd8000000 0x8719fb36ec000000 0xeffffffffc000000 0x77fffffffe000000

def z980 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xebffffe0fc000000 0x75fffff07e000000

def z981 : W := mkw 0x89ef6d9003fdb240 0x44f7b6c801fed920 0xffffffff03ffffff 0xffffffff81ffffff

def z982 : W := mkw 0x0231b06cc0004080 0x0118d83660002040 0xef7bb8ece301c380 0x77bddc767180e1c0

def z983 : W := mkw 0xcdc647931e993a60 0xe6e323c98f4c9d30 0x008447131c983860 0x004223898e4c1c30

def z984 : W := mkw 0x4dc6449216812a60 0xa6e322490b409530 0x008040101c803860 0x004020080e401c30

def z985 : W := mkw 0x00393b4d6d6e9d3a 0x001c9da6b6b74e9d 0xffffffffffffffff 0xffffffffffffffff

def z986 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x4983c0f0ff87fbe0 0x24c1e0787fc3fdf0

def z987 : W := mkw 0x89e76d00002db000 0x44f3b6800016d800 0x4b7bff000007f800 0x25bdff800003fc00

def z988 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xfffffffffc600419 0x7ffffffffe30020c

def z989 : W := mkw 0x4ff7f6ffd80042c0 0xa7fbfb7fec002160 0xeffffffffc000380 0x77fffffffe0001c0

def z990 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xef7bffecfc000000 0x77bdfff67e000000

def z991 : W := mkw 0x1239b86ce566cdb8 0x091cdc3672b366dc 0xff7bf8ecff67ff99 0x7fbdfc767fb3ffcc

def z992 : W := mkw 0x05d6d2ffd8000000 0x02eb697fec000000 0xeffffffffc000000 0x77fffffffe000000

def z993 : W := mkw 0x0021a020a0024480 0x0010d01050012240 0xff7bb8e0e307c780 0x7fbddc707183e3c0

def z994 : W := mkw 0x89c6459002993240 0x44e322c8014c9920 0x0084471000983860 0x00422388004c1c30

def z995 : W := mkw 0x0008090027fe1c2a 0x0004048013ff0e15 0x1000000003fe3c7f 0x8800000001ff1e3f

def z996 : W := mkw 0x0239b86cc1648110 0x011cdc3660b24088 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z997 : W := mkw 0xcdc65f957ebf3e6a 0x66e32fcabf5f9f35 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z998 : W := mkw 0x1239384c41648118 0x091c9c2620b2408c 0xff7bb8ec0367c799 0x7fbddc7601b3e3cc

def z999 : W := mkw 0x03f5b2ffc8000000 0x01fad97fe4000000 0xeffffffffc000000 0x77fffffffe000000

def z1000 : W := mkw 0xd008090027fffff8 0x6804048013fffffc 0x1000000003fffff9 0x0800000001fffffc

def z1001 : W := mkw 0x1239a068a142c590 0x091cd03450a162c8 0x477b80e0e301c780 0x23bdc0707180e3c0

def z1002 : W := mkw 0x0e75b6ffd8000000 0x873adb7fec000000 0xef7fbffffc000000 0x77bfdffffe000000

def z1003 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x6b7fff00037ff800 0x35bfff8001bffc00

def z1004 : W := mkw 0x641092fffc024ffe 0x3208497ffe0127ff 0x040000fffc0007ff 0x8200007ffe0003ff

def z1005 : W := mkw 0x0182409026832e60 0x00c1204813419730 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z1006 : W := mkw 0x00292900016c9000 0x0014948000b64800 0xfb7bff000367f800 0x7dbdff8001b3fc00

def z1007 : W := mkw 0x1239ba6ded66cdba 0x091cdd36f6b366dd 0xffffffffff67c7ff 0xffffffffffb3e3ff

def z1008 : W := mkw 0x2ff7f6ffda900354 0x97fbfb7fed4801aa 0xeffffffffc9807ff 0xf7fffffffe4c03ff

def z1009 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0x4b7bffe0ff07fb80 0x25bdfff07f83fdc0

def z1010 : W := mkw 0x00080900256e1d3a 0x0004048012b70e9d 0x1000000003fe3fff 0x8800000001ff1fff

def z1011 : W := mkw 0x5008090027effffa 0x2804048013f7fffd 0x1000000003ffffff 0x8800000001ffffff

def z1012 : W := mkw 0x10080900256e9d3a 0x0804048012b74e9d 0x1000000000fe3c7f 0x88000000007f1e3f

def z1013 : W := mkw 0x882b6d00016db000 0x4415b68000b6d800 0x2a7bff000067f800 0x153dff800033fc00

def z1014 : W := mkw 0x88676d00002db000 0x4433b6800016d800 0x2a7fff000007f800 0x153fff800003fc00

def z1015 : W := mkw 0x1239a8688164c190 0x091cd43440b260c8 0x637bb8e00361c380 0x31bddc7001b0e1c0

def z1016 : W := mkw 0x1239a068a542cdb0 0x091cd03452a166d8 0xdffbc0f0ff87ffe0 0x6ffde0787fc3fff0

def z1017 : W := mkw 0x103928482166c598 0x081c942410b362cc 0xff7bb8ec0367c799 0x7fbddc7601b3e3cc

def z1018 : W := mkw 0x1239b96ce16ed598 0x091cdcb670b76acc 0xffffffffe3ffffff 0xfffffffff1ffffff

def z1019 : W := mkw 0x440080b0b4024ee0 0x220040585a012770 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z1020 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x6b7fffeffc000000 0x35bffff7fe000000

def z1021 : W := mkw 0x1239ba6ded66cdba 0x091cdd36f6b366dd 0xffffb8ffffffc7ff 0xffffdc7fffffe3ff

def z1022 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xdf7bb8e0e307c780 0x6fbddc707183e3c0

def z1023 : W := mkw 0xa9c6459202993244 0x54e322c9014c9922 0x0084470000983800 0x00422380004c1c00

def z1024 : W := mkw 0x0018986ce1664598 0x000c4c3670b322cc 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z1025 : W := mkw 0x89e7650002993000 0x44f3b280014c9800 0xfbffff00039ff800 0x7dffff8001cffc00

def z1026 : W := mkw 0x0ff7f6ffda812000 0x87fbfb7fed409000 0xeffffffffc803800 0x77fffffffe401c00

def z1027 : W := mkw 0x0865360548000000 0x04329b02a4000000 0xaefc7f1ffc000000 0x577e3f8ffe000000

def z1028 : W := mkw 0xa9ef6d9203fdb244 0x54f7b6c901fed922 0xffffff1f03fffc7f 0xffffff8f81fffe3f

def z1029 : W := mkw 0x1239a868a166c598 0x091cd43450b362cc 0x437b80e00307c380 0x21bdc0700183e1c0

def z1030 : W := mkw 0x6582c0b2b6836ee4 0x32c160595b41b772 0xdd83c0f3ff87ffe6 0xeec1e079ffc3fff3

def z1031 : W := mkw 0x200812054bd00354 0x10040902a5e801aa 0xbc847f1ffff807ff 0xde423f8ffffc03ff

def z1032 : W := mkw 0x2dde44da13d00354 0x96ef226d09e801aa 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z1033 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7fbfefe3ffffff 0xffbfdff7f1ffffff

def z1034 : W := mkw 0x1239b86cc164c198 0x091cdc3660b260cc 0x437bb8e00301c380 0x21bddc700180e1c0

def z1035 : W := mkw 0x1239a8688164c190 0x091cd43440b260c8 0x4b7bb8e00307c380 0x25bddc700183e1c0

def z1036 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffff1f03fff800 0x7fffff8f81fffc00

def z1037 : W := mkw 0xafffe4fa93d1a354 0xd7fff27d49e8d1aa 0x437b80e00301c380 0x21bdc0700180e1c0

def z1038 : W := mkw 0x4402c020b4036ca0 0x220160105a01b650 0x4903c0e0ff07fb80 0x2481e0707f83fdc0

def z1039 : W := mkw 0x205c00da01500354 0x102e006d00a801aa 0xf77c00ff037807ff 0xfbbe007f81bc03ff

def z1040 : W := mkw 0x65c6c0b2b6936ee4 0x32e360595b49b772 0xfd87c0ffffffffff 0xfec3e07fffffffff

def z1041 : W := mkw 0x1239a068a142c598 0x091cd03450a162cc 0x437b80e00301c799 0x21bdc0700180e3cc

def z1042 : W := mkw 0x0ff7f6ffd8000240 0x87fbfb7fec000120 0xeffffffffc0007e0 0x77fffffffe0003f0

def z1043 : W := mkw 0x00188068a1424590 0x000c403450a122c8 0xdf7b80e0e307c780 0x6fbdc0707183e3c0

def z1044 : W := mkw 0x00001b05482c1000 0x00000d82a4160800 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z1045 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xffffffffff07c000 0x7fffffffff83e000

def z1046 : W := mkw 0x21dc1bdf6ffe1f7e 0x10ee0defb7ff0fbf 0x4b787fe0ff063b80 0x25bc3ff07f831dc0

def z1047 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xef7bb8ece307c380 0x77bddc767183e1c0

def z1048 : W := mkw 0x1239b86ce566cdb8 0x091cdc3672b366dc 0xff7bb8fcff67c7f9 0x7fbddc7e7fb3e3fc

def z1049 : W := mkw 0x2ff7f6ffd8000354 0x97fbfb7fec0001aa 0xeffffffffc000380 0x77fffffffe0001c0

def z1050 : W := mkw 0x0e23f625d8000000 0x8711fb12ec000000 0xeb7bff00fc000000 0x75bdff807e000000

def z1051 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xffffff10fffff800 0x7fffff887ffffc00

def z1052 : W := mkw 0x3239b86ee166c59c 0x191cdc3770b362ce 0xff7bb8efe367c79f 0xffbddc77f1b3e3cf

def z1053 : W := mkw 0x4e23ff25fc2f7caa 0xa711ff92fe17be55 0x0803ff00fc07f800 0x0401ff807e03fc00

def z1054 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xffffffecffffff99 0x7ffffff67fffffcc

def z1055 : W := mkw 0x09e7640000012000 0x04f3b20000009000 0xebffff000007f800 0x75ffff800003fc00

def z1056 : W := mkw 0xa9ef6d0003fdb354 0x54f7b68001fed9aa 0xfbffff0003fffb80 0x7dffff8001fffdc0

def z1057 : W := mkw 0x07d492ffd8000000 0x83ea497fec000000 0xeffc7ffffc000000 0x77fe3ffffe000000

def z1058 : W := mkw 0x4dc646931a812240 0xa6e323498d409120 0x008447131c000000 0x004223898e000000

def z1059 : W := mkw 0x09e76d0002ad3000 0x04f3b68001569800 0xfbffff0003fff800 0x7dffff8001fffc00

def z1060 : W := mkw 0x0018806881404190 0x000c403440a020c8 0xf77b80ec0361c799 0x7bbdc07601b0e3cc

def z1061 : W := mkw 0x6dc646931e912a64 0xb6e323498f489532 0x008447131c983866 0x804223898e4c1c33

def z1062 : W := mkw 0x1231b86ce026c488 0x0918dc3670136244 0xff7bb8ece307c780 0x7fbddc767183e3c0

def z1063 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0x5903c0e0ff87ffe0 0x2c81e0707fc3fff0

def z1064 : W := mkw 0x09ef640003d12000 0x04f7b20001e89000 0xfbffff0003fff800 0x7dffff8001fffc00

def z1065 : W := mkw 0x1231b06ce0024598 0x0918d836700122cc 0xff7bb8ece307c799 0x7fbddc767183e3cc

def z1066 : W := mkw 0x2ff7f6ffd8000244 0x97fbfb7fec000122 0xeffffffffc000066 0xf7fffffffe000033

def z1067 : W := mkw 0x1218906ce1424598 0x090c483670a122cc 0xff7b80ece367c799 0x7fbdc07671b3e3cc

def z1068 : W := mkw 0x00080900256e9c2a 0x0004048012b74e15 0x1000000003fffc7f 0x8800000001fffe3f

def z1069 : W := mkw 0x1239b06cc140c198 0x091cd83660a060cc 0x437b80ec0301c399 0x21bdc0760180e1cc

def z1070 : W := mkw 0x0a75b66fc8000000 0x853adb37e4000000 0xeffffffffc000000 0x77fffffffe000000

def z1071 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xcffbfff0fc000000 0x67fdfff87e000000

def z1072 : W := mkw 0x00000900242e1c20 0x0000048012170e10 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z1073 : W := mkw 0x5639b86cf566cdb8 0x2b1cdc367ab366dc 0xff7bb8ecff67c799 0x7fbddc767fb3e3cc

def z1074 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xffffb8ece3ffc799 0x7fffdc7671ffe3cc

def z1075 : W := mkw 0x01ce490003fd3000 0x00e7248001fe9800 0xfbffff0003fff800 0x7dffff8001fffc00

def z1076 : W := mkw 0x1239ba6de966c598 0x091cdd36f4b362cc 0xff7bffecff67c799 0x7fbdfff67fb3e3cc

def z1077 : W := mkw 0xa9ef6d9203fdb354 0x54f7b6c901fed9aa 0xfbffff1303ffffff 0xfdffff8981ffffff

def z1078 : W := mkw 0x0029a920a56edca0 0x0014d49052b76e50 0xfffffff0ffffffe0 0x7ffffff87ffffff0

def z1079 : W := mkw 0x0231a068a0024480 0x0118d03450012240 0xdf7b80e0e307c780 0x6fbdc0707183e3c0

def z1080 : W := mkw 0x2ff7f6ffd8000114 0x97fbfb7fec00008a 0xeffffffffc00001f 0xf7fffffffe00000f

def z1081 : W := mkw 0x0e67f625d8000000 0x8733fb12ec000000 0x2a7fff00fc000000 0x153fff807e000000

def z1082 : W := mkw 0x0039a868a166c590 0x001cd43450b362c8 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z1083 : W := mkw 0x4582c020b6836ca0 0x22c160105b41b650 0xdd83c0e0ff87ff80 0x6ec1e0707fc3ffc0

def z1084 : W := mkw 0xa9ef6d9003fdb354 0x54f7b6c801fed9aa 0xfffffff003ffffff 0xfffffff801ffffff

def z1085 : W := mkw 0x4dc6449016812a60 0x26e322480b409530 0x008447101c803860 0x004223880e401c30

def z1086 : W := mkw 0xe008090027fffff4 0x7004048013fffffa 0x1000000003ffffff 0x8800000001ffffff

def z1087 : W := mkw 0x00001b056c2e5caa 0x00000d82b6172e55 0xbc847f1fffffffff 0xde423f8fffffffff

def z1088 : W := mkw 0x1239b96ce56eddba 0x091cdcb672b76edd 0xffffb8ffe3ffffff 0xffffdc7ff1ffffff

def z1089 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x4bfffff3fc000000 0x25fffff9fe000000

def z1090 : W := mkw 0x1239b06cc140c190 0x091cd83660a060c8 0x637bb8ec0301c380 0x31bddc760180e1c0

def z1091 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7bffffff67ffff 0xffbdffffffb3ffff

def z1092 : W := mkw 0x4dc6c4b0b6836ee0 0x26e362585b41b770 0xdd87c7f0ff87ffe0 0x6ec3e3f87fc3fff0

def z1093 : W := mkw 0x0ff7f6ffda812240 0x87fbfb7fed409120 0xffffffffff87ffe0 0x7fffffffffc3fff0

def z1094 : W := mkw 0x0ff7f6ffda800240 0x87fbfb7fed400120 0xefffffffff000380 0x77ffffffff8001c0

def z1095 : W := mkw 0x8def6d9013fdb000 0x46f7b6c809fed800 0xfbffff101ffff800 0x7dffff880ffffc00

def z1096 : W := mkw 0x45c6c0b0b6936ee0 0x22e360585b49b770 0xdd87c0f0ff9fffe0 0x6ec3e0787fcffff0

def z1097 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0xfb7bff000367f800 0x7dbdff8001b3fc00

def z1098 : W := mkw 0x09f776df48000000 0x04fbbb6fa4000000 0xeffffffffc000000 0x77fffffffe000000

def z1099 : W := mkw 0x8ff7f6ffd801a000 0xc7fbfb7fec00d000 0xeffffffffc01c000 0x77fffffffe00e000

def z1100 : W := mkw 0x89ef6d9003fdb240 0x44f7b6c801fed920 0xfbffff1003fff860 0x7dffff8801fffc30

def z1101 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xeffffffffc980066 0xf7fffffffe4c0033

def z1102 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x4f7bfffffc000000 0x27bdfffffe000000

def z1103 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7bb8ffffffffff 0xffbddc7fffffffff

def z1104 : W := mkw 0xa9ef6d9203fdb244 0x54f7b6c901fed922 0xfffffff303ffffe6 0xfffffff981fffff3

def z1105 : W := mkw 0x561092fffc024ff8 0xab08497ffe0127fc 0x040000fffc0007f9 0x0200007ffe0003fc

def z1106 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xfffc40ff03fe3fff 0xfffe207f81ff1fff

def z1107 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x2affff1ffc000000 0x157fff8ffe000000

def z1108 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xd77b80e00301c780 0x6bbdc0700180e3c0

def z1109 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x737bb8ec0367c799 0x39bddc7601b3e3cc

def z1110 : W := mkw 0x1239bb6dc96cd19a 0x091cddb6e4b668cd 0x637fbfef0379c39f 0xb1bfdff781bce1cf

def z1111 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xf37b80e00361c380 0x79bdc07001b0e1c0

def z1112 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xff7bb8ffe367c7ff 0xffbddc7ff1b3e3ff

def z1113 : W := mkw 0x0df7e4fa90000000 0x06fbf27d48000000 0xeffffffffc000000 0x77fffffffe000000

def z1114 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x737c00ef03f807ff 0xb9be007781fc03ff

def z1115 : W := mkw 0x0029b824e166c488 0x0014dc1270b36244 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z1116 : W := mkw 0x000013054c081822 0x00000982a6040c11 0xbc847f1ffcf83c7f 0xde423f8ffe7c1e3f

def z1117 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xf7ff80ff03f9c7ff 0xfbffc07f81fce3ff

def z1118 : W := mkw 0x858ac9b093fdb000 0x42c564d849fed800 0xdd83c0f0fffff800 0x6ec1e0787ffffc00

def z1119 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xffffffffff000780 0x7fffffffff8003c0

def z1120 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xfd87c0f0ffffffe0 0x7ec3e0787ffffff0

def z1121 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x677c00ff037807ff 0xb3be007f81bc03ff

def z1122 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x737fbf0003fff800 0x39bfdf8001fffc00

def z1123 : W := mkw 0x0ff7f6ffda812000 0x87fbfb7fed409000 0xefffffffff01c000 0x77ffffffff80e000

def z1124 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xdb7b80e00307c380 0x6dbdc0700183e1c0

def z1125 : W := mkw 0xa9c647930e993a66 0x54e323c9874c9d33 0x008447131c983866 0x804223898e4c1c33

def z1126 : W := mkw 0x1ff7f6ffd8000118 0x8ffbfb7fec00008c 0xeffffffffc000019 0x77fffffffe00000c

def z1127 : W := mkw 0x00188068a5424db0 0x000c403452a126d8 0xffffc0ffffffffff 0xffffe07fffffffff

def z1128 : W := mkw 0x09ef6c0003e5a000 0x04f7b60001f2d000 0xfbffff0003e7f800 0x7dffff8001f3fc00

def z1129 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xe77b80ec0301c380 0x73bdc0760180e1c0

def z1130 : W := mkw 0x1239a068a142c590 0x091cd03450a162c8 0x4b7b80e0e307c380 0x25bdc0707183e1c0

def z1131 : W := mkw 0x1239b06ce142c598 0x091cd83670a162cc 0x437b80e0e301c380 0x21bdc0707180e1c0

def z1132 : W := mkw 0x21de40da03d12354 0x10ef206d01e891aa 0xf7ff80ff03f9c7ff 0xfbffc07f81fce3ff

def z1133 : W := mkw 0x0029a020a142c480 0x0014d01050a16240 0xdf7b80e0e307c780 0x6fbdc0707183e3c0

def z1134 : W := mkw 0x0ff7f4fcd0000000 0x07fbfa7e68000000 0xeffffffcfc000000 0x77fffffe7e000000

def z1135 : W := mkw 0x00088020a1424480 0x0004401050a12240 0xff7b80e0e367c780 0x7fbdc07071b3e3c0

def z1136 : W := mkw 0x1239b06cc140c190 0x091cd83660a060c8 0x4b7bb8e0e301c380 0x25bddc707180e1c0

def z1137 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0x26fc7ffffc000000 0x137e3ffffe000000

def z1138 : W := mkw 0x0ff7f6ffd8012000 0x87fbfb7fec009000 0xeffffffffc07f800 0x77fffffffe03fc00

def z1139 : W := mkw 0x89ef6d9003fdb240 0x44f7b6c801fed920 0xfbffffe003fffb80 0x7dfffff001fffdc0

def z1140 : W := mkw 0x1a39be6de966c598 0x8d1cdf36f4b362cc 0xff7bbfece367c799 0x7fbddff671b3e3cc

def z1141 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xfffbf8fcff67c799 0x7ffdfc7e7fb3e3cc

def z1142 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x577800ff03f807ff 0xabbc007f81fc03ff

def z1143 : W := mkw 0x65c65b977ebf3e6e 0x32e32dcbbf5f9f37 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z1144 : W := mkw 0x1239b06cc140c190 0x091cd83660a060c8 0x477b80ece301c380 0x23bdc0767180e1c0

def z1145 : W := mkw 0x1239ba6ded66cdba 0x091cdd36f6b366dd 0xff7bb8ecff67c799 0x7fbddc767fb3e3cc

def z1146 : W := mkw 0xcdc64d9036bf3e60 0x66e326c81b5f9f30 0xbc847f10fcfe3c60 0x5e423f887e7f1e30

def z1147 : W := mkw 0xa87d3f4f497c911e 0x543e9fa7a4be488f 0x227c3f0f0078001f 0x913e1f87803c000f

def z1148 : W := mkw 0x12393b4d496c911a 0x091c9da6a4b6488d 0x22783f0c00600019 0x113c1f860030000c

def z1149 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x5b7bb8e0e367c799 0x2dbddc7071b3e3cc

def z1150 : W := mkw 0x1239a8688164c190 0x091cd43440b260c8 0xff7bb8ec0367c799 0x7fbddc7601b3e3cc

def z1151 : W := mkw 0x461092fffc024eea 0xa308497ffe012775 0x040000fffc0007ff 0x8200007ffe0003ff

def z1152 : W := mkw 0x1239b96ce16ed598 0x091cdcb670b76acc 0xff7bb8ece3ffff99 0x7fbddc7671ffffcc

def z1153 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x677bb8ece361c799 0x33bddc7671b0e3cc

def z1154 : W := mkw 0x882b6d0003fdb000 0x4415b68001fed800 0xfb7bff0003fff800 0x7dbdff8001fffc00

def z1155 : W := mkw 0x0bf536df48000000 0x85fa9b6fa4000000 0xeffc7ffffc000000 0x77fe3ffffe000000

def z1156 : W := mkw 0x0ff7f6ffda800240 0x87fbfb7fed400120 0xeffffffffc800060 0x77fffffffe400030

def z1157 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0xfffc40fffff807ff 0xfffe207ffffc03ff

def z1158 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x577b80ece367c799 0x2bbdc07671b3e3cc

def z1159 : W := mkw 0xa9c6449202912244 0x54e3224901489122 0x0000000000000000 0x0000000000000000

def z1160 : W := mkw 0x0e77f66fd8000000 0x873bfb37ec000000 0x0a7bff00fc000000 0x053dff807e000000

def z1161 : W := mkw 0x1639ba6df966c598 0x8b1cdd36fcb362cc 0xff7bb8ecff67c799 0x7fbddc767fb3e3cc

def z1162 : W := mkw 0x09e7640000000000 0x04f3b20000000000 0xefffff10fc000000 0x77ffff887e000000

def z1163 : W := mkw 0x0e75b6ffd8000000 0x873adb7fec000000 0xaefc7ffffc000000 0x577e3ffffe000000

def z1164 : W := mkw 0x3239b86ce176c59c 0x191cdc3670bb62ce 0xff7bb8ece37fc79f 0xffbddc7671bfe3cf

def z1165 : W := mkw 0x1239a0688140c190 0x091cd03440a060c8 0xcf7b80e0e301c380 0x67bdc0707180e1c0

def z1166 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0x6b7bb8ece367c399 0x35bddc7671b3e1cc

def z1167 : W := mkw 0x9a39bd6ce16ed598 0x4d1cdeb670b76acc 0xff7bbfece367c799 0x7fbddff671b3e3cc

def z1168 : W := mkw 0x0582c0b092812240 0x02c1605849409120 0xdd83c0f0ff87ffe0 0x6ec1e0787fc3fff0

def z1169 : W := mkw 0x1239bb6de96ed59a 0x091cddb6f4b76acd 0xffffbfffe3ffc7ff 0xffffdffff1ffe3ff

def z1170 : W := mkw 0x1239b86ce166c598 0x091cdc3670b362cc 0xffffffece367c799 0x7ffffff671b3e3cc

def z1171 : W := mkw 0x21dc00da03d00354 0x10ee006d01e801aa 0x26fc00ff00f807ff 0x937e007f807c03ff

def z1172 : W := mkw 0x0231b86ce0264488 0x0118dc3670132244 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z1173 : W := mkw 0x0fe7f625d8000000 0x87f3fb12ec000000 0xefffff1ffc000000 0x77ffff8ffe000000

def z1174 : W := mkw 0x0ff7f6ffd8000000 0x87fbfb7fec000000 0xeffffffffc00047f 0xf7fffffffe00023f

def z1175 : W := mkw 0x0ff7f66fd8000000 0x87fbfb37ec000000 0xebffff0ffc000000 0x75ffff87fe000000

def z1176 : W := mkw 0x1239a868a166c598 0x091cd43450b362cc 0xdf7b80e0e367c799 0x6fbdc07071b3e3cc

def z1177 : W := mkw 0x25de40da13d00354 0x12ef206d09e801aa 0xf7fc40ff1ff807ff 0xfbfe207f8ffc03ff

def z1178 : W := mkw 0x661092fffc024ff4 0xb308497ffe0127fa 0x040000fffc0007ff 0x8200007ffe0003ff

def z1179 : W := mkw 0x1239b86ce566cdb8 0x091cdc3672b366dc 0xff7bb8ece3e7fff9 0x7fbddc7671f3fffc

def z1180 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7fbfffff7fc7ff 0xffbfdfffffbfe3ff

def z1181 : W := mkw 0x01cc009003d00240 0x00e6004801e80120 0xf7fc00ff03f807ff 0xfbfe007f81fc03ff

def z1182 : W := mkw 0x8008090027ffbc2a 0x4004048013ffde15 0x1000000003fff800 0x0800000001fffc00

def z1183 : W := mkw 0x4582c0b0b4036ca0 0x22c160585a01b650 0xdd83c0f0ff07ff80 0x6ec1e0787f83ffc0

def z1184 : W := mkw 0x45c6c0b2b6836ee0 0x22e360595b41b770 0xdd87c0f3ff87ffe0 0x6ec3e079ffc3fff0

def z1185 : W := mkw 0x00108068a0024480 0x0008403450012240 0xff7b80ece307c780 0x7fbdc0767183e3c0

def z1186 : W := mkw 0x0ff7f6ffda800240 0x87fbfb7fed400120 0xfffffffffff807ff 0xfffffffffffc03ff

def z1187 : W := mkw 0x89ef6d9203fdb000 0x44f7b6c901fed800 0xfbffff1303fff800 0x7dffff8981fffc00

def z1188 : W := mkw 0x45c6409016912a60 0x22e320480b489530 0x008440101c983860 0x004220080e4c1c30

def z1189 : W := mkw 0x00001b056c2e1c2a 0x00000d82b6170e15 0x24847f1ffcf83c7f 0x92423f8ffe7c1e3f

def z1190 : W := mkw 0x4dc656977e832e60 0xa6e32b4bbf419730 0xbc847f1ffc863c60 0x5e423f8ffe431e30

def z1191 : W := mkw 0x0a75364f48000000 0x853a9b27a4000000 0x267c3f1ffc000000 0x133e1f8ffe000000

def z1192 : W := mkw 0x886f6d00017db000 0x4437b68000bed800 0xbaffff0000fff800 0x5d7fff80007ffc00

def z1193 : W := mkw 0x1239b26ded42cdba 0x091cd936f6a166dd 0x477b80ffff01c7ff 0xa3bdc07fff80e3ff

def z1194 : W := mkw 0x89ef6d0003fdb000 0x44f7b68001fed800 0x5b7bff0003fff800 0x2dbdff8001fffc00

def z1195 : W := mkw 0x89ef6d9003fdb000 0x44f7b6c801fed800 0xfffffff003fff800 0x7ffffff801fffc00

def z1196 : W := mkw 0xedc6459216993a64 0x76e322c90b4c9d32 0x008447131c983866 0x804223898e4c1c33

def z1197 : W := mkw 0x1239b96ce56eddba 0x091cdcb672b76edd 0xffffffece3ffffff 0xfffffff671ffffff

def z1198 : W := mkw 0xc008090027fffca0 0x6004048013fffe50 0x1000000003fff800 0x0800000001fffc00

def z1199 : W := mkw 0x10188868a166c598 0x080c443450b362cc 0xff7b80ece367c799 0x7fbdc07671b3e3cc

def z1200 : W := mkw 0x1239b96ce56eddba 0x091cdcb672b76edd 0xff7bb8ece367ff99 0x7fbddc7671b3ffcc

def z1201 : W := mkw 0x0039384c61668518 0x001c9c2630b3428c 0xff7bb8ece367c799 0x7fbddc7671b3e3cc

def z1202 : W := mkw 0x0de7f6b5d8000000 0x06f3fb5aec000000 0xeffffffffc000000 0x77fffffffe000000

def z1203 : W := mkw 0x4582c0b0b6836ee0 0x22c160585b41b770 0xdd83c0f0ffffffff 0xeec1e0787fffffff

def z1204 : W := mkw 0x0021320548000000 0x00109902a4000000 0xefffff1ffc000000 0x77ffff8ffe000000

def z1205 : W := mkw 0xa9c65f976ebf3e6e 0x54e32fcbb75f9f37 0xbc847f1ffcfe3c7f 0xde423f8ffe7f1e3f

def z1206 : W := mkw 0x886f6d00017db000 0x4437b68000bed800 0x0a7bff000007f800 0x053dff800003fc00

def z1207 : W := mkw 0x1239ba6de966c59a 0x091cdd36f4b362cd 0xff7bb8efe367c79f 0xffbddc77f1b3e3cf

def z1208 : W := mkw 0x00189b6ded6e5dba 0x000c4db6f6b72edd 0xffffffffffffffff 0xffffffffffffffff

def z1209 : W := mkw 0x440080b0b6836ee0 0x220040585b41b770 0xdd0380f0ff87ffe0 0x6e81c0787fc3fff0

def z1210 : W := mkw 0x1239bb6ded6eddba 0x091cddb6f6b76edd 0xff7bffecffffffff 0xffbdfff67fffffff

def z1211 : W := mkw 0x89ab6d0003edb000 0x44d5b68001f6d800 0xfbfbff0003e7f800 0x7dfdff8001f3fc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z7,z5,z6]),(0,[z0,z8,z9,z3,z4,z5,z6])],[(0,[z10,z0,z9,z3,z4,z5,z6]),(0,[z0,z11,z9,z3,z4,z5,z6]),(0,[z12,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z13,z3,z4,z6]),(0,[z0,z14,z9,z3,z4,z5,z6]),(0,[z0,z9,z15,z3,z4,z5,z16])],[(0,[z0,z9,z3,z17,z4,z18,z6])],[(0,[z0,z9,z19,z4,z20,z5,z6]),(0,[z0,z2,z21,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z22,z5,z6])],[(0,[z0,z9,z3,z4,z5,z23,z6]),(0,[z0,z9,z3,z4,z5,z24,z6]),(1,[z0,z25,z9,z4,z5,z6]),(0,[z0,z26,z9,z3,z4,z5,z6])],[],[(0,[z0,z27,z3,z4,z28,z5,z6]),(1,[z0,z29,z9,z3,z4,z5]),(0,[z30,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z32,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z33]),(0,[z34,z0,z9,z35,z4,z5,z6]),(0,[z36,z9,z3,z4,z37,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z38]),(0,[z0,z9,z39,z3,z4,z5,z6])],[(0,[z40,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z41,z6]),(0,[z0,z42,z9,z3,z4,z5,z6]),(0,[z0,z43,z9,z3,z4,z5,z6]),(0,[z0,z44,z3,z45,z4,z5,z6]),(0,[z0,z9,z3,z4,z46,z6,z47])]],
   [[(0,[z48,z0,z9,z19,z4,z5,z6]),(1,[z0,z9,z49,z3,z4,z5]),(0,[z0,z9,z31,z4,z50,z5,z6]),(0,[z0,z9,z3,z4,z5,z51,z6]),(0,[z0,z52,z9,z3,z4,z5,z6]),(1,[z0,z53,z9,z4,z5,z6])],[(1,[z0,z9,z54,z4,z5,z6]),(0,[z55,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z56,z5,z6])],[],[(0,[z10,z0,z21,z3,z4,z5,z6]),(0,[z0,z57,z9,z3,z4,z5,z6]),(0,[z0,z58,z9,z3,z4,z59,z5]),(0,[z0,z60,z9,z4,z5,z6,z16])],[(0,[z0,z9,z3,z4,z5,z6,z61]),(0,[z0,z9,z3,z4,z5,z6,z62]),(0,[z0,z63,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z64,z5,z6]),(0,[z65,z0,z9,z3,z66,z5,z6]),(0,[z0,z9,z3,z4,z67,z5,z6]),(0,[z0,z68,z9,z3,z4,z5,z6]),(0,[z0,z9,z69,z3,z4,z5,z6])],[(0,[z0,z70,z9,z3,z4,z5,z6]),(0,[z9,z3,z4,z37,z5,z71,z6]),(0,[z0,z2,z9,z3,z28,z5,z6]),(1,[z0,z9,z3,z17,z18,z6]),(0,[z0,z9,z3,z5,z72,z6,z73])],[(0,[z0,z9,z19,z4,z5,z74,z6]),(0,[z0,z9,z19,z4,z5,z75,z6]),(0,[z0,z9,z31,z4,z28,z5,z6]),(0,[z0,z9,z31,z4,z18,z5,z6]),(0,[z0,z76,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z77,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z78,z4,z5,z6]),(0,[z0,z79,z9,z3,z4,z5,z6]),(0,[z0,z80,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z81,z5,z6]),(0,[z0,z82,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z83,z4,z5,z6])],[(0,[z0,z84,z9,z3,z4,z5,z6]),(1,[z0,z9,z32,z85,z5,z6]),(0,[z0,z9,z3,z4,z5,z86,z6])],[(0,[z0,z9,z3,z4,z5,z6,z6]),(0,[z0,z87,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z88,z4,z5,z6]),(0,[z0,z9,z4,z89,z5,z90,z6]),(1,[z0,z3,z4,z91,z5,z6])],[(0,[z0,z9,z19,z45,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z92,z6])],[(1,[z48,z9,z31,z4,z5,z6]),(0,[z0,z3,z93,z4,z50,z5,z6]),(0,[z0,z9,z3,z4,z94,z5,z6]),(0,[z95,z0,z9,z15,z3,z4,z5]),(0,[z0,z3,z96,z4,z28,z5,z6]),(0,[z0,z9,z3,z4,z5,z97,z6]),(0,[z0,z9,z98,z3,z4,z89,z6]),(0,[z0,z99,z9,z3,z45,z5,z6])],[(0,[z0,z2,z100,z3,z4,z5,z6]),(0,[z101,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z46,z6]),(0,[z0,z102,z3,z4,z37,z5,z6]),(0,[z0,z76,z103,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z71,z6]),(0,[z0,z9,z3,z104,z4,z5,z6]),(0,[z0,z105,z9,z3,z4,z5,z6]),(0,[z95,z0,z9,z3,z4,z5,z106]),(0,[z0,z42,z9,z4,z89,z5,z6]),(0,[z0,z9,z107,z3,z4,z5,z6])],[(0,[z0,z102,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z108,z5,z6]),(0,[z0,z109,z9,z3,z4,z5,z6]),(0,[z0,z9,z110,z3,z4,z5,z6]),(0,[z0,z9,z3,z111,z4,z5,z6])]],
   [[(0,[z0,z112,z9,z3,z19,z4,z6]),(0,[z30,z0,z80,z9,z3,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z113]),(0,[z114,z0,z9,z3,z4,z5,z6]),(1,[z0,z115,z3,z4,z5,z6])],[(0,[z0,z9,z27,z19,z4,z5,z6]),(0,[z116,z100,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z117,z6]),(0,[z118,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z119,z5,z6]),(0,[z0,z9,z3,z4,z5,z120,z6]),(0,[z0,z9,z3,z4,z5,z121,z6]),(0,[z0,z122,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z123,z6]),(0,[z124,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z125,z3,z4,z5,z6])],[(0,[z126,z0,z9,z3,z4,z5,z6]),(0,[z30,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z32,z3,z4,z5,z6])],[(0,[z0,z9,z127,z31,z4,z5,z6]),(0,[z0,z128,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z129,z5,z6]),(0,[z0,z9,z3,z4,z5,z72,z47])],[(0,[z0,z9,z31,z19,z4,z5,z6]),(0,[z0,z130,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z131,z6])],[(0,[z10,z0,z100,z3,z4,z5,z6]),(0,[z0,z9,z132,z3,z4,z5,z6]),(0,[z0,z133,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z134,z4,z5,z6]),(0,[z0,z9,z135,z19,z4,z5,z6]),(0,[z95,z0,z9,z136,z4,z5,z6]),(0,[z0,z42,z9,z137,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z138]),(0,[z0,z139,z9,z3,z4,z5,z6])],[(0,[z0,z9,z31,z4,z140,z5,z6]),(0,[z0,z141,z9,z3,z4,z74,z6]),(0,[z0,z9,z3,z4,z5,z6,z142]),(0,[z0,z9,z143,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z47])],[(0,[z0,z2,z3,z4,z5,z74,z6]),(0,[z0,z58,z9,z3,z4,z5,z62]),(0,[z0,z9,z3,z4,z5,z6,z144]),(0,[z0,z80,z9,z4,z89,z5,z6]),(0,[z0,z9,z145,z3,z4,z5,z6])]],
   [[(0,[z146,z0,z9,z147,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z148,z6]),(0,[z0,z60,z9,z3,z4,z5,z75]),(0,[z0,z9,z3,z4,z5,z6,z149])],[(0,[z0,z9,z3,z4,z5,z150,z6]),(0,[z0,z9,z31,z96,z4,z5,z6]),(0,[z34,z9,z3,z4,z5,z71,z6]),(1,[z0,z76,z3,z4,z5,z151]),(0,[z0,z76,z9,z3,z4,z5,z73])],[(0,[z0,z9,z19,z66,z4,z5,z6]),(0,[z0,z9,z152,z3,z4,z5,z6])],[(0,[z0,z9,z3,z3,z4,z5,z6]),(0,[z65,z0,z9,z31,z4,z5,z6]),(0,[z30,z0,z9,z3,z4,z5,z153]),(0,[z0,z154,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z6,z155]),(1,[z0,z9,z3,z4,z5,z156]),(0,[z0,z9,z3,z4,z5,z6,z73])],[(0,[z0,z9,z31,z157,z4,z5,z6]),(0,[z0,z9,z158,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z159,z5,z6]),(0,[z0,z160,z9,z3,z4,z5,z6]),(0,[z0,z103,z9,z3,z4,z5,z6]),(0,[z0,z161,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z162,z4,z5,z6]),(0,[z0,z163,z9,z3,z4,z5,z156])],[(0,[z0,z29,z9,z19,z4,z5,z6]),(0,[z0,z60,z9,z19,z4,z5,z6]),(0,[z0,z164,z9,z3,z4,z5,z6]),(0,[z0,z103,z9,z3,z4,z129,z6]),(1,[z0,z9,z3,z4,z5,z165]),(1,[z0,z3,z4,z5,z6,z166])],[(0,[z0,z9,z3,z167,z4,z5,z6]),(0,[z10,z0,z3,z4,z5,z74,z6]),(0,[z0,z1,z9,z31,z4,z5,z6]),(1,[z0,z9,z168,z4,z5,z6]),(0,[z36,z0,z9,z3,z4,z71,z6])]],
   [[(0,[z0,z9,z98,z19,z4,z5,z6]),(1,[z0,z169,z3,z4,z5,z6]),(0,[z30,z0,z9,z3,z50,z5,z6]),(0,[z170,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z171,z6]),(0,[z0,z9,z3,z4,z172,z5,z6])],[(0,[z173,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z17,z4,z5,z6]),(0,[z0,z174,z9,z3,z4,z5,z6]),(0,[z0,z175,z9,z3,z4,z5,z6])],[(0,[z65,z0,z9,z104,z4,z5,z6]),(0,[z0,z8,z9,z3,z4,z18,z6])],[(0,[z0,z9,z3,z4,z5,z6,z176]),(0,[z0,z9,z3,z4,z5,z177,z6]),(0,[z30,z0,z9,z32,z3,z5,z6]),(0,[z0,z9,z178,z3,z4,z5,z6])],[(0,[z0,z179,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z180]),(0,[z0,z9,z31,z4,z5,z75,z6]),(0,[z0,z9,z3,z35,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z155,z73]),(0,[z0,z9,z3,z4,z5,z181,z6]),(0,[z0,z76,z9,z3,z4,z5,z72])],[(0,[z0,z9,z3,z182,z4,z5,z6]),(1,[z0,z183,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z37,z5,z6]),(0,[z146,z0,z9,z15,z3,z4,z5]),(0,[z0,z184,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z50,z5,z6]),(0,[z0,z103,z3,z4,z28,z5,z6]),(0,[z0,z9,z3,z4,z5,z185,z6]),(1,[z0,z175,z3,z4,z5,z6])],[(0,[z0,z9,z127,z3,z4,z5,z6]),(0,[z146,z0,z9,z3,z4,z5,z106]),(0,[z0,z9,z3,z4,z5,z6,z186])]],
   [[(0,[z0,z100,z9,z31,z4,z5,z6]),(0,[z0,z9,z31,z45,z4,z5,z6]),(1,[z0,z9,z136,z4,z5,z6]),(0,[z0,z9,z3,z187,z4,z5,z6]),(0,[z0,z9,z188,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z189,z5,z6]),(0,[z0,z190,z3,z4,z50,z5,z6]),(0,[z0,z191,z9,z3,z4,z5,z6])],[(0,[z0,z9,z192,z3,z19,z5,z6]),(0,[z0,z122,z3,z85,z4,z5,z6]),(0,[z0,z9,z3,z4,z89,z5,z6]),(0,[z0,z193,z9,z3,z4,z5,z6]),(0,[z0,z163,z9,z3,z4,z5,z194])],[(0,[z10,z0,z58,z3,z4,z5,z6])],[(0,[z0,z135,z3,z19,z4,z5,z6]),(1,[z0,z3,z4,z5,z195,z6]),(0,[z0,z9,z3,z4,z5,z196,z6]),(0,[z0,z9,z3,z4,z5,z197,z6])],[(0,[z0,z9,z19,z4,z28,z5,z6]),(0,[z0,z9,z19,z4,z18,z5,z6]),(0,[z65,z0,z80,z9,z3,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z198]),(0,[z0,z76,z3,z4,z5,z74,z6]),(0,[z0,z199,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z200,z5,z6]),(0,[z0,z9,z201,z3,z4,z5,z6]),(0,[z0,z9,z202,z3,z4,z5,z6]),(0,[z0,z203,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z75,z6,z16])],[(0,[z0,z9,z31,z4,z5,z204,z6]),(0,[z65,z0,z9,z3,z4,z5,z6]),(0,[z95,z0,z9,z3,z4,z5,z155]),(0,[z0,z205,z9,z3,z4,z5,z6]),(0,[z0,z206,z21,z3,z4,z5,z6]),(0,[z0,z207,z9,z3,z4,z5,z6]),(0,[z0,z9,z208,z3,z4,z5,z6]),(0,[z209,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z85,z4,z5,z75,z6]),(0,[z0,z9,z3,z4,z5,z6,z210]),(0,[z0,z9,z3,z4,z211,z5,z6])]],
   [[(0,[z212,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z168,z3,z4,z5,z6]),(0,[z213,z0,z9,z3,z4,z5,z6])],[(0,[z214,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z158,z3,z4,z5,z6]),(1,[z0,z9,z215,z4,z5,z6]),(0,[z0,z9,z3,z137,z4,z5,z6]),(0,[z0,z9,z3,z216,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z217,z6]),(0,[z0,z218,z9,z3,z4,z5,z6])],[(0,[z10,z9,z27,z3,z4,z5,z6]),(0,[z0,z9,z3,z54,z4,z5,z6]),(0,[z0,z3,z4,z28,z5,z74,z6]),(0,[z0,z9,z3,z4,z5,z219,z6])],[(0,[z116,z0,z3,z4,z5,z151,z6]),(0,[z0,z9,z19,z4,z5,z46,z6]),(0,[z0,z9,z3,z220,z4,z5,z6]),(0,[z0,z9,z3,z221,z4,z5,z6]),(0,[z0,z1,z9,z3,z4,z5,z6]),(0,[z0,z222,z9,z3,z4,z5,z6]),(0,[z0,z9,z223,z3,z4,z5,z6])],[(0,[z116,z0,z9,z31,z4,z5,z6]),(0,[z0,z112,z9,z3,z4,z5,z6]),(0,[z95,z0,z60,z9,z3,z4,z5]),(1,[z0,z141,z3,z4,z74,z6]),(1,[z0,z103,z3,z4,z129,z6]),(0,[z224,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z225,z6]),(0,[z0,z9,z3,z4,z5,z226,z6])],[(0,[z0,z9,z3,z227,z4,z5,z6]),(0,[z0,z228,z9,z3,z4,z5,z6]),(0,[z0,z9,z229,z3,z4,z5,z6]),(0,[z0,z141,z3,z4,z5,z151,z6]),(0,[z0,z9,z3,z4,z5,z6,z230])],[(0,[z0,z141,z9,z31,z4,z5,z6]),(1,[z0,z122,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z231,z5,z6])],[(0,[z0,z99,z9,z19,z4,z5,z6]),(0,[z0,z9,z32,z85,z4,z5,z6])]],
   [[(1,[z0,z9,z232,z4,z5,z6]),(0,[z36,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z233,z6]),(0,[z0,z63,z76,z9,z3,z4,z5])],[(0,[z0,z9,z31,z4,z5,z6,z155]),(0,[z0,z9,z31,z4,z5,z234,z6]),(0,[z0,z235,z9,z3,z4,z5,z6]),(0,[z0,z76,z58,z3,z4,z5,z6]),(0,[z0,z80,z9,z4,z236,z5,z6])],[(0,[z0,z9,z19,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z237,z5,z6]),(0,[z0,z9,z3,z4,z59,z5,z47])],[(0,[z10,z0,z27,z3,z4,z5,z6]),(1,[z0,z130,z19,z4,z5,z6]),(0,[z0,z238,z9,z3,z4,z5,z6]),(0,[z0,z206,z9,z137,z4,z5,z6]),(0,[z0,z8,z60,z9,z4,z5,z6]),(0,[z0,z239,z9,z3,z4,z5,z6])],[(0,[z0,z100,z9,z3,z4,z5,z6]),(0,[z116,z0,z9,z132,z4,z5,z6]),(0,[z95,z0,z9,z19,z4,z5,z6]),(0,[z34,z0,z9,z215,z4,z5,z6])],[(0,[z65,z0,z9,z3,z50,z5,z6]),(1,[z0,z240,z3,z4,z5,z6])],[(0,[z10,z0,z1,z3,z4,z5,z6]),(0,[z0,z241,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z242,z4,z5,z6]),(0,[z0,z243,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z244,z6]),(0,[z0,z9,z245,z3,z4,z5,z6]),(0,[z0,z9,z3,z246,z4,z5,z6]),(0,[z0,z247,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z96,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z248,z6]),(0,[z0,z8,z9,z98,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z249])]],
   [[(0,[z250,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z251,z5,z6]),(0,[z0,z252,z9,z3,z4,z5,z6]),(0,[z65,z0,z9,z32,z3,z5,z6]),(0,[z0,z9,z3,z85,z4,z5,z6]),(0,[z0,z9,z15,z3,z4,z5,z75])],[(0,[z0,z9,z3,z4,z5,z253,z6])],[(0,[z10,z0,z103,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z254]),(0,[z0,z9,z3,z4,z5,z6,z255]),(0,[z0,z256,z9,z3,z4,z5,z6]),(0,[z257,z0,z9,z3,z4,z5,z6])],[(0,[z0,z258,z9,z3,z4,z5,z6]),(0,[z0,z259,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z74,z6,z62])],[(0,[z0,z9,z3,z4,z5,z260,z6]),(0,[z48,z0,z9,z31,z4,z5,z6]),(0,[z261,z0,z9,z3,z4,z5,z6]),(1,[z0,z1,z3,z28,z5,z6]),(0,[z0,z9,z3,z4,z262,z5,z6])],[(0,[z0,z263,z9,z3,z4,z5,z6]),(0,[z0,z9,z19,z264,z4,z5,z6]),(0,[z0,z265,z9,z3,z4,z5,z6]),(1,[z0,z60,z9,z4,z5,z16])],[(0,[z0,z9,z3,z4,z5,z266,z6]),(1,[z0,z112,z9,z19,z4,z6]),(0,[z0,z9,z15,z19,z4,z5,z6]),(1,[z0,z9,z267,z4,z5,z6]),(0,[z0,z9,z3,z96,z4,z5,z268]),(0,[z0,z269,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z270,z5,z6])],[(0,[z10,z0,z9,z232,z4,z5,z6]),(0,[z116,z0,z27,z3,z4,z5,z6]),(0,[z0,z9,z19,z17,z4,z5,z6]),(0,[z0,z9,z3,z271,z4,z5,z6]),(0,[z0,z9,z3,z4,z272,z5,z6])]],
   [[(0,[z116,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z273,z4,z5,z6]),(0,[z0,z9,z192,z3,z4,z5,z6]),(0,[z30,z0,z169,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z274,z5,z6]),(0,[z146,z0,z9,z3,z4,z5,z155]),(0,[z0,z1,z9,z3,z28,z5,z6]),(0,[z275,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z276,z3,z4,z5,z6]),(0,[z0,z9,z3,z18,z5,z234,z6])],[(0,[z0,z9,z49,z19,z4,z5,z6]),(1,[z0,z9,z3,z4,z177,z6]),(1,[z0,z190,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z37,z234,z6]),(0,[z0,z9,z3,z4,z277,z5,z6])],[(0,[z0,z9,z3,z278,z4,z5,z6]),(0,[z0,z279,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z280,z6]),(0,[z0,z141,z9,z3,z4,z5,z6]),(0,[z0,z281,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z72,z6])],[(0,[z0,z9,z3,z4,z5,z6,z282]),(0,[z146,z0,z9,z283,z4,z5,z6]),(0,[z0,z42,z3,z4,z28,z5,z6]),(0,[z0,z141,z9,z3,z4,z129,z6]),(0,[z0,z9,z3,z4,z284,z5,z6]),(0,[z0,z80,z60,z9,z4,z5,z6])],[(0,[z0,z9,z3,z285,z4,z5,z6]),(0,[z0,z58,z9,z31,z4,z5,z6]),(0,[z36,z0,z9,z3,z4,z5,z6]),(0,[z286,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z287,z5,z6]),(0,[z0,z9,z3,z4,z236,z5,z6]),(0,[z288,z0,z9,z3,z4,z5,z6])],[(0,[z30,z0,z183,z3,z4,z5,z6]),(0,[z146,z0,z60,z9,z3,z4,z5]),(0,[z0,z9,z289,z3,z4,z5,z6]),(0,[z0,z8,z9,z4,z5,z90,z6]),(0,[z0,z9,z3,z4,z5,z6,z290]),(0,[z0,z99,z9,z3,z5,z6,z73])],[(0,[z116,z0,z103,z3,z4,z5,z6]),(0,[z291,z0,z9,z19,z4,z5,z6]),(0,[z30,z9,z3,z4,z50,z5,z6]),(0,[z0,z9,z292,z3,z4,z5,z6])],[(1,[z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z293,z6]),(0,[z0,z9,z3,z294,z4,z5,z6]),(0,[z0,z2,z3,z96,z4,z5,z6]),(1,[z0,z44,z3,z4,z5,z6])]],
   [[(0,[z0,z163,z9,z19,z4,z5,z6]),(0,[z0,z8,z206,z9,z4,z5,z6]),(0,[z0,z141,z103,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z73,z47]),(0,[z0,z295,z9,z3,z4,z5,z6])],[(0,[z9,z31,z3,z19,z4,z5,z6]),(0,[z0,z9,z296,z3,z4,z5,z6]),(0,[z0,z297,z9,z3,z4,z5,z6])],[(0,[z116,z0,z21,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z298,z5,z6]),(0,[z0,z9,z3,z4,z5,z299,z6]),(0,[z0,z9,z3,z300,z4,z5,z6])],[(0,[z301,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z302,z6]),(0,[z303,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z304,z4,z5,z6]),(0,[z0,z9,z3,z4,z305,z5,z6]),(0,[z0,z306,z9,z3,z4,z5,z6])],[(0,[z0,z206,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z307]),(0,[z0,z9,z3,z4,z5,z308,z6])],[(0,[z0,z9,z27,z31,z4,z5,z6]),(0,[z146,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z6,z62]),(1,[z0,z9,z147,z4,z5,z6]),(0,[z0,z9,z3,z4,z309,z5,z6]),(0,[z0,z9,z3,z4,z5,z151,z6]),(0,[z0,z310,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z311,z5,z6]),(0,[z0,z9,z3,z4,z312,z5,z6])],[(1,[z0,z70,z9,z19,z5,z6]),(0,[z0,z9,z15,z4,z5,z75,z6]),(0,[z0,z9,z313,z3,z4,z5,z6]),(0,[z0,z63,z9,z3,z4,z6,z47])],[(0,[z314,z0,z9,z3,z4,z5,z6]),(0,[z10,z0,z3,z96,z4,z5,z6]),(0,[z0,z9,z315,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z316,z6]),(0,[z0,z9,z3,z4,z5,z317,z6]),(0,[z0,z9,z318,z3,z4,z5,z6]),(0,[z0,z9,z3,z319,z4,z5,z6])]],
   [[(0,[z48,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z31,z4,z5,z6]),(0,[z0,z42,z206,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z268,z6]),(0,[z0,z9,z3,z4,z5,z320,z6]),(0,[z0,z321,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z322])],[(0,[z0,z9,z3,z4,z5,z6,z323])],[(0,[z0,z9,z324,z31,z4,z5,z6]),(0,[z0,z9,z3,z325,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z326])],[(0,[z0,z9,z3,z4,z5,z327,z6]),(0,[z34,z0,z9,z3,z4,z37,z6]),(0,[z95,z0,z9,z328,z4,z5,z6]),(0,[z0,z21,z3,z137,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z329]),(0,[z0,z9,z3,z4,z5,z330,z6])],[(0,[z331,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z332,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z333,z6]),(0,[z0,z334,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z335,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z6,z336])],[(1,[z10,z27,z3,z4,z5,z6]),(1,[z0,z9,z192,z19,z5,z6]),(1,[z0,z9,z315,z4,z5,z6]),(0,[z0,z9,z3,z337,z4,z5,z6]),(0,[z0,z2,z9,z3,z96,z5,z6]),(0,[z0,z76,z9,z3,z4,z5,z151]),(0,[z0,z9,z3,z4,z338,z5,z6]),(0,[z0,z9,z3,z4,z5,z339,z6])],[(0,[z116,z0,z9,z54,z4,z5,z6]),(0,[z0,z9,z19,z4,z5,z234,z6]),(0,[z0,z0,z9,z31,z4,z5,z6]),(0,[z65,z9,z3,z66,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z340,z6]),(0,[z0,z9,z3,z4,z341,z5,z6]),(1,[z146,z9,z3,z4,z5,z106]),(0,[z0,z342,z9,z3,z4,z5,z6]),(0,[z343,z0,z9,z3,z4,z5,z6]),(0,[z0,z8,z9,z3,z4,z234,z6])]],
   [[(0,[z0,z344,z9,z19,z4,z5,z6]),(0,[z0,z9,z21,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z345,z5,z6]),(0,[z0,z9,z3,z4,z5,z346,z6]),(0,[z0,z9,z347,z3,z4,z5,z6]),(0,[z0,z58,z9,z3,z4,z5,z6]),(0,[z0,z8,z9,z85,z4,z5,z6]),(0,[z0,z9,z3,z348,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z349,z6]),(0,[z0,z350,z9,z4,z5,z234,z6])],[(0,[z0,z9,z351,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z352,z5,z6]),(0,[z0,z353,z9,z3,z4,z5,z6])],[(0,[z354,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z106,z6])],[(0,[z0,z9,z355,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z356,z5,z6])],[(0,[z116,z0,z100,z3,z4,z5,z6]),(0,[z0,z42,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z129,z5,z6]),(0,[z0,z9,z3,z357,z4,z5,z6]),(1,[z0,z80,z9,z236,z5,z6]),(1,[z0,z9,z15,z4,z5,z75])],[(0,[z0,z8,z42,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z16]),(0,[z0,z9,z3,z4,z5,z6,z358])],[(0,[z0,z9,z3,z4,z359,z5,z6]),(0,[z0,z9,z360,z3,z4,z5,z6]),(0,[z0,z361,z9,z3,z4,z5,z6])],[(0,[z10,z0,z42,z3,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z6,z47]),(0,[z0,z9,z3,z362,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z363]),(0,[z0,z364,z9,z3,z4,z5,z6]),(0,[z0,z9,z98,z3,z4,z90,z6]),(0,[z0,z365,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z366,z5,z6]),(0,[z0,z206,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z268])],[(0,[z0,z9,z3,z232,z4,z5,z6]),(0,[z0,z9,z27,z3,z4,z5,z6]),(0,[z367,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z13,z19,z4,z6]),(0,[z0,z9,z3,z4,z368,z5,z6]),(0,[z0,z58,z3,z4,z28,z5,z6]),(0,[z0,z9,z3,z4,z59,z46,z6])],[(0,[z0,z9,z9,z3,z4,z5,z6]),(0,[z100,z9,z27,z3,z4,z5,z6]),(0,[z0,z369,z9,z3,z4,z5,z6]),(0,[z0,z9,z19,z4,z5,z370,z6]),(0,[z371,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z372,z5,z6])],[(0,[z0,z9,z373,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z374,z5,z6]),(0,[z0,z9,z3,z4,z5,z329,z74]),(0,[z0,z9,z375,z3,z4,z5,z6])],[(0,[z0,z9,z31,z3,z4,z5,z6]),(0,[z0,z76,z9,z19,z4,z5,z6]),(0,[z0,z130,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z376,z6]),(0,[z0,z9,z3,z377,z4,z5,z6]),(0,[z0,z9,z3,z4,z378,z5,z6]),(0,[z0,z379,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z194])],[(0,[z0,z9,z135,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z380,z6]),(0,[z0,z381,z9,z31,z4,z5,z6]),(1,[z65,z9,z3,z66,z5,z6]),(0,[z0,z25,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z89,z5,z75,z6]),(0,[z0,z63,z115,z3,z4,z5,z6])],[(0,[z0,z9,z324,z3,z4,z5,z6]),(0,[z116,z0,z3,z4,z5,z74,z6]),(1,[z0,z29,z9,z19,z4,z5]),(0,[z0,z382,z9,z3,z4,z5,z6]),(0,[z0,z383,z9,z3,z4,z5,z6]),(0,[z0,z42,z9,z21,z4,z5,z6]),(1,[z0,z42,z137,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z384,z6]),(0,[z0,z9,z3,z4,z5,z6,z385]),(0,[z386,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z85,z4,z387,z6]),(0,[z0,z9,z3,z4,z5,z6,z388])],[(0,[z36,z0,z9,z3,z4,z37,z6]),(1,[z0,z206,z21,z4,z5,z6]),(0,[z0,z389,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z390,z6]),(0,[z0,z391,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z392,z3,z4,z5,z6]),(1,[z0,z9,z49,z19,z4,z5]),(1,[z34,z9,z3,z4,z71,z6]),(0,[z0,z9,z3,z4,z393,z5,z6]),(0,[z0,z141,z3,z4,z5,z74,z6]),(0,[z0,z9,z3,z4,z5,z90,z6]),(0,[z0,z9,z394,z3,z4,z5,z6])],[(0,[z0,z395,z9,z3,z4,z5,z6]),(0,[z30,z0,z9,z3,z4,z177,z6]),(0,[z0,z396,z9,z3,z4,z5,z6]),(0,[z0,z397,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z59,z5,z6])],[(0,[z0,z9,z398,z3,z4,z5,z6]),(0,[z0,z9,z399,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z400,z6]),(0,[z0,z58,z9,z3,z4,z5,z73]),(0,[z0,z9,z3,z4,z5,z6,z401]),(0,[z0,z9,z3,z4,z5,z194,z6]),(0,[z0,z9,z3,z4,z5,z402,z6])],[(0,[z0,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z106,z73]),(0,[z0,z9,z21,z3,z4,z5,z6]),(0,[z0,z103,z3,z4,z5,z6,z62]),(1,[z0,z9,z4,z5,z403,z6]),(0,[z0,z9,z3,z4,z404,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z405])],[(0,[z406,z0,z9,z19,z4,z5,z6]),(0,[z0,z29,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z407,z4,z5,z6]),(0,[z0,z9,z3,z4,z408,z5,z6])],[(0,[z0,z9,z3,z4,z409,z5,z6]),(0,[z30,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z267,z4,z5,z6]),(1,[z0,z102,z3,z4,z5,z6]),(0,[z0,z206,z9,z4,z89,z5,z6]),(0,[z0,z9,z4,z5,z185,z74,z6]),(0,[z410,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z411]),(0,[z0,z9,z3,z4,z412,z5,z6])]],
   [[(0,[z0,z413,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z7,z5,z6]),(0,[z0,z9,z3,z414,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z415]),(0,[z0,z9,z3,z4,z416,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z417])],[(0,[z116,z0,z58,z3,z4,z5,z6]),(0,[z0,z418,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z419,z4,z5,z6]),(1,[z0,z9,z3,z4,z123,z6])],[(0,[z0,z9,z19,z4,z5,z6,z62]),(0,[z0,z99,z9,z31,z4,z5,z6]),(0,[z0,z9,z31,z4,z89,z5,z6])],[(0,[z420,z0,z9,z3,z4,z5,z6]),(0,[z0,z421,z9,z3,z4,z5,z6]),(0,[z0,z141,z58,z3,z4,z5,z6])],[(0,[z0,z422,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z96,z4,z5,z423]),(0,[z0,z3,z4,z129,z5,z151,z6]),(0,[z0,z58,z9,z3,z4,z5,z72])],[(0,[z424,z0,z9,z3,z4,z5,z6]),(0,[z425,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z5,z234,z6,z73])],[(0,[z0,z9,z373,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z426,z6]),(0,[z0,z9,z3,z427,z4,z5,z6]),(0,[z0,z1,z3,z4,z28,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z156])]],
   [[(0,[z0,z9,z13,z19,z4,z5,z6]),(0,[z0,z9,z3,z19,z4,z5,z6]),(0,[z95,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z428,z6]),(0,[z0,z9,z3,z45,z5,z72,z6])],[(0,[z0,z381,z9,z3,z4,z5,z6]),(0,[z0,z429,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z71,z234,z6]),(0,[z0,z42,z2,z3,z4,z5,z6]),(0,[z0,z9,z3,z430,z4,z5,z6])],[(0,[z0,z103,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z137,z4,z5,z6]),(1,[z0,z9,z98,z4,z89,z6]),(0,[z0,z9,z3,z4,z5,z431,z6]),(0,[z0,z9,z3,z4,z5,z6,z432]),(0,[z0,z9,z433,z3,z4,z5,z6])],[(0,[z0,z434,z9,z3,z4,z5,z6]),(0,[z0,z103,z3,z4,z129,z5,z6]),(0,[z435,z0,z9,z3,z4,z5,z6]),(1,[z0,z436,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z20,z5,z6]),(0,[z30,z0,z9,z332,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z437,z6]),(0,[z0,z63,z9,z3,z372,z5,z6])],[(0,[z0,z9,z3,z4,z5,z438,z6]),(0,[z0,z9,z3,z4,z439,z5,z6])],[(0,[z0,z9,z3,z4,z5,z6,z440]),(0,[z0,z29,z9,z3,z19,z4,z5]),(0,[z30,z0,z9,z315,z4,z5,z6]),(0,[z0,z441,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z442,z4,z5,z6]),(0,[z0,z3,z85,z4,z7,z5,z6]),(0,[z0,z9,z3,z4,z5,z165,z6]),(0,[z0,z9,z3,z443,z4,z5,z6]),(0,[z0,z9,z3,z45,z17,z5,z6])],[(0,[z444,z0,z9,z3,z4,z5,z6]),(0,[z34,z0,z8,z9,z3,z4,z6])]],
   [[(0,[z0,z100,z3,z4,z28,z5,z6]),(1,[z0,z9,z283,z4,z5,z6]),(0,[z0,z80,z9,z3,z85,z5,z6]),(0,[z0,z445,z9,z3,z4,z5,z6]),(0,[z0,z9,z446,z3,z4,z5,z6]),(0,[z0,z447,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z448,z6]),(0,[z0,z9,z3,z4,z18,z71,z6]),(0,[z449,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z129,z5,z6]),(0,[z0,z9,z15,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z450,z5,z6]),(0,[z9,z3,z4,z5,z106,z6,z155]),(0,[z0,z451,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z452]),(0,[z0,z9,z3,z85,z4,z5,z307]),(0,[z0,z9,z3,z4,z5,z6,z453]),(0,[z0,z9,z3,z4,z91,z5,z6])],[(1,[z9,z31,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z454]),(0,[z0,z455,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z456,z5,z6])],[(0,[z0,z9,z3,z457,z4,z5,z6]),(0,[z0,z9,z458,z3,z4,z5,z6]),(0,[z459,z0,z9,z3,z4,z5,z6]),(0,[z0,z8,z9,z3,z4,z89,z6])],[(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z0,z9,z19,z4,z5,z6,z47]),(0,[z0,z9,z3,z332,z4,z5,z6])],[(0,[z0,z9,z3,z4,z460,z5,z6]),(0,[z461,z0,z9,z3,z4,z5,z6]),(0,[z462,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z17,z5,z6,z73])],[(0,[z0,z9,z3,z4,z463,z5,z6]),(1,[z0,z9,z464,z4,z5,z6]),(0,[z95,z146,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z465,z6]),(0,[z0,z99,z9,z3,z4,z5,z6]),(0,[z466,z0,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z5,z74,z6]),(0,[z0,z467,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z75,z6]),(0,[z0,z468,z9,z3,z4,z5,z6]),(0,[z0,z9,z115,z3,z4,z5,z6])],[(1,[z0,z9,z3,z4,z5,z469]),(0,[z0,z9,z3,z470,z4,z5,z6]),(0,[z0,z60,z9,z15,z4,z5,z6]),(0,[z471,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z472,z3,z4,z5,z6])],[(1,[z30,z9,z3,z50,z5,z6]),(0,[z0,z473,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z474,z6]),(0,[z0,z475,z9,z3,z4,z5,z6]),(0,[z0,z9,z32,z3,z85,z5,z6]),(0,[z0,z44,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z6,z73]),(1,[z0,z112,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z5,z476,z6]),(0,[z0,z9,z3,z477,z4,z5,z6]),(0,[z0,z350,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z478,z4,z5,z6])],[(0,[z48,z9,z31,z3,z4,z5,z6]),(0,[z0,z163,z9,z31,z4,z5,z6]),(0,[z95,z0,z9,z3,z4,z5,z6]),(0,[z0,z479,z9,z3,z4,z5,z6]),(0,[z0,z206,z9,z21,z4,z5,z6]),(0,[z0,z164,z9,z3,z4,z5,z74]),(0,[z480,z0,z9,z3,z4,z5,z6]),(0,[z0,z163,z313,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z481,z6]),(0,[z0,z9,z3,z45,z4,z5,z6])],[(1,[z0,z135,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z482,z5,z6]),(1,[z0,z383,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z483,z73])],[(0,[z484,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z485,z5,z6]),(0,[z0,z9,z3,z4,z486,z5,z6])],[(0,[z0,z9,z3,z4,z5,z71,z6]),(0,[z487,z0,z9,z3,z4,z5,z6]),(0,[z488,z0,z9,z3,z4,z5,z6]),(0,[z0,z489,z9,z3,z4,z5,z6])]],
   [[],[(0,[z0,z2,z9,z19,z4,z5,z6]),(0,[z0,z112,z9,z19,z4,z5,z6]),(0,[z146,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z490,z6]),(0,[z0,z9,z3,z4,z5,z6,z491])],[(0,[z0,z9,z3,z4,z5,z492,z6]),(0,[z0,z493,z9,z3,z4,z5,z6]),(0,[z0,z494,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z495,z6]),(0,[z0,z9,z3,z4,z496,z5,z6]),(0,[z0,z163,z9,z3,z17,z5,z6]),(0,[z0,z63,z240,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z204,z6]),(0,[z0,z9,z3,z4,z5,z153,z6]),(0,[z0,z9,z3,z4,z497,z5,z6])],[(0,[z0,z9,z19,z4,z37,z5,z6]),(0,[z0,z9,z31,z4,z5,z6,z282]),(0,[z498,z0,z9,z3,z4,z5,z6]),(0,[z146,z9,z3,z4,z5,z106,z6]),(0,[z0,z499,z9,z3,z4,z5,z6]),(0,[z0,z63,z9,z3,z4,z5,z46])],[(0,[z34,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z236,z5,z6]),(0,[z0,z9,z3,z4,z500,z5,z6]),(0,[z501,z0,z9,z3,z4,z5,z6])],[(0,[z0,z502,z9,z3,z4,z5,z6]),(1,[z0,z164,z9,z3,z4,z5]),(0,[z0,z9,z15,z3,z4,z5,z6]),(0,[z0,z503,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z166])],[(0,[z0,z504,z9,z31,z4,z5,z6]),(0,[z0,z103,z2,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z423]),(0,[z0,z9,z3,z505,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z5,z506,z6]),(0,[z507,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z508,z4,z5,z6]),(0,[z0,z8,z9,z19,z4,z5,z6]),(0,[z0,z509,z9,z31,z4,z5,z6]),(0,[z0,z1,z9,z3,z96,z5,z6]),(0,[z0,z9,z3,z510,z4,z5,z6]),(0,[z0,z163,z306,z3,z4,z5,z6]),(1,[z0,z9,z4,z5,z6,z511])],[(0,[z10,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z19,z4,z89,z5,z6]),(0,[z0,z9,z49,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z4,z5,z6]),(0,[z0,z9,z3,z4,z512,z5,z6]),(0,[z0,z9,z3,z513,z4,z5,z6]),(0,[z514,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z515]),(0,[z0,z99,z9,z3,z4,z5,z73])],[(0,[z0,z9,z3,z4,z5,z516,z6]),(0,[z0,z9,z3,z4,z5,z517,z6]),(0,[z0,z9,z98,z3,z4,z18,z6])],[(0,[z0,z9,z3,z4,z518,z5,z6]),(1,[z291,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z66,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z519,z6])],[(0,[z520,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z521,z5,z6]),(0,[z0,z9,z3,z4,z522,z5,z6]),(0,[z0,z3,z4,z5,z151,z6,z62]),(0,[z0,z8,z9,z3,z4,z90,z6])],[(0,[z0,z60,z9,z31,z4,z5,z6]),(0,[z0,z9,z183,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z155]),(0,[z0,z523,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z524,z4,z5,z6]),(0,[z0,z9,z525,z3,z4,z5,z6]),(0,[z526,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z403,z6])],[(0,[z0,z527,z9,z3,z4,z5,z6]),(0,[z116,z0,z3,z96,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z151,z6]),(0,[z0,z9,z3,z4,z5,z6,z528]),(0,[z0,z53,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z45,z4,z5,z73]),(0,[z0,z9,z4,z5,z6,z511,z47])],[(0,[z0,z529,z9,z3,z4,z5,z6]),(0,[z0,z9,z98,z31,z4,z5,z6]),(0,[z65,z0,z9,z168,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z530]),(0,[z0,z9,z3,z531,z4,z5,z6]),(0,[z0,z9,z3,z4,z532,z5,z6])]],
   [[(0,[z0,z9,z19,z137,z4,z5,z6]),(0,[z0,z9,z215,z3,z4,z5,z6]),(0,[z34,z0,z9,z98,z3,z4,z6]),(0,[z36,z0,z9,z267,z4,z5,z6]),(0,[z0,z533,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z534,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z535]),(0,[z0,z9,z3,z4,z536,z5,z6]),(0,[z0,z163,z9,z3,z4,z5,z6]),(0,[z0,z537,z9,z3,z4,z5,z6]),(0,[z0,z9,z538,z3,z4,z5,z6])],[(0,[z0,z383,z3,z4,z5,z6,z155]),(0,[z0,z9,z3,z4,z5,z539,z6])],[(0,[z540,z0,z9,z3,z4,z5,z6]),(0,[z541,z0,z9,z3,z4,z5,z6]),(0,[z0,z76,z9,z3,z4,z59,z5]),(0,[z0,z542,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z543,z6])],[(0,[z544,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z545,z6])],[(0,[z48,z291,z9,z3,z4,z5,z6]),(0,[z0,z63,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z195,z6]),(0,[z0,z9,z3,z4,z546,z5,z6]),(0,[z0,z9,z3,z4,z5,z547,z6]),(0,[z0,z548,z9,z3,z4,z5,z6]),(0,[z0,z99,z9,z3,z4,z5,z72])],[(0,[z549,z0,z9,z3,z4,z5,z6]),(0,[z146,z0,z9,z3,z4,z5,z6])],[(0,[z0,z70,z9,z19,z4,z5,z6]),(0,[z0,z9,z147,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z550,z6]),(0,[z0,z9,z3,z551,z4,z5,z6])],[(0,[z0,z9,z3,z4,z50,z5,z6]),(0,[z0,z9,z3,z552,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z553]),(0,[z0,z554,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z80,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z6,z73]),(0,[z555,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z556,z3,z4,z5,z6]),(0,[z557,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z558]),(0,[z0,z9,z3,z4,z559,z5,z6]),(0,[z0,z8,z9,z4,z5,z75,z6]),(0,[z0,z9,z15,z3,z4,z5,z73]),(0,[z0,z560,z9,z3,z4,z5,z6])],[(0,[z36,z0,z9,z19,z4,z5,z6]),(1,[z0,z9,z328,z4,z5,z6]),(0,[z0,z9,z3,z45,z4,z5,z72])],[(0,[z0,z9,z3,z93,z4,z5,z6]),(0,[z561,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z562,z5,z6]),(0,[z0,z9,z3,z4,z5,z329,z6])],[(0,[z563,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z106,z6]),(0,[z0,z504,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z564]),(0,[z565,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z13,z3,z19,z4,z6]),(0,[z0,z566,z9,z31,z4,z5,z6]),(0,[z0,z509,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z512,z6]),(0,[z0,z9,z3,z4,z5,z6,z567]),(0,[z0,z9,z3,z568,z4,z5,z6]),(0,[z0,z9,z3,z569,z4,z5,z6]),(1,[z0,z163,z9,z3,z234,z6])],[(0,[z570,z0,z9,z3,z4,z5,z6])],[(0,[z116,z0,z42,z3,z4,z5,z6]),(0,[z0,z571,z9,z3,z4,z5,z6]),(0,[z0,z9,z19,z4,z5,z248,z6]),(0,[z0,z9,z31,z4,z5,z6,z16]),(0,[z0,z9,z3,z4,z28,z5,z6]),(0,[z0,z572,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z573,z6]),(0,[z0,z9,z3,z4,z18,z5,z6]),(0,[z0,z63,z9,z3,z4,z59,z6])],[(0,[z0,z9,z19,z85,z4,z5,z6]),(0,[z0,z9,z3,z4,z574,z5,z6]),(0,[z0,z58,z9,z3,z4,z5,z151]),(0,[z0,z58,z3,z4,z5,z6,z62]),(0,[z0,z9,z575,z3,z4,z5,z6]),(0,[z0,z9,z3,z85,z4,z5,z165]),(0,[z0,z9,z3,z4,z5,z6,z576])]],
   [[(0,[z0,z344,z9,z3,z4,z5,z6]),(0,[z577,z0,z9,z3,z4,z5,z6]),(0,[z0,z578,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z129,z5,z74,z6]),(0,[z0,z3,z45,z4,z91,z5,z6]),(1,[z0,z63,z9,z3,z4,z47])],[(0,[z579,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z4,z37,z5,z6]),(0,[z30,z0,z9,z3,z4,z5,z469]),(0,[z0,z580,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z581,z6]),(0,[z0,z9,z3,z283,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z582]),(0,[z0,z60,z9,z3,z4,z5,z6])],[(0,[z0,z9,z32,z19,z4,z5,z6]),(0,[z0,z583,z9,z3,z4,z5,z6]),(0,[z406,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z584]),(0,[z0,z9,z3,z585,z4,z5,z6]),(0,[z586,z0,z9,z3,z4,z5,z6])],[(0,[z0,z587,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z293,z6,z155]),(0,[z0,z9,z98,z3,z4,z5,z6]),(0,[z0,z9,z15,z3,z4,z5,z72])],[(0,[z36,z0,z9,z98,z3,z4,z6]),(0,[z0,z9,z3,z588,z4,z5,z6]),(1,[z0,z8,z9,z4,z90,z6]),(0,[z0,z9,z3,z4,z5,z46,z6])],[(0,[z116,z10,z9,z3,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z376,z6]),(0,[z0,z9,z3,z4,z5,z589,z6]),(0,[z0,z9,z32,z3,z236,z5,z6]),(0,[z0,z9,z3,z4,z5,z590,z6]),(1,[z0,z9,z3,z404,z5,z6]),(0,[z0,z3,z4,z5,z6,z166,z47])],[(0,[z591,z0,z9,z3,z4,z5,z6]),(0,[z0,z592,z9,z3,z4,z5,z6]),(0,[z0,z76,z9,z3,z4,z5,z62]),(0,[z0,z9,z3,z4,z5,z6,z593])],[(0,[z0,z9,z19,z273,z4,z5,z6]),(0,[z30,z65,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z594,z4,z5,z6]),(0,[z595,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z423]),(0,[z0,z9,z3,z4,z596,z5,z6]),(0,[z0,z597,z9,z3,z4,z5,z6]),(0,[z0,z598,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z599,z5,z6]),(0,[z0,z80,z9,z4,z5,z75,z6]),(0,[z0,z9,z600,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z601,z6])],[(0,[z0,z9,z19,z4,z5,z72,z6]),(0,[z0,z9,z31,z4,z5,z90,z6]),(0,[z0,z9,z3,z4,z5,z6,z602]),(0,[z0,z9,z3,z4,z5,z603,z6])],[(0,[z0,z9,z3,z4,z604,z5,z6]),(0,[z0,z9,z31,z4,z59,z5,z6]),(0,[z0,z9,z3,z605,z4,z5,z6])],[(0,[z606,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z19,z4,z236,z5,z6]),(0,[z0,z9,z3,z607,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z608,z6]),(0,[z609,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z5,z6]),(0,[z0,z9,z3,z4,z5,z72,z106]),(0,[z0,z9,z610,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z611])],[(0,[z0,z58,z9,z19,z4,z5,z6]),(0,[z0,z130,z3,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z140,z5,z6]),(0,[z0,z9,z3,z4,z5,z612,z6]),(0,[z0,z9,z3,z4,z5,z613,z6]),(0,[z614,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z615]),(1,[z0,z9,z4,z5,z6,z483])],[(0,[z0,z103,z9,z31,z4,z5,z6]),(0,[z95,z9,z3,z4,z5,z6,z155]),(0,[z0,z42,z3,z137,z4,z5,z6]),(0,[z0,z58,z3,z4,z129,z5,z6]),(0,[z0,z9,z3,z4,z59,z5,z46])],[(0,[z0,z9,z31,z4,z408,z5,z6]),(0,[z0,z9,z3,z4,z5,z616,z6]),(0,[z0,z9,z3,z4,z617,z5,z6]),(0,[z0,z8,z80,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z618])]],
   [[(0,[z0,z566,z9,z3,z4,z5,z6]),(0,[z34,z0,z9,z3,z4,z71,z6]),(0,[z0,z9,z3,z96,z4,z5,z6]),(0,[z0,z60,z9,z4,z89,z5,z6])],[(0,[z0,z9,z85,z4,z89,z5,z6]),(0,[z0,z619,z9,z3,z4,z5,z6])],[(0,[z620,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z98,z4,z89,z5,z6])],[(0,[z621,z0,z9,z3,z4,z5,z6]),(0,[z0,z60,z9,z3,z4,z5,z73])],[(0,[z0,z9,z19,z4,z5,z151,z6]),(0,[z0,z9,z3,z157,z4,z5,z6]),(0,[z34,z36,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z622]),(0,[z0,z9,z3,z4,z5,z623,z6]),(0,[z0,z163,z9,z3,z4,z234,z6])],[(0,[z0,z9,z3,z4,z5,z624,z6]),(0,[z0,z206,z9,z19,z4,z5,z6]),(0,[z0,z63,z9,z3,z4,z5,z47]),(0,[z0,z175,z3,z4,z5,z6,z47])],[(0,[z406,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z264,z4,z5,z6]),(0,[z0,z9,z4,z5,z403,z234,z6]),(0,[z0,z9,z3,z4,z5,z46,z73])],[(0,[z0,z9,z3,z4,z5,z6,z625]),(1,[z0,z3,z4,z5,z293,z6])]],
   [[(0,[z0,z9,z3,z4,z5,z6,z626]),(0,[z627,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z85,z4,z123,z6]),(0,[z0,z9,z3,z17,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z628,z6]),(0,[z0,z9,z3,z4,z629,z5,z6]),(1,[z95,z9,z3,z4,z5,z155]),(0,[z0,z630,z9,z3,z4,z5,z6]),(0,[z0,z60,z9,z3,z4,z5,z16]),(1,[z0,z350,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z511])],[(0,[z0,z631,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z632,z6]),(0,[z0,z9,z3,z633,z4,z5,z6]),(0,[z0,z163,z9,z3,z4,z18,z6])],[(0,[z634,z0,z9,z3,z4,z5,z6]),(1,[z0,z58,z3,z4,z5,z62]),(0,[z0,z9,z3,z635,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z636,z6]),(0,[z0,z9,z31,z85,z4,z5,z6]),(0,[z0,z637,z9,z3,z4,z5,z6]),(0,[z0,z638,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z639,z5,z6]),(0,[z0,z436,z9,z4,z5,z6,z47]),(0,[z640,z0,z9,z3,z4,z5,z6])],[(0,[z291,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z641,z6]),(0,[z0,z63,z58,z9,z3,z4,z5]),(1,[z0,z9,z3,z4,z387,z6])],[(1,[z0,z9,z31,z4,z5,z6]),(1,[z0,z130,z3,z4,z5,z6]),(0,[z0,z9,z642,z3,z4,z5,z6]),(0,[z0,z60,z9,z3,z4,z5,z72]),(1,[z0,z313,z3,z4,z5,z6])],[(0,[z65,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z643,z4,z5,z6]),(0,[z0,z63,z9,z3,z404,z5,z6]),(0,[z644,z0,z9,z3,z4,z5,z6])]],
   [[(1,[z116,z100,z3,z4,z5,z6]),(0,[z0,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z13,z3,z4,z5,z6]),(0,[z645,z0,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z106,z6]),(0,[z0,z9,z21,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z646,z5,z6]),(0,[z0,z9,z3,z4,z18,z37,z6]),(0,[z0,z9,z136,z3,z4,z5,z6]),(0,[z0,z9,z3,z647,z4,z5,z6]),(0,[z0,z9,z3,z4,z648,z5,z6]),(1,[z0,z2,z3,z96,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z649]),(0,[z0,z436,z9,z3,z4,z5,z6])],[(0,[z0,z9,z650,z3,z4,z5,z6]),(1,[z0,z99,z9,z3,z5,z73])],[(0,[z0,z1,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z651]),(0,[z0,z9,z3,z45,z5,z234,z6])],[(0,[z0,z9,z19,z4,z5,z6,z16]),(0,[z30,z0,z9,z3,z4,z512,z6]),(0,[z0,z2,z3,z4,z5,z151,z6]),(0,[z0,z9,z652,z3,z4,z5,z6])],[(0,[z0,z2,z9,z31,z4,z5,z6]),(1,[z0,z9,z104,z4,z5,z6]),(0,[z0,z9,z3,z4,z653,z5,z6]),(0,[z0,z9,z3,z4,z5,z654,z6]),(0,[z0,z9,z3,z4,z655,z5,z6])],[(1,[z0,z9,z132,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z72,z6]),(0,[z36,z0,z8,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z5,z6,z656]),(0,[z0,z60,z9,z85,z4,z5,z6]),(0,[z0,z657,z9,z3,z4,z5,z6]),(0,[z0,z240,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z372,z4,z5,z6])],[(0,[z0,z9,z464,z3,z4,z5,z6]),(0,[z0,z658,z9,z3,z4,z5,z6]),(0,[z0,z659,z9,z3,z4,z5,z6]),(0,[z0,z9,z98,z3,z4,z234,z6]),(0,[z660,z0,z9,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z19,z4,z368,z5,z6]),(0,[z0,z9,z3,z4,z5,z661,z6]),(0,[z0,z9,z662,z3,z4,z5,z6]),(0,[z0,z21,z3,z4,z28,z5,z6])],[(0,[z34,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z74,z6]),(0,[z0,z663,z9,z3,z4,z5,z6])],[(1,[z0,z9,z398,z4,z5,z6]),(0,[z0,z9,z3,z407,z4,z5,z6]),(0,[z0,z9,z3,z328,z4,z5,z6]),(0,[z0,z9,z3,z4,z664,z5,z6]),(0,[z0,z58,z2,z3,z4,z5,z6]),(0,[z0,z25,z9,z4,z5,z74,z6]),(0,[z665,z0,z9,z3,z4,z5,z6]),(1,[z0,z306,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z666,z6]),(0,[z0,z9,z3,z4,z5,z72,z46])],[(0,[z0,z9,z3,z4,z667,z5,z6])],[(0,[z10,z0,z3,z4,z5,z151,z6]),(0,[z0,z100,z9,z19,z4,z5,z6]),(0,[z0,z8,z9,z31,z4,z5,z6]),(0,[z0,z190,z9,z3,z4,z5,z6]),(0,[z0,z668,z9,z3,z4,z5,z6]),(1,[z36,z9,z3,z4,z37,z6]),(0,[z0,z669,z9,z3,z4,z5,z6])],[(0,[z10,z0,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z72,z155]),(0,[z670,z0,z9,z3,z4,z5,z6]),(0,[z0,z671,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z17,z18,z5,z6])],[(1,[z0,z70,z9,z3,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z336]),(0,[z0,z631,z9,z3,z4,z5,z6])],[(0,[z0,z9,z19,z4,z5,z90,z6])]],
   [[(0,[z0,z9,z19,z4,z59,z5,z6]),(0,[z0,z70,z9,z3,z19,z5,z6]),(0,[z0,z9,z31,z4,z5,z71,z6]),(0,[z30,z0,z9,z3,z66,z5,z6]),(0,[z0,z672,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z673,z6]),(0,[z0,z9,z3,z4,z5,z234,z6])],[(0,[z291,z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z674,z5,z6]),(0,[z0,z103,z9,z3,z4,z74,z6])],[(1,[z0,z9,z3,z4,z5,z6]),(0,[z0,z675,z9,z3,z4,z5,z6]),(0,[z676,z0,z9,z3,z4,z5,z6]),(0,[z0,z80,z9,z32,z4,z5,z6]),(0,[z0,z677,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z678]),(0,[z0,z53,z9,z4,z5,z6,z73])],[(0,[z0,z9,z3,z4,z5,z6,z679]),(0,[z0,z42,z9,z31,z4,z5,z6]),(0,[z0,z9,z85,z4,z236,z5,z6]),(0,[z0,z9,z3,z4,z680,z5,z6])],[(0,[z0,z681,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z682,z4,z5,z6]),(0,[z0,z9,z3,z683,z4,z5,z6])],[(1,[z0,z135,z3,z4,z5,z6]),(0,[z0,z169,z9,z3,z4,z5,z6]),(0,[z9,z3,z66,z4,z50,z5,z6])],[(1,[z0,z9,z192,z3,z5,z6]),(0,[z0,z684,z9,z3,z4,z5,z6]),(0,[z685,z0,z9,z3,z4,z5,z6]),(0,[z686,z0,z9,z3,z4,z5,z6])],[(1,[z0,z3,z93,z4,z5,z6]),(0,[z0,z3,z4,z37,z5,z195,z6]),(0,[z0,z9,z3,z4,z687,z5,z6]),(0,[z0,z9,z3,z4,z387,z5,z6]),(0,[z0,z163,z9,z3,z5,z234,z6]),(0,[z0,z9,z3,z4,z5,z6,z688]),(0,[z0,z9,z3,z4,z5,z6,z689])]],
   [[(0,[z0,z2,z27,z3,z4,z5,z6]),(0,[z116,z0,z9,z19,z4,z5,z6]),(0,[z0,z9,z192,z19,z4,z5,z6]),(0,[z0,z63,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z690,z5,z6]),(0,[z0,z9,z3,z4,z5,z691,z6]),(0,[z0,z692,z9,z3,z4,z5,z6])],[(0,[z10,z0,z9,z398,z4,z5,z6]),(0,[z36,z0,z9,z464,z4,z5,z6]),(0,[z0,z2,z9,z3,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z307]),(0,[z0,z9,z3,z4,z5,z6,z693]),(0,[z694,z0,z9,z3,z4,z5,z6]),(0,[z0,z695,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z696,z5,z6]),(1,[z0,z9,z3,z4,z59,z46])],[(0,[z0,z141,z9,z19,z4,z5,z6]),(0,[z0,z76,z3,z4,z5,z151,z6])],[(0,[z0,z9,z3,z4,z5,z370,z6]),(0,[z0,z76,z9,z31,z4,z5,z6]),(1,[z0,z9,z3,z4,z5,z153]),(1,[z0,z9,z35,z4,z5,z6])],[(0,[z0,z9,z49,z3,z19,z4,z5]),(0,[z0,z9,z31,z66,z4,z5,z6]),(0,[z0,z80,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z469]),(0,[z0,z9,z3,z4,z5,z697,z6]),(0,[z0,z9,z3,z17,z4,z234,z6])],[(0,[z698,z0,z9,z3,z4,z5,z6]),(0,[z34,z0,z9,z3,z4,z5,z6]),(0,[z699,z0,z9,z3,z4,z5,z6]),(1,[z0,z9,z4,z5,z185,z6]),(0,[z0,z700,z9,z3,z4,z5,z6]),(0,[z0,z701,z9,z3,z4,z5,z6]),(0,[z0,z702,z9,z3,z4,z5,z6])],[(0,[z291,z9,z3,z19,z4,z5,z6]),(0,[z0,z9,z3,z703,z4,z5,z6]),(0,[z0,z9,z3,z4,z704,z5,z6]),(0,[z0,z80,z9,z3,z236,z5,z6]),(0,[z0,z9,z3,z4,z5,z6,z483])],[(0,[z0,z705,z9,z3,z4,z5,z6]),(0,[z0,z3,z4,z28,z5,z151,z6]),(0,[z0,z706,z9,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z9,z3,z4,z5,z707]),(0,[z0,z9,z19,z4,z6,z708]),(0,[z0,z9,z19,z4,z5,z194]),(0,[z95,z9,z3,z4,z5,z155]),(0,[z0,z9,z3,z4,z5,z709]),(0,[z0,z9,z710,z4,z5,z6]),(0,[z0,z350,z9,z4,z5,z6]),(0,[z0,z711,z3,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z712]),(0,[z65,z9,z19,z66,z5,z6]),(0,[z0,z713,z3,z4,z5,z6]),(0,[z0,z9,z3,z714,z5,z6]),(0,[z0,z436,z63,z9,z4,z47])],[(0,[z0,z9,z3,z4,z5,z715]),(0,[z0,z112,z9,z4,z90,z6]),(0,[z0,z9,z3,z5,z6,z716]),(0,[z0,z9,z4,z5,z6,z717]),(0,[z565,z9,z3,z4,z5,z155]),(0,[z0,z718,z3,z4,z5,z6]),(0,[z0,z9,z3,z348,z5,z73])],[(0,[z0,z719,z3,z4,z5,z6]),(0,[z0,z105,z9,z3,z234,z6]),(0,[z0,z720,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z721,z6]),(0,[z0,z63,z115,z3,z4,z47])],[(0,[z34,z9,z19,z4,z71,z6]),(0,[z0,z112,z29,z9,z19,z4]),(0,[z0,z631,z21,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z722]),(0,[z0,z9,z3,z4,z387,z6]),(0,[z0,z60,z9,z4,z387,z6]),(0,[z0,z723,z3,z4,z5,z6])],[(0,[z0,z9,z3,z724,z5,z6]),(0,[z0,z164,z9,z31,z4,z5]),(0,[z0,z9,z15,z283,z4,z5]),(0,[z0,z76,z3,z4,z5,z151]),(0,[z0,z9,z3,z4,z5,z725]),(0,[z0,z9,z726,z404,z5,z6])],[(0,[z116,z727,z3,z4,z5,z6]),(0,[z0,z9,z3,z5,z6,z728]),(0,[z0,z80,z9,z596,z5,z6]),(0,[z0,z9,z729,z4,z5,z6])],[(0,[z0,z9,z730,z4,z5,z6])]],
   [[(0,[z0,z70,z29,z9,z4,z5]),(0,[z0,z9,z4,z5,z6,z731]),(0,[z0,z3,z4,z5,z732,z6])],[(0,[z30,z3,z93,z50,z5,z6]),(0,[z0,z99,z9,z3,z5,z73])],[(0,[z0,z3,z4,z733,z5,z6]),(0,[z0,z9,z734,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z735]),(0,[z0,z102,z19,z4,z5,z6]),(0,[z0,z9,z3,z736,z5,z6]),(0,[z0,z737,z3,z4,z5,z6]),(0,[z0,z175,z4,z5,z6,z511])],[(0,[z0,z9,z738,z4,z5,z6]),(0,[z0,z9,z739,z4,z5,z6]),(0,[z0,z70,z135,z19,z5,z6]),(0,[z0,z9,z19,z4,z5,z740]),(0,[z0,z103,z31,z4,z129,z6]),(0,[z0,z9,z31,z4,z5,z307]),(0,[z0,z80,z9,z332,z5,z6]),(0,[z0,z80,z9,z104,z5,z6]),(0,[z0,z3,z741,z4,z5,z6]),(0,[z0,z9,z3,z4,z6,z742]),(0,[z9,z3,z4,z5,z743,z6]),(0,[z0,z63,z9,z3,z372,z47])],[(0,[z0,z42,z135,z4,z5,z6]),(0,[z0,z9,z13,z4,z89,z6]),(0,[z0,z163,z9,z3,z744,z6])],[(0,[z0,z9,z19,z4,z123,z6]),(0,[z0,z9,z745,z4,z5,z6]),(0,[z0,z9,z746,z4,z5,z6]),(1,[z0,z9,z4,z5,z747]),(0,[z0,z9,z3,z5,z725,z73])],[(0,[z0,z748,z9,z19,z5,z6]),(0,[z0,z9,z3,z4,z749,z6]),(0,[z0,z750,z9,z4,z5,z6]),(0,[z0,z751,z3,z4,z5,z6]),(0,[z0,z752,z3,z4,z5,z6]),(0,[z0,z63,z175,z3,z4,z5])]],
   [[(0,[z0,z130,z232,z4,z5,z6]),(0,[z0,z9,z3,z4,z753,z6]),(0,[z0,z9,z754,z4,z5,z6]),(0,[z0,z130,z4,z368,z5,z6]),(0,[z0,z755,z9,z19,z4,z6]),(0,[z0,z756,z3,z4,z5,z6]),(0,[z757,z9,z3,z4,z5,z6]),(0,[z0,z53,z99,z9,z5,z73])],[(0,[z0,z183,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z758,z6]),(0,[z0,z9,z19,z5,z759,z6]),(0,[z0,z306,z3,z4,z5,z6]),(0,[z0,z76,z3,z4,z5,z589])],[(0,[z0,z9,z192,z31,z5,z6]),(0,[z0,z9,z19,z760,z5,z6]),(0,[z0,z29,z9,z4,z89,z5]),(0,[z0,z9,z192,z104,z5,z6]),(0,[z0,z761,z3,z4,z5,z6]),(0,[z0,z9,z762,z4,z5,z6]),(0,[z0,z3,z4,z5,z151,z763]),(0,[z0,z3,z4,z7,z387,z6]),(0,[z0,z115,z3,z404,z5,z6])],[(0,[z116,z0,z3,z4,z5,z268]),(0,[z30,z379,z9,z3,z5,z6])],[(0,[z0,z9,z764,z4,z5,z6]),(0,[z0,z63,z9,z19,z4,z47]),(0,[z0,z9,z765,z4,z5,z6])],[(0,[z0,z70,z9,z3,z5,z6]),(0,[z0,z9,z373,z4,z140,z6]),(0,[z0,z766,z9,z3,z4,z6]),(0,[z0,z9,z3,z767,z5,z6]),(0,[z0,z163,z9,z3,z234,z156])],[(0,[z0,z9,z19,z4,z5,z768]),(0,[z0,z9,z769,z4,z5,z6]),(0,[z0,z3,z4,z5,z770,z6]),(0,[z0,z2,z3,z362,z5,z6]),(0,[z0,z3,z300,z28,z5,z6]),(0,[z0,z9,z3,z4,z771,z6]),(0,[z0,z9,z3,z17,z744,z6]),(0,[z0,z772,z9,z404,z5,z6])],[(0,[z0,z112,z29,z9,z3,z4]),(0,[z0,z3,z4,z5,z6,z773]),(0,[z0,z60,z9,z4,z5,z282]),(0,[z0,z8,z9,z267,z4,z6]),(0,[z0,z3,z774,z28,z5,z6]),(0,[z0,z3,z4,z5,z775,z6]),(0,[z0,z3,z4,z776,z5,z6])]],
   [[(0,[z0,z9,z777,z4,z5,z6]),(0,[z0,z3,z4,z5,z195,z6]),(0,[z29,z9,z31,z19,z4,z5]),(0,[z0,z3,z4,z5,z6,z778]),(0,[z0,z509,z9,z4,z5,z282])],[(0,[z0,z2,z3,z278,z5,z6]),(0,[z0,z9,z19,z4,z779,z5]),(0,[z0,z169,z3,z4,z512,z6]),(0,[z0,z164,z3,z4,z28,z5])],[(0,[z10,z493,z3,z4,z5,z6]),(0,[z0,z780,z3,z4,z5,z6]),(0,[z0,z9,z3,z781,z5,z6]),(0,[z0,z183,z3,z4,z5,z153]),(0,[z0,z141,z4,z185,z74,z6])],[(0,[z0,z9,z3,z782,z5,z6]),(0,[z0,z9,z3,z4,z783,z6]),(0,[z0,z9,z784,z4,z5,z6]),(0,[z0,z130,z49,z3,z4,z5]),(0,[z0,z163,z9,z31,z234,z6]),(0,[z0,z785,z9,z4,z5,z6]),(0,[z0,z786,z3,z4,z5,z6])],[(0,[z0,z1,z31,z28,z5,z6]),(0,[z0,z9,z127,z157,z5,z6]),(0,[z0,z87,z3,z28,z5,z6]),(0,[z0,z9,z4,z403,z123,z6])],[(0,[z0,z9,z215,z4,z5,z6]),(0,[z0,z112,z344,z9,z4,z6]),(0,[z0,z787,z9,z3,z4,z5]),(0,[z9,z3,z4,z5,z749,z6]),(0,[z0,z9,z4,z5,z6,z788]),(0,[z0,z9,z85,z5,z428,z6])],[(0,[z0,z3,z93,z4,z5,z6]),(0,[z116,z100,z54,z4,z5,z6]),(0,[z0,z789,z9,z3,z4,z6]),(0,[z0,z183,z3,z4,z512,z6]),(0,[z0,z9,z790,z4,z5,z6]),(0,[z0,z9,z3,z791,z5,z6]),(0,[z0,z9,z3,z792,z5,z6])],[(0,[z0,z793,z9,z3,z5,z6]),(0,[z0,z9,z3,z4,z6,z794]),(0,[z0,z63,z9,z31,z4,z47]),(0,[z0,z9,z32,z332,z5,z6]),(0,[z0,z9,z3,z4,z177,z469]),(0,[z0,z9,z795,z4,z5,z6]),(0,[z0,z9,z32,z104,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z5,z796]),(0,[z0,z9,z3,z4,z5,z797]),(0,[z30,z9,z3,z50,z177,z6]),(0,[z0,z9,z3,z4,z5,z798]),(0,[z0,z103,z3,z4,z129,z6]),(0,[z0,z9,z3,z4,z5,z307]),(0,[z0,z60,z9,z4,z5,z307]),(0,[z0,z8,z9,z4,z403,z6])],[(0,[z0,z3,z96,z460,z5,z6]),(0,[z116,z0,z164,z3,z4,z5]),(0,[z0,z19,z4,z5,z799,z6]),(0,[z0,z9,z31,z4,z177,z6]),(0,[z0,z9,z800,z4,z5,z6])],[(0,[z0,z801,z9,z19,z4,z5]),(0,[z0,z112,z9,z4,z75,z6]),(1,[z0,z3,z4,z802,z6]),(0,[z0,z803,z3,z4,z5,z6])],[(0,[z135,z31,z19,z4,z5,z6]),(0,[z0,z804,z9,z4,z5,z6]),(0,[z0,z9,z805,z4,z5,z6]),(0,[z0,z9,z806,z4,z5,z6]),(0,[z0,z9,z32,z85,z387,z6]),(0,[z0,z807,z3,z4,z5,z6])],[(0,[z0,z9,z232,z4,z5,z6]),(0,[z0,z29,z135,z19,z4,z5]),(0,[z0,z3,z4,z808,z5,z6]),(0,[z0,z9,z809,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z810]),(0,[z0,z9,z3,z4,z744,z6])],[(0,[z0,z811,z9,z3,z5,z6]),(0,[z0,z9,z19,z4,z5,z469]),(0,[z9,z3,z4,z5,z812,z155]),(0,[z0,z9,z4,z89,z771,z6])],[(0,[z0,z103,z3,z4,z359,z6]),(0,[z9,z19,z4,z287,z5,z6]),(0,[z0,z29,z9,z4,z5,z336]),(0,[z0,z9,z85,z714,z5,z6])],[(0,[z0,z813,z9,z19,z4,z5]),(0,[z0,z814,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z763]),(0,[z0,z815,z9,z4,z5,z156])]],
   [[(0,[z0,z9,z816,z4,z5,z6]),(0,[z0,z112,z70,z9,z4,z6]),(0,[z0,z112,z9,z98,z4,z6]),(0,[z0,z164,z3,z4,z5,z62]),(0,[z0,z63,z3,z4,z166,z47])],[(0,[z0,z383,z19,z4,z5,z6]),(0,[z0,z112,z42,z9,z4,z6]),(0,[z146,z9,z3,z4,z5,z812]),(0,[z0,z3,z4,z5,z817,z6])],[(0,[z727,z9,z3,z4,z5,z6]),(0,[z0,z9,z818,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z819]),(0,[z0,z9,z820,z4,z5,z6])],[(0,[z0,z9,z192,z85,z5,z6]),(0,[z0,z821,z31,z4,z5,z6]),(0,[z0,z115,z31,z4,z5,z6]),(0,[z0,z9,z15,z4,z5,z204]),(0,[z0,z25,z9,z4,z5,z6]),(0,[z0,z9,z4,z5,z822,z6]),(0,[z0,z103,z3,z4,z562,z6]),(0,[z0,z9,z3,z4,z5,z823])],[(0,[z0,z31,z824,z4,z5,z6]),(0,[z146,z9,z283,z4,z5,z106]),(0,[z0,z9,z4,z5,z329,z185]),(0,[z0,z164,z115,z3,z4,z5]),(0,[z0,z825,z3,z4,z5,z6]),(0,[z0,z826,z3,z4,z5,z6])],[(0,[z0,z827,z31,z4,z5,z6]),(0,[z0,z9,z98,z4,z140,z6]),(0,[z0,z60,z9,z283,z4,z5]),(0,[z0,z25,z141,z4,z74,z6]),(0,[z0,z828,z3,z4,z5,z6])],[(0,[z0,z21,z232,z4,z5,z6]),(0,[z0,z9,z3,z829,z5,z6]),(0,[z0,z9,z3,z4,z830,z6]),(0,[z0,z831,z9,z3,z5,z6]),(0,[z0,z9,z3,z4,z5,z832]),(0,[z0,z3,z4,z7,z5,z307])],[(0,[z10,z389,z3,z4,z5,z6]),(0,[z0,z70,z9,z13,z19,z6]),(0,[z0,z9,z19,z4,z5,z833]),(0,[z0,z9,z49,z3,z4,z5]),(0,[z0,z834,z104,z4,z5,z6]),(0,[z0,z835,z9,z3,z4,z6]),(0,[z0,z9,z3,z4,z836,z6]),(0,[z0,z9,z837,z4,z5,z6]),(0,[z0,z53,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z46,z838])]],
   [[(0,[z0,z9,z54,z4,z5,z6]),(0,[z0,z9,z839,z4,z5,z6]),(0,[z0,z19,z4,z840,z5,z6]),(0,[z0,z1,z3,z28,z5,z6]),(0,[z0,z9,z3,z4,z841,z6])],[(0,[z0,z9,z842,z4,z5,z6]),(0,[z0,z130,z21,z4,z5,z6]),(0,[z0,z9,z49,z4,z5,z75]),(0,[z0,z566,z9,z4,z376,z6]),(0,[z0,z9,z3,z5,z6,z843]),(0,[z0,z844,z3,z4,z5,z6]),(0,[z0,z60,z9,z4,z5,z16])],[(0,[z0,z112,z9,z19,z4,z6]),(0,[z0,z9,z13,z4,z368,z6]),(0,[z0,z135,z49,z3,z4,z5]),(0,[z0,z9,z332,z4,z5,z469]),(0,[z0,z9,z3,z442,z5,z73]),(0,[z0,z9,z726,z4,z5,z6])],[(0,[z0,z135,z54,z4,z5,z6]),(0,[z0,z9,z19,z4,z5,z423]),(0,[z0,z112,z70,z9,z19,z6]),(0,[z30,z9,z332,z50,z5,z6]),(0,[z0,z9,z3,z845,z5,z6]),(0,[z846,z9,z3,z4,z5,z6]),(0,[z9,z3,z4,z5,z6,z847]),(0,[z0,z9,z848,z4,z5,z6]),(0,[z0,z9,z3,z5,z539,z73])],[(0,[z0,z9,z3,z4,z849,z6]),(0,[z0,z9,z3,z4,z850,z6]),(0,[z0,z9,z315,z4,z5,z469]),(0,[z0,z9,z3,z851,z5,z6])],[(0,[z10,z27,z19,z4,z5,z6]),(0,[z0,z852,z9,z4,z5,z6]),(0,[z0,z853,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z177,z6]),(0,[z30,z9,z315,z50,z5,z6]),(0,[z0,z9,z3,z4,z5,z854])],[(0,[z0,z130,z192,z19,z5,z6]),(0,[z0,z9,z3,z4,z5,z855]),(0,[z0,z3,z4,z856,z5,z6]),(0,[z0,z436,z4,z5,z6,z166]),(0,[z0,z857,z9,z4,z5,z6])],[(0,[z0,z9,z858,z4,z5,z6]),(0,[z70,z9,z31,z19,z5,z6]),(0,[z0,z9,z192,z13,z19,z6]),(0,[z0,z9,z31,z4,z5,z156]),(0,[z9,z3,z4,z749,z71,z6]),(0,[z0,z313,z3,z4,z5,z156]),(0,[z0,z9,z3,z4,z5,z838])]],
   [[(0,[z10,z572,z3,z4,z5,z6]),(1,[z0,z112,z130,z4,z6]),(0,[z0,z9,z3,z4,z5,z859]),(0,[z0,z9,z3,z4,z387,z165])],[(0,[z203,z9,z19,z4,z5,z6]),(1,[z0,z112,z70,z9,z6]),(0,[z0,z9,z31,z4,z5,z165]),(0,[z0,z3,z4,z91,z5,z6]),(0,[z0,z9,z860,z4,z5,z6]),(0,[z0,z9,z3,z18,z744,z6])],[(0,[z0,z21,z54,z4,z5,z6]),(0,[z30,z169,z3,z50,z5,z6]),(0,[z0,z861,z3,z4,z5,z6])],[(0,[z48,z9,z31,z4,z5,z6]),(0,[z0,z9,z19,z4,z862,z6]),(1,[z0,z112,z29,z9,z4]),(0,[z0,z29,z9,z85,z4,z5]),(0,[z0,z169,z31,z4,z5,z6]),(0,[z0,z9,z3,z863,z5,z6])],[(0,[z0,z1,z3,z604,z5,z6]),(0,[z218,z9,z19,z4,z5,z6]),(0,[z0,z834,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z864,z6]),(0,[z0,z9,z865,z4,z5,z6]),(0,[z0,z8,z9,z4,z771,z6]),(0,[z0,z63,z9,z3,z4,z838])],[(0,[z0,z164,z9,z19,z4,z5]),(0,[z0,z9,z3,z4,z866,z6]),(0,[z0,z3,z4,z5,z867,z6]),(0,[z0,z637,z9,z3,z5,z73]),(0,[z0,z868,z9,z4,z5,z6]),(0,[z0,z9,z3,z17,z5,z156])],[(0,[z0,z9,z3,z4,z177,z153]),(0,[z0,z9,z3,z4,z5,z869]),(0,[z95,z9,z136,z4,z5,z155]),(0,[z0,z141,z3,z4,z329,z74])],[(0,[z286,z9,z19,z4,z5,z6]),(0,[z0,z9,z3,z870,z5,z6]),(0,[z0,z821,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z6,z871]),(0,[z0,z115,z3,z4,z5,z6]),(0,[z0,z9,z32,z85,z5,z307]),(0,[z0,z240,z3,z404,z5,z6])]],
   [[(0,[z0,z9,z4,z5,z872,z6]),(0,[z0,z9,z3,z4,z5,z873]),(0,[z0,z9,z31,z4,z5,z268]),(0,[z257,z9,z31,z4,z5,z6]),(0,[z0,z9,z874,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z875]),(0,[z876,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z744,z234,z6])],[(0,[z0,z130,z13,z19,z4,z6]),(0,[z0,z99,z9,z31,z5,z73]),(0,[z0,z175,z31,z4,z5,z6]),(0,[z0,z827,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z877]),(0,[z0,z9,z3,z404,z5,z46])],[(0,[z0,z112,z9,z192,z19,z6]),(0,[z0,z70,z9,z13,z3,z6]),(0,[z0,z9,z3,z4,z878,z6]),(0,[z0,z9,z31,z372,z5,z6]),(0,[z0,z3,z4,z802,z74,z6]),(0,[z0,z879,z3,z4,z5,z6])],[(0,[z9,z49,z31,z19,z4,z5]),(0,[z0,z2,z3,z96,z5,z268]),(0,[z0,z306,z3,z4,z5,z156]),(0,[z0,z772,z9,z4,z5,z6])],[(0,[z0,z112,z29,z9,z4,z6]),(0,[z0,z9,z3,z4,z5,z880]),(0,[z0,z31,z881,z4,z5,z6]),(0,[z544,z9,z31,z4,z5,z6]),(0,[z0,z9,z882,z4,z5,z6]),(0,[z0,z9,z3,z4,z883,z6]),(0,[z0,z9,z4,z5,z747,z16]),(0,[z0,z884,z3,z4,z5,z6])],[(0,[z9,z19,z4,z374,z5,z6])],[(0,[z116,z3,z78,z4,z5,z6]),(0,[z9,z13,z31,z19,z4,z6]),(0,[z0,z112,z70,z9,z3,z6]),(0,[z705,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z885]),(0,[z0,z9,z886,z4,z5,z6])],[(0,[z685,z9,z19,z4,z5,z6]),(0,[z0,z887,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z888,z6]),(0,[z0,z163,z306,z3,z234,z6]),(0,[z0,z9,z3,z5,z744,z6]),(0,[z0,z3,z889,z4,z5,z6])]],
   [[(0,[z0,z9,z19,z4,z512,z6]),(0,[z0,z130,z135,z4,z5,z6]),(0,[z0,z890,z19,z4,z5,z6]),(0,[z0,z9,z891,z3,z4,z5]),(0,[z0,z9,z892,z4,z5,z6]),(0,[z0,z9,z4,z5,z75,z747])],[(0,[z0,z112,z135,z3,z4,z6]),(0,[z0,z80,z9,z192,z5,z6]),(0,[z0,z9,z3,z4,z5,z893]),(0,[z0,z9,z3,z4,z838,z47])],[(0,[z0,z9,z192,z19,z5,z6]),(0,[z0,z9,z192,z13,z3,z6]),(0,[z0,z9,z3,z4,z894,z6]),(0,[z0,z895,z9,z4,z5,z6]),(0,[z0,z9,z98,z35,z4,z6]),(0,[z0,z9,z15,z328,z4,z5]),(0,[z0,z21,z4,z439,z5,z6]),(0,[z0,z896,z3,z4,z5,z6]),(0,[z0,z560,z9,z3,z4,z47])],[(0,[z0,z9,z897,z4,z5,z6]),(0,[z0,z9,z19,z5,z898,z6]),(0,[z0,z899,z9,z4,z5,z6]),(0,[z0,z9,z900,z4,z5,z6]),(0,[z0,z3,z4,z5,z763,z62]),(0,[z0,z9,z3,z4,z5,z156])],[],[(0,[z0,z70,z9,z31,z5,z6]),(0,[z0,z135,z192,z19,z5,z6]),(0,[z0,z70,z130,z3,z5,z6]),(0,[z0,z70,z9,z332,z5,z6]),(0,[z487,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z901]),(0,[z0,z3,z4,z5,z6,z166]),(0,[z0,z9,z3,z4,z5,z165]),(0,[z0,z9,z3,z4,z5,z902])],[(0,[z0,z9,z903,z4,z5,z6]),(0,[z0,z9,z168,z4,z5,z6]),(0,[z0,z3,z4,z904,z5,z6]),(0,[z0,z42,z407,z4,z5,z6]),(0,[z0,z9,z4,z5,z905,z6]),(0,[z0,z9,z906,z4,z5,z6]),(0,[z0,z9,z3,z4,z907,z6]),(0,[z0,z9,z3,z4,z387,z307])],[(0,[z0,z169,z3,z4,z5,z6]),(0,[z0,z102,z31,z4,z5,z6]),(0,[z0,z31,z4,z5,z293,z6]),(0,[z0,z141,z31,z4,z74,z6]),(0,[z0,z174,z3,z4,z74,z6])]],
   [[(0,[z36,z3,z4,z37,z195,z6]),(0,[z0,z80,z9,z236,z5,z6]),(0,[z0,z122,z3,z4,z387,z6]),(0,[z0,z9,z15,z4,z5,z75])],[(0,[z0,z9,z19,z404,z5,z6]),(0,[z0,z908,z3,z4,z5,z6]),(0,[z0,z122,z31,z4,z5,z6]),(0,[z909,z9,z3,z4,z5,z6])],[(0,[z0,z9,z910,z4,z5,z6]),(0,[z0,z9,z3,z4,z911,z6]),(0,[z0,z9,z3,z4,z5,z912]),(0,[z0,z70,z9,z32,z5,z6]),(0,[z0,z9,z31,z4,z123,z6]),(0,[z0,z9,z3,z4,z913,z6]),(0,[z0,z914,z3,z4,z5,z6]),(0,[z0,z915,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z916,z6]),(0,[z0,z25,z2,z4,z5,z6])],[(0,[z0,z9,z4,z5,z917,z6]),(0,[z0,z163,z9,z19,z234,z6]),(0,[z0,z918,z9,z4,z5,z6])],[(0,[z0,z919,z104,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z920]),(0,[z0,z9,z3,z4,z5,z921]),(0,[z0,z9,z3,z4,z5,z268]),(0,[z0,z9,z922,z4,z5,z6])],[(0,[z0,z9,z923,z4,z5,z6]),(0,[z0,z29,z9,z49,z4,z5]),(0,[z0,z112,z9,z192,z3,z6]),(0,[z0,z9,z332,z4,z512,z6]),(0,[z0,z3,z4,z5,z6,z924]),(0,[z0,z175,z3,z4,z5,z6]),(0,[z0,z9,z925,z4,z5,z6])],[(0,[z0,z9,z3,z4,z926,z6]),(0,[z0,z9,z3,z5,z6,z927]),(0,[z9,z928,z3,z4,z5,z6]),(0,[z0,z9,z3,z372,z5,z6])],[(0,[z0,z9,z136,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z929]),(0,[z0,z9,z315,z4,z512,z6]),(0,[z0,z9,z4,z5,z930,z6]),(0,[z0,z58,z3,z4,z704,z5]),(0,[z0,z80,z9,z305,z5,z6]),(0,[z0,z9,z931,z4,z5,z6])]],
   [[(0,[z0,z9,z3,z4,z6,z708]),(0,[z0,z240,z31,z4,z5,z6]),(0,[z0,z169,z3,z4,z5,z153]),(0,[z0,z9,z3,z4,z5,z932]),(0,[z0,z9,z933,z4,z5,z6]),(0,[z0,z9,z3,z774,z5,z6])],[(0,[z0,z9,z4,z5,z6,z934]),(0,[z0,z58,z3,z4,z5,z763])],[(0,[z0,z29,z9,z19,z4,z5]),(0,[z0,z9,z19,z4,z5,z935]),(0,[z0,z9,z4,z5,z936,z6]),(0,[z0,z3,z4,z5,z937,z6]),(0,[z0,z42,z137,z4,z5,z6]),(0,[z0,z9,z938,z4,z5,z6]),(0,[z0,z63,z9,z3,z404,z47])],[(0,[z0,z19,z4,z7,z5,z6]),(0,[z0,z9,z741,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z939]),(0,[z0,z940,z9,z4,z5,z6]),(0,[z941,z9,z3,z4,z5,z6]),(0,[z0,z942,z3,z4,z5,z6]),(0,[z0,z3,z4,z7,z5,z165])],[(0,[z0,z9,z943,z4,z5,z6]),(0,[z0,z9,z4,z89,z5,z165])],[(0,[z0,z944,z31,z4,z5,z6]),(0,[z0,z945,z3,z4,z5,z6]),(0,[z36,z102,z3,z4,z37,z6]),(0,[z0,z946,z3,z4,z5,z6]),(0,[z0,z58,z9,z3,z404,z5]),(0,[z0,z8,z122,z4,z5,z6]),(0,[z0,z9,z98,z4,z771,z6])],[],[(0,[z112,z9,z31,z19,z4,z6]),(0,[z0,z947,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z948])]],
   [[(0,[z0,z9,z13,z31,z4,z6])],[(0,[z0,z9,z19,z4,z5,z949]),(0,[z0,z9,z4,z5,z950,z6]),(0,[z0,z8,z29,z9,z4,z5]),(0,[z0,z919,z3,z4,z5,z6]),(0,[z0,z9,z951,z4,z5,z6]),(0,[z0,z9,z3,z952,z5,z6])],[(0,[z0,z9,z3,z953,z4,z5]),(0,[z0,z954,z3,z4,z5,z6]),(0,[z0,z58,z3,z4,z5,z530])],[(0,[z0,z102,z3,z4,z5,z6]),(0,[z621,z27,z3,z4,z5,z6]),(0,[z9,z31,z955,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z956]),(0,[z30,z190,z3,z50,z5,z6]),(0,[z0,z3,z4,z5,z957,z6]),(0,[z0,z141,z3,z4,z74,z6])],[(0,[z9,z19,z271,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z740]),(0,[z0,z190,z31,z4,z5,z6]),(0,[z0,z141,z3,z4,z802,z6])],[(0,[z0,z9,z3,z4,z958,z6]),(0,[z0,z29,z9,z31,z4,z5]),(0,[z95,z9,z19,z4,z5,z155]),(0,[z0,z9,z19,z4,z959,z6]),(0,[z0,z960,z9,z19,z4,z6]),(0,[z0,z29,z130,z3,z4,z5]),(0,[z0,z122,z3,z4,z5,z6]),(0,[z0,z21,z741,z4,z5,z6]),(0,[z0,z141,z164,z3,z4,z74]),(0,[z0,z9,z4,z771,z90,z6]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z163,z9,z3,z234,z194])],[(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z9,z963,z4,z5,z6]),(0,[z0,z9,z3,z4,z123,z6])],[(0,[z0,z9,z49,z31,z4,z5]),(0,[z0,z58,z19,z4,z5,z62]),(0,[z0,z9,z3,z4,z964,z6]),(0,[z0,z835,z9,z104,z4,z6]),(0,[z0,z3,z4,z965,z5,z6]),(0,[z0,z175,z3,z4,z5,z73])]],
   [[(0,[z0,z966,z31,z4,z5,z6]),(0,[z30,z9,z3,z50,z5,z469]),(0,[z0,z9,z967,z4,z5,z6]),(0,[z0,z968,z3,z4,z5,z6]),(0,[z0,z560,z9,z3,z234,z6])],[(0,[z0,z9,z969,z4,z5,z6]),(0,[z30,z9,z19,z50,z5,z6]),(0,[z0,z9,z19,z4,z387,z6]),(0,[z0,z9,z3,z5,z759,z6]),(0,[z0,z9,z970,z4,z5,z6]),(0,[z0,z63,z9,z3,z4,z120]),(0,[z0,z76,z115,z3,z4,z5])],[(0,[z0,z9,z3,z760,z5,z6]),(0,[z0,z9,z955,z4,z5,z6]),(0,[z0,z130,z19,z4,z5,z6]),(0,[z0,z112,z130,z19,z4,z6]),(0,[z0,z29,z9,z192,z19,z5]),(0,[z0,z313,z19,z4,z5,z6]),(0,[z0,z44,z31,z4,z5,z6]),(0,[z0,z9,z3,z971,z5,z6]),(0,[z0,z9,z4,z5,z6,z972]),(0,[z0,z9,z3,z973,z5,z6])],[(0,[z0,z84,z3,z28,z5,z6]),(0,[z0,z9,z3,z4,z5,z974]),(0,[z0,z70,z9,z368,z5,z6]),(0,[z0,z9,z19,z5,z6,z728]),(0,[z0,z112,z206,z9,z4,z6]),(0,[z435,z9,z31,z4,z5,z6])],[(0,[z727,z27,z3,z4,z5,z6]),(0,[z116,z100,z19,z4,z5,z6]),(0,[z0,z8,z9,z35,z4,z6]),(0,[z0,z240,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z975]),(0,[z0,z9,z32,z85,z5,z165])],[(0,[z0,z9,z19,z976,z4,z6]),(0,[z0,z2,z19,z96,z5,z6]),(0,[z0,z383,z31,z4,z5,z6]),(0,[z224,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z977]),(0,[z0,z978,z3,z4,z5,z6])],[(0,[z0,z979,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z768])],[(0,[z0,z70,z9,z89,z5,z6]),(0,[z0,z31,z93,z4,z5,z6]),(0,[z0,z980,z3,z4,z5,z6]),(0,[z36,z9,z267,z4,z37,z6]),(0,[z0,z436,z9,z4,z5,z6])]],
   [[(0,[z0,z183,z3,z4,z177,z6]),(0,[z0,z9,z3,z4,z5,z981]),(0,[z0,z982,z4,z5,z195,z6]),(0,[z0,z9,z4,z5,z6,z983])],[(0,[z116,z3,z4,z5,z691,z6]),(0,[z0,z9,z4,z5,z984,z6]),(0,[z0,z9,z3,z4,z779,z5]),(0,[z0,z944,z3,z4,z5,z6]),(0,[z0,z985,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z986,z6]),(0,[z0,z60,z9,z328,z4,z5]),(0,[z0,z206,z4,z5,z339,z6]),(0,[z0,z175,z3,z4,z5,z72]),(0,[z0,z9,z3,z404,z5,z47])],[(0,[z0,z9,z714,z236,z5,z6]),(0,[z0,z8,z9,z4,z5,z165]),(0,[z0,z9,z4,z5,z483,z307])],[(0,[z0,z9,z3,z4,z5,z987]),(0,[z0,z988,z3,z4,z5,z6]),(0,[z0,z813,z9,z3,z4,z5]),(0,[z0,z3,z4,z5,z989,z6]),(0,[z0,z3,z4,z7,z123,z6]),(0,[z0,z122,z4,z89,z5,z6])],[(0,[z0,z19,z4,z5,z293,z6]),(0,[z0,z9,z267,z4,z5,z6]),(0,[z0,z990,z3,z4,z5,z6]),(0,[z0,z9,z991,z4,z5,z6]),(0,[z36,z9,z464,z4,z37,z6]),(0,[z0,z9,z4,z89,z123,z6])],[(0,[z0,z70,z9,z49,z19,z5]),(0,[z0,z306,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z329])],[(0,[z9,z31,z19,z4,z5,z6]),(0,[z0,z112,z130,z9,z4,z6]),(0,[z0,z8,z130,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z423]),(0,[z0,z9,z3,z4,z5,z956]),(0,[z0,z992,z3,z4,z5,z6]),(0,[z0,z3,z4,z129,z6,z417]),(0,[z0,z993,z9,z4,z5,z6]),(0,[z0,z9,z4,z5,z994,z6]),(0,[z0,z995,z3,z4,z5,z6])]],
   [[(0,[z0,z190,z3,z4,z5,z6]),(0,[z36,z9,z19,z4,z37,z6]),(0,[z0,z112,z29,z9,z4,z5]),(0,[z0,z31,z4,z7,z5,z6]),(0,[z0,z42,z294,z4,z5,z6]),(0,[z0,z996,z9,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z997])],[(0,[z10,z27,z31,z4,z5,z6]),(0,[z10,z705,z3,z4,z5,z6]),(0,[z9,z192,z31,z19,z5,z6]),(0,[z0,z99,z9,z19,z5,z73]),(0,[z193,z9,z31,z4,z5,z6]),(0,[z0,z9,z998,z4,z5,z6])],[(0,[z0,z344,z135,z4,z5,z6]),(0,[z0,z999,z19,z4,z5,z6]),(0,[z146,z9,z31,z4,z5,z106]),(0,[z0,z80,z9,z408,z5,z6]),(0,[z95,z9,z3,z4,z5,z812]),(0,[z0,z2,z3,z96,z5,z423]),(0,[z0,z3,z4,z5,z6,z1000]),(0,[z0,z9,z1001,z4,z5,z6])],[(0,[z0,z9,z464,z4,z5,z6]),(0,[z291,z9,z955,z4,z5,z6]),(0,[z291,z130,z19,z4,z5,z6]),(0,[z9,z19,z4,z338,z5,z6]),(0,[z0,z1002,z3,z4,z5,z6])],[(0,[z0,z966,z3,z4,z5,z6]),(0,[z0,z63,z240,z3,z4,z47])],[(0,[z9,z19,z4,z5,z349,z6]),(0,[z0,z112,z60,z9,z4,z6]),(0,[z0,z29,z9,z192,z3,z5]),(0,[z0,z9,z3,z4,z5,z1003]),(0,[z0,z9,z3,z4,z5,z1004])],[(0,[z0,z9,z19,z4,z5,z6]),(0,[z488,z9,z19,z4,z5,z6]),(0,[z0,z1005,z9,z3,z4,z6]),(0,[z0,z1006,z9,z3,z4,z5]),(0,[z36,z9,z525,z3,z4,z6]),(0,[z0,z44,z3,z4,z5,z6])],[(0,[z10,z0,z25,z4,z5,z6]),(0,[z0,z58,z3,z4,z5,z611]),(0,[z0,z9,z1007,z4,z5,z6]),(1,[z0,z9,z714,z5,z6]),(0,[z0,z3,z4,z1008,z5,z6]),(0,[z0,z63,z9,z4,z511,z47])]],
   [[(0,[z0,z9,z1009,z4,z5,z6]),(0,[z386,z9,z19,z4,z5,z6]),(0,[z0,z9,z891,z104,z4,z5]),(0,[z0,z58,z3,z4,z5,z432]),(0,[z0,z1010,z3,z4,z5,z6])],[(0,[z0,z383,z3,z4,z5,z6]),(0,[z10,z0,z164,z3,z4,z5]),(0,[z0,z135,z19,z4,z5,z6]),(0,[z0,z3,z4,z5,z1011,z6]),(0,[z0,z1012,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1013]),(0,[z0,z436,z9,z4,z5,z73])],[(0,[z0,z9,z3,z4,z5,z1014])],[(0,[z0,z112,z9,z35,z4,z6]),(0,[z0,z9,z1015,z4,z5,z6])],[(0,[z586,z100,z3,z4,z5,z6]),(0,[z0,z9,z147,z4,z5,z6]),(0,[z0,z9,z1016,z4,z5,z6]),(0,[z0,z9,z19,z4,z6,z794]),(0,[z0,z9,z1017,z4,z5,z6]),(0,[z0,z122,z32,z85,z5,z6]),(0,[z0,z8,z9,z4,z86,z6]),(0,[z0,z9,z1018,z4,z5,z6])],[(0,[z10,z27,z398,z4,z5,z6]),(0,[z0,z70,z9,z19,z5,z6]),(0,[z0,z112,z9,z4,z370,z6]),(0,[z0,z9,z19,z4,z1019,z6]),(0,[z0,z9,z19,z4,z59,z46]),(0,[z410,z9,z19,z4,z5,z6]),(0,[z0,z1020,z3,z4,z5,z6]),(0,[z65,z9,z289,z3,z5,z6]),(0,[z0,z76,z3,z4,z5,z543]),(0,[z0,z9,z32,z85,z123,z6]),(0,[z0,z9,z1021,z4,z5,z6])],[(0,[z0,z3,z4,z5,z151,z625]),(0,[z291,z112,z9,z19,z4,z6]),(0,[z0,z9,z49,z4,z5,z370]),(0,[z0,z9,z1022,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1023])],[(0,[z0,z9,z19,z4,z5,z153]),(0,[z0,z9,z31,z4,z5,z194]),(0,[z0,z1024,z9,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1025]),(0,[z0,z9,z4,z714,z5,z6]),(0,[z0,z1026,z3,z4,z5,z6]),(0,[z0,z313,z3,z4,z5,z194]),(0,[z0,z1027,z3,z4,z5,z6])]],
   [[(1,[z0,z70,z29,z9,z5]),(0,[z0,z9,z31,z4,z5,z1028]),(0,[z0,z741,z137,z4,z5,z6]),(0,[z0,z9,z1029,z4,z5,z6]),(0,[z0,z9,z3,z4,z1030,z6])],[(0,[z9,z955,z3,z4,z5,z6]),(0,[z0,z70,z9,z49,z3,z5]),(0,[z0,z79,z3,z4,z74,z6])],[(0,[z0,z3,z1031,z4,z5,z6]),(0,[z0,z9,z3,z1032,z5,z6]),(0,[z0,z70,z9,z192,z5,z6]),(0,[z0,z31,z4,z91,z5,z6]),(0,[z0,z9,z3,z4,z512,z469]),(0,[z0,z9,z1033,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z329]),(0,[z0,z9,z1034,z4,z5,z6]),(0,[z0,z9,z3,z17,z231,z6]),(0,[z0,z9,z1035,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z1036]),(0,[z0,z130,z49,z19,z4,z5]),(0,[z0,z29,z9,z13,z19,z4]),(0,[z0,z9,z332,z4,z5,z6]),(0,[z34,z9,z31,z4,z71,z6]),(0,[z30,z9,z3,z50,z512,z6]),(0,[z0,z9,z3,z4,z5,z423]),(0,[z9,z3,z4,z5,z6,z1037])],[(0,[z116,z3,z4,z5,z92,z6]),(0,[z0,z9,z31,z4,z1038,z6]),(0,[z0,z8,z9,z4,z123,z6]),(0,[z0,z9,z4,z5,z6,z511]),(0,[z0,z9,z3,z1039,z5,z6]),(0,[z0,z436,z9,z4,z5,z72])],[(0,[z10,z27,z3,z4,z5,z6]),(0,[z0,z9,z315,z4,z5,z6]),(0,[z686,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z1040,z6]),(0,[z0,z9,z1041,z4,z5,z6]),(0,[z0,z1042,z3,z4,z5,z6])],[(0,[z0,z112,z130,z4,z5,z6]),(0,[z0,z789,z9,z19,z4,z6]),(0,[z0,z19,z4,z5,z6,z773]),(0,[z0,z1043,z9,z4,z5,z6]),(0,[z146,z9,z3,z4,z5,z106]),(0,[z1044,z9,z3,z4,z5,z6]),(0,[z0,z1045,z3,z4,z5,z6]),(0,[z0,z489,z9,z3,z5,z73])],[(0,[z291,z9,z19,z4,z5,z6]),(0,[z0,z19,z4,z5,z195,z6]),(0,[z0,z19,z4,z5,z6,z778]),(0,[z614,z9,z19,z4,z5,z6]),(1,[z9,z3,z1046,z5,z6]),(0,[z65,z9,z104,z66,z5,z6]),(0,[z0,z3,z4,z774,z5,z6]),(0,[z0,z3,z4,z129,z802,z6])]],
   [[(0,[z0,z9,z1047,z4,z5,z6]),(0,[z0,z9,z1048,z4,z5,z6]),(0,[z0,z44,z3,z4,z5,z73])],[(0,[z660,z9,z19,z4,z5,z6]),(0,[z0,z70,z9,z236,z5,z6]),(0,[z0,z3,z4,z1049,z5,z6]),(0,[z0,z1050,z3,z4,z5,z6])],[(0,[z0,z42,z232,z4,z5,z6]),(0,[z291,z135,z19,z4,z5,z6]),(0,[z275,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z5,z234,z156])],[(0,[z0,z9,z3,z4,z5,z1051]),(0,[z0,z9,z3,z4,z862,z6]),(0,[z0,z306,z3,z4,z5,z194]),(0,[z0,z9,z4,z1052,z5,z6])],[(0,[z0,z9,z3,z5,z1053,z6]),(0,[z0,z9,z13,z267,z4,z6]),(0,[z0,z9,z332,z4,z5,z153]),(0,[z0,z3,z4,z5,z763,z6]),(1,[z0,z9,z4,z771,z6])],[(0,[z0,z19,z93,z4,z5,z6]),(0,[z0,z811,z9,z19,z5,z6]),(0,[z0,z9,z31,z404,z5,z6]),(0,[z0,z9,z4,z5,z75,z307])],[(0,[z291,z70,z9,z19,z5,z6]),(0,[z0,z9,z315,z4,z5,z153])],[(0,[z0,z70,z29,z9,z5,z6]),(0,[z30,z9,z3,z1046,z5,z6]),(1,[z0,z741,z4,z5,z6]),(0,[z0,z9,z1054,z4,z5,z6])]],
   [[(0,[z0,z9,z13,z19,z4,z6]),(0,[z0,z112,z9,z264,z4,z6]),(0,[z0,z3,z824,z4,z5,z6]),(0,[z0,z1055,z9,z3,z4,z5])],[(0,[z0,z9,z3,z4,z5,z1056]),(0,[z0,z1057,z3,z4,z5,z6]),(0,[z0,z4,z5,z1058,z195,z6]),(0,[z0,z122,z3,z4,z5,z165])],[(0,[z0,z9,z19,z17,z18,z6]),(0,[z0,z9,z15,z4,z5,z483])],[(0,[z0,z135,z13,z19,z4,z6]),(0,[z0,z9,z3,z4,z5,z194]),(0,[z0,z44,z3,z4,z5,z72])],[(0,[z0,z1059,z9,z3,z4,z5]),(0,[z0,z70,z135,z3,z5,z6]),(0,[z9,z289,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1028]),(0,[z65,z9,z3,z66,z5,z6]),(0,[z0,z1060,z9,z4,z5,z6]),(0,[z466,z9,z3,z4,z5,z106]),(0,[z0,z9,z4,z5,z1061,z6]),(0,[z0,z25,z9,z4,z5,z329])],[(0,[z0,z1,z3,z774,z5,z6]),(0,[z0,z9,z1062,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1063,z6]),(0,[z0,z42,z54,z4,z5,z6]),(0,[z291,z9,z192,z19,z5,z6]),(0,[z0,z29,z9,z15,z4,z5]),(0,[z0,z29,z9,z13,z3,z4]),(0,[z0,z31,z4,z5,z6,z166]),(0,[z0,z383,z3,z4,z5,z72]),(0,[z0,z206,z21,z4,z5,z6]),(0,[z0,z1064,z9,z3,z4,z5]),(0,[z0,z9,z1065,z4,z5,z6]),(0,[z0,z3,z4,z1066,z5,z6]),(0,[z0,z9,z1067,z4,z5,z6])],[(0,[z0,z9,z49,z19,z4,z5]),(0,[z9,z19,z4,z5,z6,z615]),(0,[z0,z748,z9,z3,z5,z6]),(0,[z34,z9,z3,z4,z71,z6]),(0,[z0,z1068,z3,z4,z5,z6]),(0,[z0,z9,z1069,z4,z5,z6])]],
   [[(0,[z0,z755,z9,z3,z4,z6]),(0,[z0,z1070,z19,z4,z5,z6]),(0,[z0,z890,z3,z4,z5,z6]),(0,[z48,z9,z955,z4,z5,z6]),(0,[z0,z9,z3,z4,z1038,z6]),(0,[z0,z1071,z3,z4,z5,z6]),(0,[z0,z3,z4,z28,z5,z268])],[(0,[z0,z9,z3,z4,z1040,z6]),(1,[z9,z3,z4,z749,z6]),(0,[z0,z42,z110,z4,z5,z6])],[(0,[z0,z135,z49,z19,z4,z5])],[(0,[z0,z9,z3,z5,z898,z6]),(0,[z0,z9,z49,z283,z4,z5]),(0,[z34,z9,z215,z4,z71,z6]),(0,[z36,z9,z3,z4,z749,z6]),(0,[z0,z9,z4,z5,z403,z6]),(0,[z1072,z9,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z1073,z6])],[(0,[z0,z115,z19,z4,z5,z6]),(0,[z0,z8,z9,z4,z376,z6]),(0,[z0,z9,z1074,z4,z5,z6]),(0,[z0,z1075,z9,z3,z4,z5]),(0,[z0,z9,z3,z4,z59,z51]),(0,[z0,z63,z9,z3,z4,z47])],[(0,[z0,z9,z1076,z4,z5,z6]),(0,[z0,z29,z9,z4,z5,z16]),(0,[z0,z381,z407,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1077])],[(0,[z9,z318,z31,z4,z5,z6]),(0,[z0,z164,z3,z4,z129,z5]),(1,[z0,z3,z4,z5,z763])],[(0,[z0,z9,z19,z4,z878,z6]),(0,[z0,z1078,z9,z4,z5,z6]),(0,[z0,z2,z3,z357,z5,z6]),(0,[z0,z99,z9,z5,z483,z73])]],
   [[(0,[z0,z1079,z9,z4,z5,z6]),(0,[z34,z9,z35,z4,z71,z6]),(0,[z0,z8,z9,z4,z90,z6]),(0,[z0,z60,z9,z4,z5,z491]),(0,[z0,z3,z4,z1080,z5,z6]),(0,[z0,z1081,z3,z4,z5,z6])],[(0,[z10,z727,z3,z4,z5,z6]),(0,[z291,z9,z13,z19,z4,z6]),(0,[z9,z19,z457,z4,z5,z6]),(0,[z0,z164,z9,z4,z5,z185]),(0,[z0,z9,z3,z404,z5,z6]),(0,[z0,z1082,z9,z4,z5,z6])],[(0,[z0,z112,z9,z49,z19,z4]),(0,[z0,z9,z19,z5,z6,z716]),(0,[z0,z3,z4,z5,z799,z6]),(0,[z65,z9,z3,z1046,z5,z6]),(0,[z0,z9,z3,z4,z1083,z6])],[(0,[z0,z58,z31,z4,z5,z62]),(0,[z95,z383,z3,z4,z5,z155]),(0,[z0,z9,z3,z4,z5,z1084]),(0,[z0,z9,z15,z4,z5,z747])],[(0,[z9,z19,z4,z5,z465,z6]),(0,[z0,z9,z31,z4,z5,z469]),(0,[z0,z31,z4,z5,z195,z6]),(0,[z0,z9,z4,z5,z1085,z6])],[(0,[z0,z76,z19,z4,z5,z151]),(0,[z30,z9,z31,z50,z5,z6]),(0,[z0,z3,z4,z5,z6,z1086])],[(0,[z291,z29,z9,z19,z4,z5]),(0,[z0,z130,z31,z4,z5,z6]),(0,[z0,z313,z31,z4,z5,z6]),(0,[z0,z169,z3,z4,z177,z6]),(0,[z1087,z9,z3,z4,z5,z6])],[(0,[z0,z9,z49,z192,z19,z5]),(0,[z0,z9,z1088,z4,z5,z6]),(0,[z0,z122,z3,z4,z5,z307]),(0,[z0,z239,z9,z3,z5,z73])]],
   [[(0,[z116,z100,z31,z4,z5,z6]),(0,[z0,z1089,z3,z4,z5,z6]),(0,[z291,z9,z49,z19,z4,z5]),(0,[z0,z9,z192,z264,z5,z6]),(0,[z0,z9,z19,z4,z5,z156]),(0,[z0,z19,z4,z91,z5,z6]),(0,[z0,z3,z881,z4,z5,z6]),(0,[z0,z9,z1090,z4,z5,z6]),(0,[z0,z9,z3,z4,z123,z307]),(0,[z0,z9,z1091,z4,z5,z6])],[(0,[z0,z2,z31,z96,z5,z6]),(0,[z0,z9,z4,z5,z6,z483]),(0,[z0,z9,z98,z4,z89,z6]),(0,[z0,z9,z3,z5,z6,z725])],[(0,[z0,z801,z9,z3,z4,z5]),(0,[z0,z9,z19,z4,z5,z165]),(0,[z0,z9,z3,z4,z5,z935]),(0,[z0,z9,z3,z4,z1092,z6]),(0,[z0,z436,z175,z4,z5,z6])],[(0,[z288,z9,z19,z4,z5,z6]),(0,[z146,z9,z318,z3,z4,z5]),(0,[z0,z9,z3,z111,z234,z6]),(0,[z0,z9,z4,z5,z75,z210]),(0,[z0,z1093,z3,z4,z5,z6])],[(0,[z0,z169,z19,z4,z5,z6]),(0,[z0,z29,z135,z3,z4,z5]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1095]),(0,[z0,z206,z741,z4,z5,z6]),(0,[z0,z9,z3,z4,z1096,z6])],[(0,[z0,z206,z135,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1097]),(0,[z0,z1098,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1099]),(0,[z0,z9,z85,z5,z6,z149]),(0,[z0,z9,z3,z4,z5,z1100])],[(0,[z10,z0,z3,z4,z5,z268]),(0,[z0,z908,z19,z4,z5,z6]),(0,[z0,z112,z80,z9,z4,z6]),(0,[z0,z1101,z3,z4,z5,z6]),(0,[z0,z504,z9,z408,z5,z6]),(0,[z0,z1102,z3,z4,z5,z6]),(0,[z0,z1006,z9,z104,z4,z5]),(0,[z0,z3,z96,z774,z5,z6]),(0,[z0,z9,z1103,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1104])],[(0,[z0,z9,z19,z4,z911,z6]),(0,[z0,z9,z283,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1105]),(0,[z0,z58,z3,z4,z5,z582])]],
   [[(0,[z116,z100,z132,z4,z5,z6]),(0,[z0,z31,z4,z808,z5,z6]),(0,[z0,z9,z3,z4,z696,z46]),(0,[z0,z4,z5,z6,z166,z511])],[(0,[z0,z183,z19,z4,z5,z6]),(0,[z0,z3,z4,z840,z5,z6]),(0,[z170,z9,z31,z4,z5,z6]),(0,[z0,z9,z3,z1106,z5,z6]),(0,[z0,z9,z4,z387,z75,z6])],[(0,[z554,z9,z19,z4,z5,z6]),(0,[z0,z175,z19,z4,z5,z6]),(0,[z0,z76,z3,z4,z5,z323])],[(0,[z0,z3,z4,z251,z74,z6]),(0,[z379,z9,z31,z4,z5,z6]),(0,[z0,z3,z4,z5,z151,z61]),(0,[z0,z1107,z3,z4,z5,z6]),(0,[z0,z9,z1108,z4,z5,z6]),(0,[z0,z468,z9,z3,z5,z73])],[(0,[z0,z9,z1109,z4,z5,z6]),(0,[z130,z31,z19,z4,z5,z6]),(0,[z0,z9,z1110,z4,z5,z6]),(0,[z0,z9,z1111,z4,z5,z6])],[(0,[z0,z70,z130,z19,z5,z6]),(0,[z0,z9,z3,z4,z959,z6]),(0,[z0,z112,z9,z49,z3,z4]),(0,[z449,z9,z31,z4,z5,z6]),(0,[z0,z9,z1112,z4,z5,z6]),(0,[z501,z9,z3,z4,z37,z6]),(0,[z0,z32,z85,z7,z5,z6]),(0,[z0,z60,z9,z4,z5,z693])],[(0,[z0,z2,z3,z510,z5,z6]),(0,[z0,z1113,z3,z4,z5,z6])],[(0,[z0,z9,z3,z1114,z5,z6]),(0,[z0,z1115,z9,z4,z5,z6]),(0,[z1116,z9,z3,z4,z5,z6]),(0,[z0,z58,z3,z4,z5,z62]),(0,[z0,z9,z4,z5,z771,z6]),(0,[z0,z115,z3,z372,z5,z6])]],
   [[(0,[z0,z9,z1117,z4,z5,z6]),(0,[z0,z29,z9,z264,z4,z5]),(0,[z0,z8,z9,z13,z4,z6]),(0,[z0,z9,z3,z4,z5,z469]),(1,[z9,z3,z4,z5,z812]),(0,[z0,z3,z4,z5,z1118,z6]),(0,[z0,z76,z9,z3,z404,z5]),(0,[z0,z1119,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z6,z838])],[(0,[z30,z9,z3,z50,z5,z6]),(0,[z0,z169,z332,z4,z5,z6]),(0,[z0,z9,z3,z4,z1120,z6]),(0,[z9,z3,z4,z37,z749,z6]),(0,[z0,z9,z4,z5,z1058,z6])],[(0,[z0,z9,z31,z4,z5,z6]),(0,[z0,z130,z3,z4,z5,z6]),(0,[z0,z9,z19,z781,z5,z6]),(0,[z0,z112,z9,z3,z4,z6]),(0,[z0,z9,z49,z192,z3,z5]),(0,[z0,z9,z3,z1121,z5,z6]),(0,[z34,z9,z3,z4,z749,z6]),(0,[z526,z9,z3,z4,z71,z6]),(0,[z0,z313,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z747]),(0,[z0,z60,z9,z4,z5,z483])],[(0,[z0,z9,z3,z4,z5,z1122]),(0,[z0,z169,z315,z4,z5,z6]),(0,[z0,z1123,z3,z4,z5,z6]),(0,[z0,z58,z115,z3,z4,z5]),(0,[z0,z9,z1124,z4,z5,z6])],[(0,[z116,z100,z3,z4,z5,z6]),(0,[z0,z19,z4,z5,z6,z166]),(0,[z0,z9,z4,z5,z6,z1125]),(0,[z0,z3,z1126,z4,z5,z6])],[(0,[z0,z9,z3,z976,z4,z6]),(0,[z0,z135,z31,z4,z5,z6]),(0,[z0,z19,z4,z904,z5,z6]),(0,[z0,z1127,z9,z4,z5,z6]),(0,[z9,z3,z4,z5,z6,z812]),(0,[z0,z1128,z9,z3,z4,z5]),(0,[z0,z9,z1129,z4,z5,z6]),(0,[z0,z2,z3,z96,z5,z6]),(0,[z0,z9,z1130,z4,z5,z6]),(0,[z0,z9,z1131,z4,z5,z6])],[(1,[z727,z3,z4,z5,z6]),(0,[z0,z130,z192,z3,z5,z6]),(0,[z0,z979,z3,z4,z5,z6]),(0,[z0,z183,z332,z4,z5,z6]),(0,[z0,z9,z3,z1132,z5,z6]),(0,[z0,z1133,z9,z4,z5,z6]),(0,[z0,z1134,z3,z4,z5,z6]),(0,[z0,z1135,z9,z4,z5,z6])],[(0,[z0,z9,z19,z953,z4,z5]),(0,[z0,z80,z29,z9,z4,z5]),(0,[z95,z9,z328,z4,z5,z155]),(0,[z0,z25,z4,z28,z5,z6]),(0,[z0,z9,z1136,z4,z5,z6]),(0,[z0,z9,z3,z633,z18,z6]),(0,[z0,z1137,z3,z4,z5,z6]),(0,[z0,z1138,z3,z4,z5,z6])]],
   [[(0,[z0,z9,z19,z4,z5,z797]),(0,[z0,z141,z19,z4,z74,z6]),(0,[z0,z103,z19,z4,z129,z6]),(0,[z0,z9,z19,z4,z5,z307]),(0,[z0,z183,z315,z4,z5,z6])],[(0,[z621,z9,z19,z4,z5,z6]),(0,[z0,z70,z9,z20,z5,z6]),(0,[z0,z9,z104,z4,z5,z6]),(0,[z0,z9,z31,z4,z59,z46]),(0,[z0,z9,z3,z4,z5,z1139]),(0,[z0,z42,z741,z4,z5,z6]),(0,[z0,z9,z1140,z4,z5,z6])],[(0,[z0,z9,z132,z4,z5,z6]),(0,[z0,z9,z1141,z4,z5,z6]),(0,[z0,z9,z3,z1142,z5,z6]),(0,[z0,z122,z19,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z833]),(0,[z30,z9,z3,z50,z5,z153])],[(0,[z670,z9,z19,z4,z5,z6]),(0,[z0,z9,z31,z4,z5,z153]),(0,[z0,z103,z3,z4,z277,z6])],[],[(0,[z0,z164,z9,z3,z4,z5])],[(0,[z0,z9,z398,z4,z5,z6]),(0,[z114,z9,z19,z4,z5,z6]),(0,[z34,z247,z9,z3,z4,z6]),(0,[z0,z9,z4,z5,z1143,z6])],[(0,[z0,z9,z31,z4,z512,z6]),(0,[z0,z9,z1144,z4,z5,z6])]],
   [[(0,[z0,z70,z29,z9,z19,z5]),(0,[z0,z787,z9,z19,z4,z5]),(0,[z0,z9,z49,z13,z19,z4]),(0,[z0,z112,z9,z85,z4,z6]),(0,[z0,z70,z60,z9,z5,z6]),(0,[z247,z9,z31,z4,z5,z6]),(0,[z0,z9,z1145,z4,z5,z6]),(0,[z36,z9,z3,z4,z37,z6]),(0,[z0,z80,z9,z714,z5,z6])],[(0,[z0,z112,z9,z4,z248,z6]),(0,[z0,z240,z19,z4,z5,z6]),(0,[z0,z130,z4,z89,z5,z6]),(0,[z0,z130,z13,z3,z4,z6]),(0,[z65,z9,z168,z66,z5,z6]),(1,[z0,z9,z3,z744,z6])],[(0,[z116,z296,z3,z4,z5,z6]),(0,[z0,z999,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1146]),(0,[z9,z3,z1046,z50,z5,z6]),(0,[z0,z9,z3,z4,z6,z1147]),(0,[z0,z9,z1148,z104,z4,z6]),(0,[z0,z9,z3,z221,z18,z6])],[(0,[z0,z9,z1149,z4,z5,z6]),(0,[z0,z9,z1150,z4,z5,z6]),(0,[z0,z8,z9,z4,z320,z6]),(0,[z0,z60,z9,z4,z5,z747]),(0,[z0,z9,z3,z4,z5,z747])],[(0,[z0,z9,z3,z4,z5,z1151]),(0,[z0,z8,z70,z9,z5,z6])],[(0,[z0,z9,z1152,z4,z5,z6]),(0,[z0,z29,z130,z19,z4,z5]),(0,[z0,z70,z9,z5,z75,z6]),(0,[z0,z9,z1153,z4,z5,z6]),(0,[z0,z163,z313,z3,z234,z6])],[(0,[z0,z9,z3,z4,z5,z6]),(0,[z0,z9,z19,z829,z5,z6]),(0,[z0,z9,z19,z4,z5,z832]),(0,[z0,z383,z3,z4,z5,z73]),(0,[z0,z9,z3,z4,z5,z1154]),(0,[z0,z2,z3,z4,z5,z268]),(0,[z0,z8,z9,z4,z330,z6]),(0,[z0,z9,z4,z89,z6,z401])],[(0,[z0,z112,z9,z13,z4,z6]),(0,[z0,z1155,z3,z4,z5,z6]),(1,[z0,z3,z774,z5,z6]),(0,[z0,z58,z3,z4,z5,z649])]],
   [[(0,[z0,z1,z19,z28,z5,z6]),(0,[z0,z130,z137,z4,z5,z6]),(0,[z0,z1156,z3,z4,z5,z6])],[(0,[z0,z135,z3,z4,z5,z6]),(0,[z0,z9,z158,z4,z5,z204])],[(0,[z0,z9,z3,z1157,z5,z6]),(0,[z0,z9,z192,z3,z5,z6]),(0,[z9,z3,z4,z5,z106,z812]),(0,[z0,z2,z3,z774,z5,z6])],[(0,[z10,z27,z232,z4,z5,z6]),(0,[z0,z9,z1158,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1159]),(0,[z0,z1160,z3,z4,z5,z6]),(0,[z0,z9,z1161,z4,z5,z6])],[(0,[z116,z0,z25,z4,z5,z6]),(0,[z0,z9,z19,z4,z850,z6]),(0,[z0,z1162,z3,z4,z5,z6]),(0,[z0,z1163,z3,z4,z5,z6]),(0,[z0,z9,z4,z1164,z5,z6]),(0,[z0,z9,z1165,z4,z5,z6])],[(0,[z0,z9,z19,z4,z177,z6]),(0,[z0,z190,z19,z4,z5,z6]),(0,[z0,z135,z192,z3,z5,z6]),(0,[z0,z9,z3,z4,z1019,z6]),(0,[z0,z9,z1166,z4,z5,z6]),(0,[z0,z9,z1148,z3,z4,z6]),(0,[z0,z9,z3,z4,z123,z165]),(0,[z0,z9,z3,z4,z59,z46])],[(0,[z0,z58,z3,z4,z5,z176]),(0,[z0,z9,z31,z17,z18,z6]),(0,[z0,z982,z9,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1167]),(1,[z0,z9,z3,z4,z838])],[(0,[z0,z9,z35,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z153]),(0,[z0,z1168,z9,z3,z4,z6]),(0,[z0,z9,z1169,z4,z5,z6])]],
   [[(0,[z0,z9,z328,z4,z5,z6]),(0,[z0,z141,z164,z3,z4,z5])],[(0,[z0,z9,z1170,z4,z5,z6]),(0,[z0,z831,z9,z19,z5,z6]),(0,[z0,z60,z9,z49,z4,z5]),(0,[z0,z9,z4,z5,z185,z6]),(0,[z0,z60,z9,z4,z5,z138])],[],[(0,[z0,z44,z19,z4,z5,z6]),(0,[z0,z70,z29,z9,z3,z5]),(0,[z0,z9,z49,z13,z3,z4]),(0,[z9,z296,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z512,z6]),(0,[z0,z9,z32,z714,z5,z6]),(0,[z0,z9,z3,z1171,z5,z6]),(0,[z0,z163,z9,z3,z234,z6]),(0,[z0,z99,z9,z3,z5,z725])],[(0,[z0,z1172,z9,z4,z5,z6]),(0,[z9,z19,z4,z617,z5,z6]),(0,[z0,z3,z4,z7,z5,z6]),(0,[z0,z141,z3,z4,z120,z6]),(0,[z0,z163,z9,z403,z234,z6])],[(0,[z0,z9,z13,z3,z4,z6]),(0,[z0,z1173,z3,z4,z5,z6]),(0,[z95,z3,z4,z5,z293,z155])],[(0,[z0,z29,z9,z328,z4,z5]),(0,[z0,z1174,z3,z4,z5,z6]),(0,[z0,z9,z3,z4,z802,z6])],[(0,[z0,z9,z19,z870,z5,z6]),(0,[z0,z9,z32,z157,z5,z6]),(0,[z0,z1175,z3,z4,z5,z6]),(0,[z0,z63,z175,z3,z4,z47])]],
   [[(0,[z0,z9,z1176,z4,z5,z6]),(0,[z0,z135,z13,z3,z4,z6]),(0,[z9,z3,z4,z1046,z5,z6]),(0,[z0,z9,z3,z1177,z5,z6])],[(0,[z95,z193,z9,z3,z4,z5]),(0,[z0,z9,z3,z4,z59,z838])],[(0,[z0,z29,z9,z3,z4,z5]),(0,[z0,z9,z332,z4,z177,z6]),(0,[z9,z3,z66,z1046,z5,z6]),(0,[z0,z9,z3,z4,z5,z1178]),(0,[z0,z79,z58,z3,z4,z5])],[(0,[z0,z9,z1179,z4,z5,z6]),(0,[z0,z112,z70,z9,z5,z6]),(0,[z0,z9,z3,z4,z5,z812])],[(0,[z95,z9,z31,z4,z5,z155]),(0,[z0,z9,z315,z4,z177,z6]),(0,[z0,z9,z3,z4,z512,z153]),(0,[z0,z103,z3,z4,z802,z6]),(0,[z0,z9,z4,z5,z994,z156]),(0,[z0,z9,z1180,z4,z5,z6]),(0,[z0,z240,z3,z372,z5,z6])],[(0,[z0,z1181,z9,z3,z5,z6])],[(0,[z9,z955,z19,z4,z5,z6]),(0,[z0,z3,z4,z5,z1182,z6]),(0,[z0,z9,z3,z4,z1183,z6]),(0,[z0,z9,z3,z4,z1184,z6]),(0,[z0,z1185,z9,z4,z5,z6])],[(0,[z0,z130,z273,z4,z5,z6]),(0,[z0,z9,z19,z1032,z5,z6]),(0,[z0,z9,z19,z4,z5,z329]),(0,[z0,z887,z19,z4,z5,z6]),(0,[z0,z1186,z3,z4,z5,z6]),(0,[z0,z3,z4,z674,z5,z151])]],
   [[(0,[z0,z9,z31,z4,z387,z6]),(0,[z0,z9,z3,z4,z5,z1187])],[(0,[z0,z727,z3,z4,z5,z6]),(0,[z0,z76,z31,z4,z5,z151]),(0,[z0,z9,z4,z5,z1188,z6])],[(0,[z0,z25,z164,z9,z4,z5]),(0,[z1189,z9,z3,z4,z5,z6]),(0,[z0,z9,z3,z17,z18,z6])],[(0,[z146,z9,z19,z4,z5,z106]),(0,[z0,z9,z4,z5,z1190,z6]),(0,[z0,z1191,z3,z4,z5,z6])],[(0,[z0,z29,z9,z4,z368,z5]),(0,[z9,z525,z31,z4,z5,z6]),(0,[z0,z9,z3,z4,z5,z1192]),(0,[z0,z164,z2,z3,z4,z5])],[(0,[z0,z9,z1193,z4,z5,z6]),(0,[z0,z70,z9,z5,z370,z6]),(0,[z0,z960,z9,z3,z4,z6]),(0,[z0,z9,z98,z267,z4,z6]),(0,[z0,z9,z32,z85,z5,z6]),(0,[z0,z122,z3,z4,z123,z6]),(0,[z0,z815,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z5,z1194]),(0,[z0,z169,z3,z4,z5,z469]),(0,[z0,z9,z4,z89,z474,z6]),(0,[z0,z9,z3,z4,z5,z1195])],[(0,[z0,z76,z164,z3,z4,z5]),(0,[z0,z9,z4,z5,z6,z1196])]],
   [[(0,[z0,z19,z4,z5,z1011,z6]),(0,[z0,z1070,z3,z4,z5,z6]),(0,[z0,z631,z324,z4,z5,z6]),(0,[z0,z9,z1197,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1198]),(0,[z0,z175,z3,z4,z59,z5])],[(0,[z146,z9,z147,z4,z5,z106]),(0,[z0,z9,z1199,z4,z5,z6])],[(0,[z0,z9,z1200,z4,z5,z6]),(0,[z0,z112,z9,z31,z4,z6]),(0,[z0,z112,z130,z3,z4,z6]),(0,[z0,z1201,z9,z4,z5,z6]),(0,[z0,z1202,z3,z4,z5,z6]),(0,[z0,z8,z9,z4,z426,z6]),(0,[z0,z350,z163,z9,z234,z6])],[(0,[z0,z9,z3,z4,z1203,z6]),(0,[z0,z183,z3,z4,z5,z469]),(0,[z0,z3,z419,z28,z5,z6])],[(0,[z0,z9,z3,z4,z5,z949]),(1,[z9,z955,z4,z5,z6]),(0,[z0,z112,z135,z19,z4,z6]),(0,[z0,z9,z19,z4,z5,z268]),(0,[z0,z756,z31,z4,z5,z6]),(0,[z30,z183,z3,z50,z5,z6]),(0,[z0,z1204,z3,z4,z5,z6]),(0,[z0,z9,z4,z5,z6,z1205])],[(0,[z100,z727,z3,z4,z5,z6]),(0,[z0,z183,z31,z4,z5,z6]),(0,[z0,z306,z31,z4,z5,z6]),(0,[z0,z9,z3,z1046,z5,z6]),(0,[z0,z9,z3,z4,z5,z1206]),(0,[z0,z9,z1207,z4,z5,z6]),(0,[z0,z3,z4,z5,z802,z6])],[(0,[z0,z3,z4,z5,z293,z6]),(0,[z0,z9,z19,z372,z5,z6]),(0,[z0,z9,z98,z4,z403,z6]),(0,[z0,z1208,z9,z4,z5,z6])],[(0,[z0,z9,z3,z4,z1209,z6]),(0,[z0,z9,z1210,z4,z5,z6]),(0,[z0,z76,z3,z4,z5,z763]),(0,[z0,z9,z3,z4,z5,z1211])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1044).take 207) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1251)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 521, 207] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 97).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 196).take 60).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [97, 99, 60] = true :=
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

end PEqualNP.Outside.L_meta_38383

theorem PEqualNP.Outside.L_meta_38383 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38383.solve