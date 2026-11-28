import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_46066

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
  Nat.testBit (4277074602 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0021011443842d68#64 ++ 0x40008404510e10b5#64 ++ 0x026307fc478c7fef#64 ++ 0xbc098c1ff11e31ff#64 : BitVec 256),
   (0x84acc4b058b19730#64 ++ 0x8212b312c162c65c#64 ++ 0x8dbcc4b078f39f1f#64 ++ 0x7636f312c1e3ce7c#64 : BitVec 256),
   (0x11c058c1805ac285#64 ++ 0x0047016306016b0a#64 ++ 0x71c0f8c380ffe3fe#64 ++ 0xf9c703e30e03ff8f#64 : BitVec 256),
   (0x6e00af02ad037806#64 ++ 0x01b802bc0ab40de0#64 ++ 0x7e00ff03ff03fc3d#64 ++ 0xfdf803fc0ffc0ff0#64 : BitVec 256),
   (0x3b77000376ec0038#64 ++ 0x04eddc000ddbb000#64 ++ 0xbfff0003fffc003b#64 ++ 0xe6fffc000ffff000#64 : BitVec 256),
   (0x3fdaf6e800000000#64 ++ 0x08ff6bdba0000000#64 ++ 0xfffffffc00000007#64 ++ 0xebfffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc478c7fef 0xbc098c1ff11e31ff

def z1 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ffe3fe 0xf9c703e30e03ff8f

def z2 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003fffc003b 0xe6fffc000ffff000

def z3 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc00000007 0xebfffffff0000000

def z4 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff03fc3d 0xfdf803fc0ffc0ff0

def z5 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078f39f1f 0x7636f312c1e3ce7c

def z6 : W := mkw 0x95edddf5dbfffffd 0xc257b777d76fffff 0xffffffffffffffff 0xffffffffffffffff

def z7 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00fb03bf03e030 0xc9f803ec0efc0f80

def z8 : W := mkw 0x842d85345ba53d78 0xc210b614d16e94f5 0x8e3f073c7f001c01 0x0638fc1cf1fc0070

def z9 : W := mkw 0x8024001058b19730 0x820090004162c65c 0x0000000078f39f18 0x1400000001e3ce7c

def z10 : W := mkw 0x84adc5b45bb5bf78 0xc212b716d16ed6fd 0x8fffc7fc7fffffff 0xfe3fff1ff1ffffff

def z11 : W := mkw 0x84acdcf0d8b3d7b5 0x8212b373c362cf5e 0xcdbcfcf078f3ffdf 0x7f36f3f3c1e3cfff

def z12 : W := mkw 0x6e21a7166f853d6a 0x41b8869c59be14f5 0x0e6307fc7f8c7fef 0xbc398c1ff1fe31ff

def z13 : W := mkw 0x00250803f6fec2bd 0x040094200fdbfb0a 0x00000003ffffe3f8 0x140000000fffff8f

def z14 : W := mkw 0x000008008012c285 0x0000002002004b0a 0x000000000003e3c0 0x1000000000000f8f

def z15 : W := mkw 0x0024000050a00030 0x0000900001428000 0x0000000078f00018 0x0400000001e3c000

def z16 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x0000000380ffe3f8 0x100000000e03ff8f

def z17 : W := mkw 0x6e00a7022d013802 0x01b8029c08b404e0 0x0e0007007f001c01 0x0438001c01fc0070

def z18 : W := mkw 0x3b52324800000000 0x08ed48c920000000 0xffff3b4c00000003 0xebfffced30000000

def z19 : W := mkw 0x3fdaf6e808011000 0x08ff6bdba0200440 0xfffffffc78039c1f 0xfffffffff1e00e70

def z20 : W := mkw 0x0000010401002840 0x40000004100400a1 0x0000034c000060c0 0x0800000d30000183

def z21 : W := mkw 0xbb7700137efd9738 0x86eddc004dfbf65c 0xbfff0003ffff9f3b 0xf6fffc000ffffe7c

def z22 : W := mkw 0x0021001442840568 0x40008400510a1015 0x0023003c00000000 0x00008c00f0000000

def z23 : W := mkw 0x0021001442840568 0x40008400510a1015 0x006300fc008c03c2 0x00018c03f002300f

def z24 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7c00f803b8038010 0x41f003e00ee00e00

def z25 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc00038738010 0x4236730000e1ce00

def z26 : W := mkw 0x1140000000000000 0x0045000000000000 0x31c0000000000002 0xe0c7000000000000

def z27 : W := mkw 0x0000080080024004 0x0000002002000900 0x7000f8038003e03c 0xf9c003e00e000f80

def z28 : W := mkw 0x95ccdce1987bd295 0x825733738661ef4a 0xfd9cf803b8738010 0x43f673e00ee1ce00

def z29 : W := mkw 0x0024000050a00030 0x0000900001428000 0x81bc000000f00002 0x0206f0000003c000

def z30 : W := mkw 0x3b530003264c0008 0x04ed4c000c993000 0x32430003870c0020 0x80c90c000e1c3000

def z31 : W := mkw 0x2a00220000000000 0x00a8008800000000 0x72003b0000000000 0x89c800ec00000000

def z32 : W := mkw 0x008059d48112efc5 0x4002016752044bbf 0x4000fffc0003ffc4 0x190003fff0000fff

def z33 : W := mkw 0x11fb50fc42840568 0x4847ed43f10a1015 0x81ff00fc008c03c2 0x0207fc03f002300f

def z34 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbfdf0003bf7c0030 0xc2ff7c000efdf000

def z35 : W := mkw 0x3bd250c000000000 0x00ef494300000000 0xfffff8c000000007 0xebffffe300000000

def z36 : W := mkw 0x0488c4a000108200 0x0012231280004208 0x8dbcc4b000f3831f 0x7236f312c003ce0c

def z37 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbc04b078f01f03 0x0636f012c1e3c07c

def z38 : W := mkw 0x11c058c08012c285 0x0047016302004b0a 0x71c0f8c00003e3c6 0xf9c703e300000f8f

def z39 : W := mkw 0x11da50e800000000 0x08476943a0000000 0x81ff00fc00000002 0x0207fc03f0000000

def z40 : W := mkw 0xbffef6f858b19730 0x8afffbdbe162c65c 0xfffffffc78f39f1f 0xfffffffff1e3ce7c

def z41 : W := mkw 0x0000000008011000 0x0000000000200440 0x0000000078039c18 0x1400000001e00e70

def z42 : W := mkw 0x6a002b02a5026806 0x01a800ac0a9409a0 0x72003b0387006020 0x89c800ec0e1c0180

def z43 : W := mkw 0x80ac40b050b08730 0x8202b102c142c21c 0x81bc00b000f00302 0x0206f002c003c00c

def z44 : W := mkw 0x3b77011777ec2d78 0x44eddc045ddfb0b5 0xbfff07fffffc7fff 0xfefffc1ffffff1ff

def z45 : W := mkw 0x4400af0089037806 0x011002bc02240de0 0x4000ff000003fc04 0x190003fc00000ff0

def z46 : W := mkw 0x0408842000000000 0x0010221080000000 0x8c3c043000000001 0x0230f010c0000000

def z47 : W := mkw 0x7fdaf7ea2d013802 0x09ff6bdfa8b404e0 0xfffffffc7f001c07 0xeffffffff1fc0070

def z48 : W := mkw 0x11c050c000108200 0x0047014300004208 0x71c0f8c000f3831e 0xf9c703e30003ce0c

def z49 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x002004b0478c7fef 0x34008012c11e31ff

def z50 : W := mkw 0x11c050c100588281 0x004701430401620a 0x01c0c0c000ff83de 0x700703030003fe0f

def z51 : W := mkw 0x1140104000000000 0x0045004100000000 0x7040384000000000 0x89c100e100000000

def z52 : W := mkw 0x0488f6e800000000 0x081223dba0000000 0x4000fffc00000004 0x090003fff0000000

def z53 : W := mkw 0x0024000050a00030 0x0000900001428000 0x8dbc000078f0001b 0x6636f00001e3c000

def z54 : W := mkw 0xbfffc4b37efd9738 0x86ffff12cdfbf65c 0xbfffc4b3ffff9f3f 0xf6ffff12cffffe7c

def z55 : W := mkw 0x6a002b02a5026806 0x01a800ac0a9409a0 0x7e003b03ff006039 0xedf800ec0ffc0180

def z56 : W := mkw 0x00210915c3deefed 0x40008424570f7bbf 0x00000003c7fffff8 0x140000000f1fffff

def z57 : W := mkw 0x11401841804a4085 0x0045006106012902 0x7000380380000000 0x01c000e00e000000

def z58 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f8c38073e3d4 0x59c603e30e01cf8f

def z59 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff00fffffc03fb 0xe6fffc03fffff00f

def z60 : W := mkw 0x3ffaf6f840800520 0x08ffebdbe1020014 0xfffffffc40801f0f 0xfffffffff102007c

def z61 : W := mkw 0x1140000100480000 0x0045000004012000 0x31c0000380fc003a 0xe0c700000e03f000

def z62 : W := mkw 0x2a37000276a40038 0x04a8dc0009da9000 0x8e3f00007f000001 0x0638fc0001fc0000

def z63 : W := mkw 0x4480ffc08913fa87 0x011203ff02244fea 0x4000ffc00003ffc4 0x190003ff00000fff

def z64 : W := mkw 0x6e00a7022d013802 0x01b8029c08b404e0 0x0e00c7007f039c1d 0x7438031c01fc0e70

def z65 : W := mkw 0x842d85345ba53d78 0xc210b614d16e94f5 0x8e7f07fc7f8c7fef 0xbe39fc1ff1fe31ff

def z66 : W := mkw 0x7fdaffe889037806 0x09ff6bffa2240de0 0xfffffffc0003fc07 0xfbfffffff0000ff0

def z67 : W := mkw 0x0021001442840568 0x40008400510a1015 0x006300fc008c63ee 0xb8018c03f002318f

def z68 : W := mkw 0x842c843058a11530 0x8210b210c1628454 0x8c3c043078001c01 0x0630f010c1e00070

def z69 : W := mkw 0x95ecdcf1d8fbd7b5 0x8257b373c763ef5e 0xfdfcfcf3f8ffffff 0xfff7f3f3cfe3ffff

def z70 : W := mkw 0x2a00000224000000 0x00a8000008900000 0x3e000003ff000039 0xe4f800000ffc0000

def z71 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbd9c0003b8700010 0x42f670000ee1c000

def z72 : W := mkw 0x2e00a60000000000 0x00b8029800000000 0x7e63fffc00000007 0xe9f98ffff0000000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0x026307fc00000007 0xa8098c1ff0000000

def z74 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fffc7fc78f39f1f 0xfe3fff1ff1e3ce7c

def z75 : W := mkw 0x95ecd4f058b19730 0x8257b353c162c65c 0xfdfcfcf078f39f1f 0xfff7f3f3c1e3ce7c

def z76 : W := mkw 0x400001022d013802 0x0100000408b404e0 0x000000007f001c00 0x0400000001fc0070

def z77 : W := mkw 0x0400a60000000000 0x0010029800000000 0x4000ff0000000004 0x090003fc00000000

def z78 : W := mkw 0x40000902ad037806 0x010000240ab40de0 0x00000003ff03fc38 0x140000000ffc0ff0

def z79 : W := mkw 0x7fdaffeaad037806 0x09ff6bffaab40de0 0xffffffffff03fc3f 0xfffffffffffc0ff0

def z80 : W := mkw 0x0021000042840028 0x00008400010a1000 0x02630000478c002b 0xa4098c00011e3000

def z81 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8d9cc4b038739f14 0x52367312c0e1ce7c

def z82 : W := mkw 0x6e21af16ef877d6e 0x41b886bc5bbe1df5 0x7e63ffffff8fffff 0xfdf98ffffffe3fff

def z83 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc478c1fc3 0x04098c1ff11e307f

def z84 : W := mkw 0x7fc0ffc3ad5bfa87 0x01ff03ff0eb56fea 0x7fc0ffc3ffffffff 0xfdff03ff0fffffff

def z85 : W := mkw 0x7f53af03af4f780e 0x05fd4ebc0ebd3de0 0x7e43ff03ff0ffc3d 0xfdf90ffc0ffc3ff0

def z86 : W := mkw 0x3b73000042840028 0x00edcc00010a1000 0xbfff0000478c002b 0xe6fffc00011e3000

def z87 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbf9c0003ff700039 0xe6fe70000ffdc000

def z88 : W := mkw 0xee8cefa2bd33fa16 0x83ba33be8af4cfe8 0xff9cff03ff73fc3d 0xfffe73fc0ffdcff0

def z89 : W := mkw 0x3fdaf6e800108200 0x08ff6bdba0004208 0xfffffffc00f3831f 0xfbfffffff003ce0c

def z90 : W := mkw 0x3b73011443842d68 0x40edcc04510e10b5 0xbfff07fc478c7fef 0xfefffc1ff11e31ff

def z91 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0223073c47001c01 0x04088c1cf11c0070

def z92 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f80380738010 0x41c603e00e01ce00

def z93 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00ff03b803fc14 0x59f003fc0ee00ff0

def z94 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc40078739c1d 0x7636731001e1ce70

def z95 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0223073c47007c2d 0xbc088c1cf11c01f0

def z96 : W := mkw 0x3bf758c3f6fec2bd 0x04efdd630fdbfb0a 0xfffff803ffff803b 0xe7ffffe00ffffe00

def z97 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x00000000478c7fe8 0x14000000011e31ff

def z98 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff07fffffc003f 0xeefffc1ffffff000

def z99 : W := mkw 0x2e00ae0080024004 0x00b802b802000900 0x7e00ff038003e03d 0xf9f803fc0e000f80

def z100 : W := mkw 0x91ff40b152fc8738 0x8647fd02c54bf21c 0x81ff00b000fc0302 0x0207fc02c003f00c

def z101 : W := mkw 0x40000802ac035006 0x010000200ab00d40 0x00000003b8038010 0x000000000ee00e00

def z102 : W := mkw 0x3fdafee9805ac285 0x08ff6bfba6016b0a 0xfd9cf80380738010 0x43f673e00e01ce00

def z103 : W := mkw 0x11c050c100588281 0x004701430401620a 0x01c000c000fc03c2 0x000700030003f00f

def z104 : W := mkw 0x2a37000276a40038 0x04a8dc0009da9000 0x8fbf00007ff0001b 0x663efc0001ffc000

def z105 : W := mkw 0x0400840008011000 0x0010021000200440 0x0c00c40078039c1d 0x7430031001e00e70

def z106 : W := mkw 0x3fc0fec1805ac285 0x00ff03fb06016b0a 0x7fc0ffc380ffe3ff 0xf9ff03ff0e03ff8f

def z107 : W := mkw 0x042185144b853d68 0x40108614512e14f5 0x0e63c7fc7f8fffff 0xfc398f1ff1fe3fff

def z108 : W := mkw 0xc488efb08913ff06 0x831223bec2244ffc 0x4000ffb00003ff04 0x190003fec0000ffc

def z109 : W := mkw 0x3fdef6eb34680010 0x0cff7bdbacd1a000 0xffffffffb8700017 0xebfffffffee1c000

def z110 : W := mkw 0x0080408000108200 0x0002010200004208 0x0000c08000038304 0x1000030200000e0c

def z111 : W := mkw 0x1165000376ec0038 0x044594000ddbb000 0x31c00003fffc003a 0xe4c700000ffff000

def z112 : W := mkw 0x4400af02ad037806 0x011002bc0ab40de0 0x4000ff03ff03fc3c 0x1d0003fc0ffc0ff0

def z113 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbddc0003b8fc003a 0xe2f770000ee3f000

def z114 : W := mkw 0x3bd27ac9805ac285 0x08ef49eb26016b0a 0x73c3fbcf80ffe3fe 0xf9cf0fef3e03ff8f

def z115 : W := mkw 0x3ffff6eb76ec0038 0x0cffffdbaddbb000 0xfffffffffffc003f 0xeffffffffffff000

def z116 : W := mkw 0x3b52324800000000 0x08ed48c920000000 0x72433b4c00000000 0x89c90ced30000000

def z117 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000c0008c63ee 0xb80100030002318f

def z118 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc43078739c11 0x4636f310c1e1ce70

def z119 : W := mkw 0x0025000376ec0038 0x040094000ddbb000 0x02630003fffc003b 0xa4098c000ffff000

def z120 : W := mkw 0x0020001040800520 0x0000800041020014 0x026307fc40801f0f 0xbc098c1ff102007c

def z121 : W := mkw 0x3b73335c43842d68 0x48edcccd710e10b5 0x72633ffc478c7fef 0xbdc98cfff11e31ff

def z122 : W := mkw 0xbbff40b376fc8738 0x86effd02cddbf21c 0xbfff00b3fffc033b 0xe6fffc02cffff00c

def z123 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8fffc4b07fff9f3f 0xf63fff12c1fffe7c

def z124 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x000007fc00007fc4 0x1800001ff00001ff

def z125 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200070000000005 0xa808001c00000000

def z126 : W := mkw 0x84acc4b058a11530 0x8212b312c1628454 0x8dbcc4b078001c07 0x6636f312c1e00070

def z127 : W := mkw 0x11e159d5c3deefed 0x40478567570f7bbf 0x73e3ffffc7ffffff 0xfdcf8fffff1fffff

def z128 : W := mkw 0x3ffbf7fc43842d68 0x48ffefdff10e10b5 0xfffffffc478c7fef 0xfffffffff11e31ff

def z129 : W := mkw 0x0488f7fc01002d40 0x481223dff00400b5 0x4000fffc00007fc4 0x190003fff00001ff

def z130 : W := mkw 0x3fdafee9805ac285 0x08ff6bfba6016b0a 0xffffffff80ffe3ff 0xfbfffffffe03ff8f

def z131 : W := mkw 0x0025011453a42d78 0x40009404514e90b5 0x8fff07fc7ffc7fff 0xfe3ffc1ff1fff1ff

def z132 : W := mkw 0x80ac40b050b08730 0x8202b102c142c21c 0x81bc04b040f01f0f 0x3606f012c103c07c

def z133 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfdbcfcb000000007 0x63f6f3f2c0000000

def z134 : W := mkw 0x6e80ef82ad13fa06 0x01ba03be0ab44fe8 0x7f80ff83fff3ff3f 0xfdfe03fe0fffcffc

def z135 : W := mkw 0x95ffc4b15afd9738 0x8657ff12c56bf65c 0x8dffc4b078ff9f1f 0x7637ff12c1e3fe7c

def z136 : W := mkw 0x6e88efa2ad037806 0x01ba23be8ab40de0 0xffbcffb3ff03fc3f 0xfffef3fecffc0ff0

def z137 : W := mkw 0x11c050c000000000 0x0047014300000000 0x71c0f8c000000006 0xe9c703e300000000

def z138 : W := mkw 0x3ffff6e952ec0038 0x0cffffdba54bb000 0xfffffffc00fc0007 0xebfffffff003f000

def z139 : W := mkw 0x0000324800000000 0x080000c920000000 0x40003b4c00000000 0x090000ed30000000

def z140 : W := mkw 0x7f56ae03bc6b5016 0x05fd5ab80ef1ad40 0xfd9cf803b8738010 0x43f673e00ee1ce00

def z141 : W := mkw 0x11400801804a4004 0x0045002006012900 0x71c0f80380ffe03e 0xf9c703e00e03ff80

def z142 : W := mkw 0x3b52000000000000 0x00ed480000000000 0xbd9c000000000000 0x42f6700000000000

def z143 : W := mkw 0x0000010001002800 0x00000004000400a0 0x0200030007006020 0x8808000c001c0180

def z144 : W := mkw 0x0480c48008119200 0x0012031200204648 0x0d80c48078f39f1f 0x7436031201e3ce7c

def z145 : W := mkw 0x3fdaf6e900588281 0x08ff6bdba401620a 0xfffffffc00fc03c7 0xebfffffff003f00f

def z146 : W := mkw 0x84a9c5b44b95bf68 0xc212a716d12e56fd 0x0263c7fc478fffef 0xbc098f1ff11e3fff

def z147 : W := mkw 0x3b77000152ec0038 0x04eddc00054bb000 0xbfff000000fc0003 0xe2fffc000003f000

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400000008c002a 0xa001000000023000

def z149 : W := mkw 0x7fe1ffd7efdfffef 0x41ff87ff5fbf7fff 0x7fe3ffffffffffff 0xfdff8fffffffffff

def z150 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0xfe3fff3c00000005 0xebf8fffcf0000000

def z151 : W := mkw 0x0400840008011000 0x0010021000200440 0x0c00040078001c01 0x0430001001e00070

def z152 : W := mkw 0x0080408000108200 0x0002010200004208 0x0180c08000f3831e 0x700603020003ce0c

def z153 : W := mkw 0x3b530107274c2848 0x44ed4c041c9d30a1 0x3243034f870c60e0 0x88c90c0d3e1c3183

def z154 : W := mkw 0x0420841048811520 0x0010821041220454 0x0c20c4b078839f1f 0x74308312c1e20e7c

def z155 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000c0000003801c 0x7000030000000e00

def z156 : W := mkw 0x3b52000000000000 0x00ed480000000000 0xbfff07fc00000007 0xeafffc1ff0000000

def z157 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e63ffffff03fc3f 0xfdf98ffffffc0ff0

def z158 : W := mkw 0x008058c08012c285 0x0002016302004b0a 0x4000f8c00003e3c4 0x190003e300000f8f

def z159 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x73e3ffff80ffe3ff 0xf9cf8ffffe03ff8f

def z160 : W := mkw 0x0488c4a000000000 0x0012231280000000 0x8d9cc00000000000 0x4236730000000000

def z161 : W := mkw 0x7f40bf43ad4b7887 0x01fd02fd0eb52de2 0x7e40ff43ff0ffcfd 0xfdf903fd0ffc3ff3

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x00400040000c60e0 0x8801000100003183

def z163 : W := mkw 0x0408a62800000000 0x08102298a0000000 0x0000073c00000000 0x0000001cf0000000

def z164 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x0000c4b078f39f1c 0x14000312c1e3ce7c

def z165 : W := mkw 0x3b52324800000000 0x08ed48c920000000 0x7000380000000000 0x01c000e000000000

def z166 : W := mkw 0x3f5aa62800000000 0x08fd6a98a0000000 0xbfff073c00000003 0xe2fffc1cf0000000

def z167 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x004000c0478c7fee 0xbc010003011e31ff

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x0223073c00000001 0x00088c1cf0000000

def z169 : W := mkw 0x3fdaf7fc01002d40 0x48ff6bdff00400b5 0xfffffffc00007fc7 0xfbfffffff00001ff

def z170 : W := mkw 0x91e458d1d8fbd7b5 0x824791634763ef5e 0x71c0f8c3f8fffffe 0xfdc703e30fe3ffff

def z171 : W := mkw 0xc0240912fdb3ff36 0x830090244bf6cffc 0x00000003fff3ff38 0x140000000fffcffc

def z172 : W := mkw 0x3f5ab66800000000 0x08fd6ad9a0000000 0xfe7f3f7c00000001 0x8bf9fcfdf0000000

def z173 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x022307bc47801f0f 0x34088c1ef11e007c

def z174 : W := mkw 0x7f77af03ffef783e 0x05fddebc0fffbde0 0xffffff03fffffc3f 0xfffffffc0ffffff0

def z175 : W := mkw 0x2e9af6e800000000 0x08ba6bdba0000000 0xce3ffffc00000005 0x0b38fffff0000000

def z176 : W := mkw 0x0080408000108200 0x0002010200004208 0x0180008000f00302 0x000600020003c00c

def z177 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff04b3fffc1f3f 0xf6fffc12cffff07c

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000078000019 0x6430000001e00000

def z179 : W := mkw 0x40002b0081026806 0x010000ac020409a0 0x40003b0000006000 0x090000ec00000180

def z180 : W := mkw 0xee2caf32fda37d36 0x83b8b2bccbf68df4 0xfe3cff33ff03fc3d 0xfff8f3fccffc0ff0

def z181 : W := mkw 0x3b530003264c0008 0x04ed4c000c993000 0xbfff0003870c0023 0xe2fffc000e1c3000

def z182 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc008c63ef 0xfbfffffff002318f

def z183 : W := mkw 0x1140000100480000 0x0045000004012000 0x31c000c380fc63fe 0xf8c700030e03f18f

def z184 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfd9cf80000000000 0x43f673e000000000

def z185 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x022307fc47007fc5 0x1c088c1ff11c01ff

def z186 : W := mkw 0x0025000376ec0038 0x040094000ddbb000 0x00000003fffc0038 0x040000000ffff000

def z187 : W := mkw 0x00010003264c0008 0x040004000c993000 0x00000003870c0020 0x000000000e1c3000

def z188 : W := mkw 0x11c0408100588200 0x0047010204016208 0x31c0c08380ff833e 0xf0c703020e03fe0c

def z189 : W := mkw 0x0021001442840568 0x40008400510a1015 0x006304fc408c1fcf 0x34018c13f102307f

def z190 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffff80000000003 0xe3ffffe000000000

def z191 : W := mkw 0x8004000018319210 0x820010000060c648 0x0000000038738010 0x0000000000e1ce00

def z192 : W := mkw 0x1140000100480000 0x0045000004012000 0x30400003800c0020 0x80c100000e003000

def z193 : W := mkw 0x0000000000108200 0x0000000000004208 0x0000000000f38318 0x100000000003ce0c

def z194 : W := mkw 0x11da58e9805ac285 0x08476963a6016b0a 0xf1fff8ff80ffe3fe 0xfbc7ffe3fe03ff8f

def z195 : W := mkw 0x51c059c3ad5bfa87 0x014701670eb56fea 0x71c0f8c3fffffffe 0xfdc703e30fffffff

def z196 : W := mkw 0x2a12000000000000 0x00a8480000000000 0x8e3f000000000001 0x0238fc0000000000

def z197 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7040f8c3800fe3e4 0x99c103e30e003f8f

def z198 : W := mkw 0x0000080080024004 0x0000002002000900 0x000000038003e038 0x100000000e000f80

def z199 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0x8e3f073c00000001 0x0238fc1cf0000000

def z200 : W := mkw 0x2e00a60000000000 0x00b8029800000000 0x7e00ff0000000005 0xe9f803fc00000000

def z201 : W := mkw 0x0488c4a000000000 0x0012231280000000 0x8dbcc4b000000007 0x6236f312c0000000

def z202 : W := mkw 0x11e159d5c3deefed 0x40478567570f7bbf 0x71c0f8c3c7fffffe 0xfdc703e30f1fffff

def z203 : W := mkw 0x11530001024c0008 0x04454c0004093000 0x00430000000c0000 0x00010c0000003000

def z204 : W := mkw 0x3fdaf7e801002800 0x08ff6bdfa00400a0 0xfffffffc47007c2f 0xfffffffff11c01f0

def z205 : W := mkw 0x0400850009013800 0x00100214002404e0 0x0e00c7007f03fc3d 0xfc38031c01fc0ff0

def z206 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7200ff038703fc24 0x99c803fc0e1c0ff0

def z207 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x006300fc478c7fea 0x14018c03f11e31ff

def z208 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x00000000070c60e0 0x00000000001c3183

def z209 : W := mkw 0x80ad40b452b48778 0xc202b502d14ad21d 0x81ff00fc00fc03c2 0x0207fc03f003f00f

def z210 : W := mkw 0x6a000902ad037806 0x01a800240ab40de0 0x3e000003ff03fc39 0xf4f800000ffc0ff0

def z211 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dfcc4f078ffffff 0xfe37f313c1e3ffff

def z212 : W := mkw 0x3fdaf6ea24000000 0x08ff6bdba8900000 0xffffffffff00003f 0xeffffffffffc0000

def z213 : W := mkw 0x2a24000274a00030 0x00a8900009d28000 0xbfbc0003fff0003b 0xe6fef0000fffc000

def z214 : W := mkw 0x3ffbf7fc43842d68 0x48ffefdff10e10b5 0xfffffffc47001c07 0xeffffffff11c0070

def z215 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x0243034c070c60e0 0x88090c0d301c3183

def z216 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbd9c0003fffc0038 0x46f670000ffff000

def z217 : W := mkw 0x3b77010777ec2878 0x44eddc041ddfb0a1 0xbfff034ffffc60fb 0xeefffc0d3ffff183

def z218 : W := mkw 0x8024001058b19730 0x820090004162c65c 0x8dbc000078f39f1b 0x7636f00001e3ce7c

def z219 : W := mkw 0x84acc4a058b19230 0x8212b3128162c648 0x8dbcc00078f3801b 0x6636f30001e3ce00

def z220 : W := mkw 0x3b770803f6fec2bd 0x04eddc200fdbfb0a 0xbfff0003ffffe3fb 0xf6fffc000fffff8f

def z221 : W := mkw 0x3fdafee880024004 0x08ff6bfba2000900 0xffffffff8003e03f 0xfbfffffffe000f80

def z222 : W := mkw 0x7fdaffeaa5026806 0x09ff6bffaa9409a0 0xffffffff87006027 0xebfffffffe1c0180

def z223 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x81bcc4b000f39f06 0x1206f312c003ce7c

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000c0008c03c2 0x000100030002300f

def z225 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8dffc4fc78ff9fdf 0x7637ff13f1e3fe7f

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000380000038 0xe0c000000e000000

def z227 : W := mkw 0x6a002b02a5026806 0x01a800ac0a9409a0 0x72003f03c7007c2d 0xbdc800fc0f1c01f0

def z228 : W := mkw 0x3ffffeebf6fec2bd 0x0cfffffbafdbfb0a 0xffffffffffffe3ff 0xffffffffffffff8f

def z229 : W := mkw 0x6e21af16ef877d6e 0x41b886bc5bbe1df5 0x7e23ff3fff03fc3d 0xfdf88ffcfffc0ff0

def z230 : W := mkw 0x7fc0ffc3ad5bfa87 0x01ff03ff0eb56fea 0x7f80ff03ff73fc3d 0xfdfe03fc0ffdcff0

def z231 : W := mkw 0x0000000224000000 0x0000000008900000 0x00000003ff000038 0x040000000ffc0000

def z232 : W := mkw 0x3bc058c3a45ac285 0x00ef01630e916b0a 0x7fc0f8c3ffffe3ff 0xfdff03e30fffff8f

def z233 : W := mkw 0x1177000152ec0038 0x0445dc00054bb000 0x81ff000000fc0002 0x0207fc000003f000

def z234 : W := mkw 0x8488c4b008119700 0x82122312c020465c 0x0000c4b000039f04 0x10000312c0000e7c

def z235 : W := mkw 0x3ffbf6e842840028 0x08ffefdba10a1000 0xfffffffc478c002f 0xeffffffff11e3000

def z236 : W := mkw 0x11611955c3ce6ded 0x40458465570f39b7 0x72633fffc78c7fef 0xbdc98cffff1e31ff

def z237 : W := mkw 0x3fdafee9805ac285 0x08ff6bfba6016b0a 0xfddcf8c380ffe3fe 0xfbf773e30e03ff8f

def z238 : W := mkw 0xbffef6f858b19730 0x8afffbdbe162c65c 0xfdbcfcb078f39f1f 0x77f6f3f2c1e3ce7c

def z239 : W := mkw 0x0000010001002800 0x00000004000400a0 0x0200070047001c01 0x0408001c011c0070

def z240 : W := mkw 0x0000010001002800 0x00000004000400a0 0x0200070047007c2d 0xbc08001c011c01f0

def z241 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xb3ff000387fc0022 0x82cffc000e1ff000

def z242 : W := mkw 0x3b771843f6ee40bd 0x04eddc610fdbb902 0xffff3843fffc60fb 0xeffffce10ffff183

def z243 : W := mkw 0x0025000052a40038 0x00009400014a9000 0x8fff00007ffc003b 0xe63ffc0001fff000

def z244 : W := mkw 0xbfffc4a37efd9238 0x86ffff128dfbf648 0xbfffc003ffff803b 0xe6ffff000ffffe00

def z245 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff00c3fffc63ff 0xfefffc030ffff18f

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x0243034c00000000 0x88090c0d30000000

def z247 : W := mkw 0x3fc0f6c000000000 0x00ff03db00000000 0x7fc0ffc000000007 0xe9ff03ff00000000

def z248 : W := mkw 0x3f52a60000000000 0x00fd4a9800000000 0xffffff0000000007 0xebfffffc00000000

def z249 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x7000f80380ffe3fc 0xf9c003e00e03ff8f

def z250 : W := mkw 0x15c0dcc1885bd285 0x0057037306216f4a 0x7dc0fcc3f8ffffff 0xfdf703f30fe3ffff

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x000007fc00000004 0x0800001ff0000000

def z252 : W := mkw 0xbffff7fc5bb5bf78 0xcaffffdff16ed6fd 0xfffffffc7fffffff 0xfffffffff1ffffff

def z253 : W := mkw 0x0037000052a40038 0x0400dc00014a9000 0x803f000000000000 0x0200fc0000000000

def z254 : W := mkw 0x6e00af16ad037d46 0x41b802bc5ab40df5 0x7e00ffffff03fffd 0xfdf803fffffc0fff

def z255 : W := mkw 0x2a13000226040008 0x04a84c0008981000 0x0203000007000000 0x00080c00001c0000

def z256 : W := mkw 0x15c8d4e000000000 0x0057235380000000 0xfdfcfcf000000007 0xebf7f3f3c0000000

def z257 : W := mkw 0x3bd272c800000000 0x08ef49cb20000000 0x73c3fbcc00000006 0xe9cf0fef30000000

def z258 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c038c380fc63e2 0x89c700e30e03f18f

def z259 : W := mkw 0x3fdafee9804a4085 0x08ff6bfba6012902 0xffffffff800c60e7 0xebfffffffe003183

def z260 : W := mkw 0x8488c4b008119700 0x82122312c020465c 0x0c00c4b078039f1d 0x74300312c1e00e7c

def z261 : W := mkw 0x6e24af02fda37836 0x01b892bc0bf68de0 0xffbcff03fff3fc3f 0xfffef3fc0fffcff0

def z262 : W := mkw 0x7b532b03a74e680e 0x05ed4cac0e9d39a0 0x72433b03870c6020 0x89c90cec0e1c3180

def z263 : W := mkw 0x0021001042840528 0x00008400410a1014 0x026304b0478c1f2f 0xb4098c12c11e307c

def z264 : W := mkw 0x2a37011677a42d78 0x44a8dc0459de90b5 0x8e3f073c7f001c01 0x0638fc1cf1fc0070

def z265 : W := mkw 0x0080408000000000 0x0002010200000000 0x0180c08000000006 0x6006030200000000

def z266 : W := mkw 0x80240811d8fbd7b5 0x820090204763ef5e 0x00000003f8fffff8 0x140000000fe3ffff

def z267 : W := mkw 0x4421af14cb877d6e 0x411086bc532e1df5 0x4263fffc478fffef 0xbd098ffff11e3fff

def z268 : W := mkw 0x4400af0089037806 0x011002bc02240de0 0x4c00ff007803fc1d 0x7d3003fc01e00ff0

def z269 : W := mkw 0x11c050c000000000 0x0047014300000000 0x01c000c000000002 0x0007000300000000

def z270 : W := mkw 0x0025000152ec0038 0x04009400054bb000 0x0000000000fc0000 0x000000000003f000

def z271 : W := mkw 0xbfdef6e818319210 0x8aff7bdba060c648 0xfd9cf80038738010 0x43f673e000e1ce00

def z272 : W := mkw 0x008050c000000000 0x0002014300000000 0x4000f8c000000004 0x090003e300000000

def z273 : W := mkw 0x0021000042840028 0x00008400010a1000 0x0223000047000001 0x04088c00011c0000

def z274 : W := mkw 0x8408843008011500 0x82102210c0200454 0x0000043000001c00 0x00000010c0000070

def z275 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0x8c1c000000000000 0x0230700000000000

def z276 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x02630000478c7feb 0xb4098c00011e31ff

def z277 : W := mkw 0x3fdac4a000000000 0x00ff6b1280000000 0xbfffc4b000000007 0xe2ffff12c0000000

def z278 : W := mkw 0x1140000100480000 0x0045000004012000 0x3180000380700010 0x40c600000e01c000

def z279 : W := mkw 0x1140104100480081 0x0045004104012002 0x00400040000c00c0 0x0001000100003003

def z280 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0x8e7f07fc00000007 0xaa39fc1ff0000000

def z281 : W := mkw 0x3bd658c3b47ac295 0x04ef59630ed1eb0a 0xfd9cf803b8738010 0x43f673e00ee1ce00

def z282 : W := mkw 0x4400af0089037806 0x011002bc02240de0 0x7000ff038003fc3c 0xf9c003fc0e000ff0

def z283 : W := mkw 0x11da50e800000000 0x08476943a0000000 0xf1fff8fc00000006 0xebc7ffe3f0000000

def z284 : W := mkw 0x11ff50e952ec0038 0x0c47fd43a54bb000 0x81ff00fc00fc0002 0x0207fc03f003f000

def z285 : W := mkw 0x84acc4b050b08730 0x8212b312c142c21c 0x8dbcc4b000f00307 0x6236f312c003c00c

def z286 : W := mkw 0x808c40a010308210 0x820231028040c208 0x819c000000700000 0x020670000001c000

def z287 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x0203030c07000000 0x00080c0c301c0000

def z288 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x0000000000007fc0 0x10000000000001ff

def z289 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00f803ff03fc38 0x55f003e00ffc0ff0

def z290 : W := mkw 0x3bf758c3f6fec2bd 0x04efdd630fdbfb0a 0xfffff8c3ffffe3ff 0xffffffe30fffff8f

def z291 : W := mkw 0x1177011553ec2d78 0x4445dc04554fb0b5 0x83ff07fc47fc7fef 0xbe0ffc1ff11ff1ff

def z292 : W := mkw 0x95ccdce1987bd295 0x825733738661ef4a 0xfddcf8c3b8ffe3fe 0xfbf773e30ee3ff8f

def z293 : W := mkw 0x2a37000376ec0038 0x04a8dc000ddbb000 0x8e3f0003fffc0039 0x0638fc000ffff000

def z294 : W := mkw 0x11400801805ac285 0x0045002006016b0a 0x31c0000380ffe3fa 0xf0c700000e03ff8f

def z295 : W := mkw 0x0000000100588281 0x000000000401620a 0x0000000000fc03c0 0x000000000003f00f

def z296 : W := mkw 0x4000090089037806 0x0100002402240de0 0x000000000003fc00 0x1000000000000ff0

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000000f0001a 0x600600000003c000

def z298 : W := mkw 0x00000801804a4085 0x0000002006012902 0x00000003800c60e0 0x000000000e003183

def z299 : W := mkw 0x11401841805ac285 0x0045006106016b0a 0x7040384380ffe3f8 0x99c100e10e03ff8f

def z300 : W := mkw 0x11f758c1d2fec2bd 0x0447dd63074bfb0a 0xf1fff8c380ffe3fe 0xfbc7ffe30e03ff8f

def z301 : W := mkw 0x7f52bf4aad037806 0x09fd4afd2ab40de0 0x7e43ff4fff03fc3d 0xfdf90ffd3ffc0ff0

def z302 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfdfff8fc00000002 0x43f7ffe3f0000000

def z303 : W := mkw 0x0001000402040048 0x4000040010081001 0x0043004c000c00c0 0x00010c0130003003

def z304 : W := mkw 0x3fdbf7ec03042848 0x48ff6fdfb00c10a1 0xfffffffc070c60e7 0xebfffffff01c3183

def z305 : W := mkw 0x3b53324b264c0008 0x0ced4cc92c993000 0x72433b4f870c0020 0x89c90ced3e1c3000

def z306 : W := mkw 0x2e0084022c011000 0x00b8021008b00440 0x3e00c403ff039c3d 0xf4f803100ffc0e70

def z307 : W := mkw 0x2a00000000000000 0x00a8000000000000 0x3e00000000000001 0xe0f8000000000000

def z308 : W := mkw 0x2a37000276a40038 0x04a8dc0009da9000 0x8e7f00007f8c002b 0xa639fc0001fe3000

def z309 : W := mkw 0x3ffff7ff77ec2d78 0x4cffffdffddfb0b5 0xfffffffffffc7fff 0xfffffffffffff1ff

def z310 : W := mkw 0x2a37011677a42d78 0x44a8dc0459de90b5 0x8e7f07fc7f8c7fef 0xbe39fc1ff1fe31ff

def z311 : W := mkw 0x001a002800000000 0x08006800a0000000 0x803f003c00000000 0x0200fc00f0000000

def z312 : W := mkw 0x8488c4b008119700 0x82122312c020465c 0x8dbcc4b000039f07 0x7236f312c0000e7c

def z313 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x006307fc008c7fc6 0x18018c1ff00231ff

def z314 : W := mkw 0xfffefffafdb3ff36 0x8bfffbffebf6cffc 0xfffffffffff3ff3f 0xffffffffffffcffc

def z315 : W := mkw 0x11da50e900588281 0x08476943a401620a 0x81ff00fc00fc03c2 0x0207fc03f003f00f

def z316 : W := mkw 0x3b77011777ec2d78 0x44eddc045ddfb0b5 0xbfff073ffffc1c3b 0xe6fffc1cfffff070

def z317 : W := mkw 0x0020001040800520 0x0000800041020014 0x002004b040801f0f 0x34008012c102007c

def z318 : W := mkw 0x0000184080024085 0x0000006102000902 0x40003840000060c0 0x090000e100000183

def z319 : W := mkw 0x1177000152ec0038 0x0445dc00054bb000 0xb1ff000380fc003a 0xe2c7fc000e03f000

def z320 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8d9cc00078f39f18 0x5636730001e3ce7c

def z321 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000040040001c0d 0x3400001001000070

def z322 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc47001c07 0xac098c1ff11c0070

def z323 : W := mkw 0x3bf750c376fc82b9 0x04efdd430ddbf20a 0xbfff00c3fffc03fb 0xe6fffc030ffff00f

def z324 : W := mkw 0x3ffef6e850a00030 0x08fffbdba1428000 0xfffffffc78f0001f 0xeffffffff1e3c000

def z325 : W := mkw 0xeeacefb2fdb3ff36 0x83bab3becbf6cffc 0xffbcffb3fff3ff3f 0xfffef3fecfffcffc

def z326 : W := mkw 0x6a212b16e7866d6e 0x41a884ac5b9e19b5 0x72633fffc78c7fef 0xbdc98cffff1e31ff

def z327 : W := mkw 0x00210914c3866d6c 0x40008424530e19b5 0x7263ffffc78fffff 0xfdc98fffff1e3fff

def z328 : W := mkw 0x7f77a7037fed383a 0x05fdde9c0dffb4e0 0xbfff0703fffc1c3b 0xe6fffc1c0ffff070

def z329 : W := mkw 0x8488dcf08813d785 0x82122373c2204f5e 0x4000fcf00003ffc4 0x190003f3c0000fff

def z330 : W := mkw 0x2e9ae6a800000000 0x08ba6b9aa0000000 0x8fbfc7bc00000007 0x623eff1ef0000000

def z331 : W := mkw 0x11401841804a4085 0x0045006106012902 0x70403843800c60e0 0x89c100e10e003183

def z332 : W := mkw 0x008850e800000000 0x08022143a0000000 0x000000fc00000000 0x00000003f0000000

def z333 : W := mkw 0x802501145bb5bf78 0xc2009404516ed6fd 0x000000007ffffff8 0x1400000001ffffff

def z334 : W := mkw 0x3fffc4a376ec0038 0x04ffff128ddbb000 0xbfffc4b3fffc003f 0xe6ffff12cffff000

def z335 : W := mkw 0x11e151d443842d68 0x40478547510e10b5 0x73e3fffc478c7fef 0xfdcf8ffff11e31ff

def z336 : W := mkw 0x7b403b43a54a6887 0x01ed00ed0e9529a2 0x72403b43870c60e0 0x89c900ed0e1c3183

def z337 : W := mkw 0xc4acefb0d9b3ff36 0x8312b3bec366cffc 0xcdbcffb078f3ff1f 0x7f36f3fec1e3cffc

def z338 : W := mkw 0x0000010001002800 0x00000004000400a0 0x0000000047007c28 0x14000000011c01f0

def z339 : W := mkw 0xaebee6b858b19730 0x8abafb9ae162c65c 0x8fbfc7bc78f39f1f 0x763eff1ef1e3ce7c

def z340 : W := mkw 0x6e00a7022d013802 0x01b8029c08b404e0 0x7e00ff007f001c05 0xedf803fc01fc0070

def z341 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x0243074c470c7ced 0xbc090c1d311c31f3

def z342 : W := mkw 0x15daf6e800000000 0x08576bdba0000000 0xc1fffffc00000006 0x0b07fffff0000000

def z343 : W := mkw 0xbffefef9d8fbd7b5 0x8afffbfbe763ef5e 0xfffffffff8ffffff 0xffffffffffe3ffff

def z344 : W := mkw 0x6e00af0089037806 0x01b802bc02240de0 0x7e00ff000003fc05 0xf9f803fc00000ff0

def z345 : W := mkw 0x2e3fa62a76a40038 0x0cb8fe98a9da9000 0x8e3f073c7f000001 0x0638fc1cf1fc0000

def z346 : W := mkw 0x4400af0089037806 0x011002bc02240de0 0x4200ff004703fc2d 0xbd0803fc011c0ff0

def z347 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7e00ff03b8038015 0xe9f803fc0ee00e00

def z348 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffbfff3c00000001 0x43fefffcf0000000

def z349 : W := mkw 0x3b53334c03042848 0x48ed4ccd300c10a1 0x72433b4c070c60e0 0x89c90ced301c3183

def z350 : W := mkw 0x0021001442840568 0x40008400510a1015 0x00000000008c03c0 0x000000000002300f

def z351 : W := mkw 0x2a37000276a40038 0x04a8dc0009da9000 0xbe3f0003ff000039 0xe6f8fc000ffc0000

def z352 : W := mkw 0x84acf6f858b19730 0x8a12b3dbe162c65c 0xcdbcfffc78f39f1f 0x7f36f3fff1e3ce7c

def z353 : W := mkw 0x802500137efd9738 0x860094004dfbf65c 0x00000003ffff9f38 0x140000000ffffe7c

def z354 : W := mkw 0x3b52324800000000 0x08ed48c920000000 0x72633ffc00000007 0xa9c98cfff0000000

def z355 : W := mkw 0x0488c4a000000000 0x0012231280000000 0x0000c4b000000004 0x00000312c0000000

def z356 : W := mkw 0x2e88f6e800000000 0x08ba23dba0000000 0x7e00fffc00000005 0xe9f803fff0000000

def z357 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff039c11 0x45f803fc0ffc0e70

def z358 : W := mkw 0x3fdafee9805ac285 0x08ff6bfba6016b0a 0xffffffff80738017 0xebfffffffe01ce00

def z359 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfd9cfffc00000004 0x4bf673fff0000000

def z360 : W := mkw 0x91ec58f1d0fac7b5 0x8247b163c743eb1e 0xf1fcf8f380ffe3fe 0xfbc7f3e3ce03ff8f

def z361 : W := mkw 0x2e00a60000000000 0x00b8029800000000 0x0e00070000000001 0x0038001c00000000

def z362 : W := mkw 0xbffff6fb7efd9738 0x8effffdbedfbf65c 0xffffffffffff9f3f 0xfffffffffffffe7c

def z363 : W := mkw 0x3bda72e800000000 0x08ef69cba0000000 0xf3ff3bfc00000002 0x8bcffceff0000000

def z364 : W := mkw 0x11c050c000000000 0x0047014300000000 0x7180f80000000000 0x41c603e000000000

def z365 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x4e00ff007f03fc05 0x1d3803fc01fc0ff0

def z366 : W := mkw 0x11f750c152fc82b9 0x0447dd43054bf20a 0x81ff00c000fc03c2 0x0207fc030003f00f

def z367 : W := mkw 0x008058c08012c285 0x0002016302004b0a 0x4180f8c000f3e3de 0x790603e30003cf8f

def z368 : W := mkw 0x842c843058a11530 0x8210b210c1628454 0x8c3cc43078039c1d 0x7630f310c1e00e70

def z369 : W := mkw 0x8424841058b19730 0x821092104162c65c 0x0c00c40078f39f1d 0x7430031001e3ce7c

def z370 : W := mkw 0x008058c08012c285 0x0002016302004b0a 0x4000f80000038000 0x010003e000000e00

def z371 : W := mkw 0x0001000002040008 0x0000040000081000 0x02430000070c0020 0x80090c00001c3000

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x026307fc008c63ef 0xb8098c1ff002318f

def z373 : W := mkw 0x842c843058a11530 0x8210b210c1628454 0x8c3c04b078801f0f 0x3630f012c1e2007c

def z374 : W := mkw 0x4400af1489037d46 0x411002bc52240df5 0x4000fffc0003ffc4 0x190003fff0000fff

def z375 : W := mkw 0x2a000802a4024004 0x00a800200a900900 0x7e00f803ff03e03d 0xfdf803e00ffc0f80

def z376 : W := mkw 0xbf7f84337eed1538 0x86fdfe10cdfbb454 0xbfff0433fffc1c3b 0xe6fffc10cffff070

def z377 : W := mkw 0x7ff7ffc3fffffabf 0x05ffdfff0fffffea 0xffffffc3ffffffff 0xffffffff0fffffff

def z378 : W := mkw 0x4488ffe889037806 0x091223ffa2240de0 0x4000fffc0003fc04 0x190003fff0000ff0

def z379 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7c00f803b803e03c 0xf9f003e00ee00f80

def z380 : W := mkw 0x3b52000000000000 0x00ed480000000000 0xbfff000000000003 0xe2fffc0000000000

def z381 : W := mkw 0x6e00a7022d013802 0x01b8029c08b404e0 0x3e000703ff001c39 0xe4f8001c0ffc0070

def z382 : W := mkw 0x11401841804a4085 0x0045006106012902 0x7040f843800fe0fc 0xf9c103e10e003f83

def z383 : W := mkw 0x95c8dcf1885bd785 0x82572373c6216f5e 0x71c0fcf380fffffe 0xf9c703f3ce03ffff

def z384 : W := mkw 0x6e00a7022d013802 0x01b8029c08b404e0 0x0e0007007f007c2d 0xbc38001c01fc01f0

def z385 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f80380ffe3f8 0x51c603e00e03ff8f

def z386 : W := mkw 0x1177000152ec0038 0x0445dc00054bb000 0x83ff000047fc002b 0xa60ffc00011ff000

def z387 : W := mkw 0x0424840058a11030 0x0010921001628440 0x8dbcc40078f39c1f 0x7636f31001e3ce70

def z388 : W := mkw 0x7fdafeeaac035006 0x09ff6bfbaab00d40 0xfd9cf803b8038010 0x43f673e00ee00e00

def z389 : W := mkw 0x6e80ffc2ad13fa87 0x01ba03ff0ab44fea 0x7e00ffc3ff03fffd 0xfdf803ff0ffc0fff

def z390 : W := mkw 0x8024001058a11530 0x8200900041628454 0x0000000078001c00 0x0400000001e00070

def z391 : W := mkw 0xbfdaf6f808119700 0x8aff6bdbe020465c 0xfffffffc00039f07 0xfbfffffff0000e7c

def z392 : W := mkw 0x11e158c1c2dec2ad 0x00478563070b7b0a 0x73e3f8c3c7ffe3ff 0xfdcf8fe30f1fff8f

def z393 : W := mkw 0x0021000042840028 0x00008400010a1000 0x00630000008c0002 0x00018c0000023000

def z394 : W := mkw 0x2a00010225002800 0x00a80004089400a0 0x3e000703ff007c3d 0xfcf8001c0ffc01f0

def z395 : W := mkw 0x6e20af12ed837d26 0x01b882bc4bb60df4 0x7e20ffb3ff83ff3f 0xfdf883fecffe0ffc

def z396 : W := mkw 0x3b770803f6ee403c 0x04eddc200fdbb900 0xfffff803ffffe03f 0xffffffe00fffff80

def z397 : W := mkw 0x0021000042840028 0x00008400010a1000 0x00000000478c0028 0x04000000011e3000

def z398 : W := mkw 0x2a12220800000000 0x08a8488820000000 0x0203030c00000000 0x00080c0c30000000

def z399 : W := mkw 0x3b40000324480000 0x00ed00000c912000 0x3fc00003fffc003b 0xe4ff00000ffff000

def z400 : W := mkw 0xaebfc4b27eb59738 0x86baff12c9fad65c 0x8fbfc4b07ff39f1f 0x763eff12c1ffce7c

def z401 : W := mkw 0x7fc0ffc2ad037806 0x01ff03ff0ab40de0 0x7fc0ffc3ff03fc3f 0xfdff03ff0ffc0ff0

def z402 : W := mkw 0x0488c4a008011000 0x0012231280200440 0x8dbcc4b078039c1f 0x7636f312c1e00e70

def z403 : W := mkw 0x00a4408050b08230 0x000291020142c208 0x8dbcc08078f3831f 0x7636f30201e3ce0c

def z404 : W := mkw 0x2a25000376ec0038 0x04a894000ddbb000 0x3e000003fffc0039 0xe4f800000ffff000

def z405 : W := mkw 0x0024000050a00030 0x0000900001428000 0x8c3c000078000001 0x0630f00001e00000

def z406 : W := mkw 0x0004000334680010 0x040010000cd1a000 0x00000003b8700010 0x000000000ee1c000

def z407 : W := mkw 0xbfffdcf3feffd7bd 0x86ffff73cffbff5e 0xfffffcf3ffffffff 0xfffffff3cfffffff

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000602c 0xb800000000000180

def z409 : W := mkw 0x0025011777ec2d78 0x440094045ddfb0b5 0x00000003fffc7ff8 0x140000000ffff1ff

def z410 : W := mkw 0x1161011543cc2d68 0x40458404550f30b5 0x33e307ffc7fc7fff 0xfccf8c1fff1ff1ff

def z411 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x0e000703ff03fc39 0x1438001c0ffc0ff0

def z412 : W := mkw 0xbffec4b058b19730 0x82fffb12c162c65c 0xbfffc4b078f39f1f 0xf6ffff12c1e3ce7c

def z413 : W := mkw 0xee2ca7327da13d32 0x83b8b29cc9f684f4 0x8e3c07307f001c01 0x0638f01cc1fc0070

def z414 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffdffb4c00000000 0xcbff7fed30000000

def z415 : W := mkw 0x008050c000108281 0x000201430000420a 0x000000c0000003c0 0x000000030000000f

def z416 : W := mkw 0x6e88ffeaad037806 0x09ba23ffaab40de0 0x7e00ffffff03fc3d 0xfdf803fffffc0ff0

def z417 : W := mkw 0x0021001442840568 0x40008400510a1015 0x026300fc478c03eb 0xa4098c03f11e300f

def z418 : W := mkw 0x3bff50eb76ec0038 0x0ceffd43addbb000 0xbfff00fffffc003b 0xe6fffc03fffff000

def z419 : W := mkw 0x0488f6e800000000 0x081223dba0000000 0x4000f80000000000 0x010003e000000000

def z420 : W := mkw 0x0000000100480000 0x0000000004012000 0x0000000380fc0038 0x000000000e03f000

def z421 : W := mkw 0x00210915c3deefed 0x40008424570f7bbf 0x026307ffc7ffffff 0xbc098c1fff1fffff

def z422 : W := mkw 0x7f77af17ffef7d7e 0x45fddebc5fffbdf5 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0x84a8c4b048919720 0x8212a312c122465c 0x0020c4b040839f0f 0x34008312c1020e7c

def z424 : W := mkw 0x11e151d543dcafe9 0x40478547550f72bf 0x03e307fc47fc7fef 0xbc0f8c1ff11ff1ff

def z425 : W := mkw 0x0021010043842828 0x00008404010e10a0 0x02630700478c7c2f 0xbc098c1c011e31f0

def z426 : W := mkw 0x0000080080024004 0x0000002002000900 0x7000f80380038010 0x41c003e00e000e00

def z427 : W := mkw 0x808840b000108700 0x82022102c000421c 0x000000b000000300 0x00000002c000000c

def z428 : W := mkw 0x84acc5b059b1bf30 0x8212b316c166c6fc 0x8fbcc7b07ff3ff3f 0xfe3ef31ec1ffcffc

def z429 : W := mkw 0x6a002b02ad037806 0x01a800ac0ab40de0 0x72003b03ff03fc38 0x9dc800ec0ffc0ff0

def z430 : W := mkw 0x008840a000000000 0x0002210280000000 0x81bc00b000000002 0x0206f002c0000000

def z431 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0x8fff07fc00000003 0x023ffc1ff0000000

def z432 : W := mkw 0x40250903ffef783e 0x050094240fffbde0 0x00000003fffffc38 0x140000000ffffff0

def z433 : W := mkw 0x0000010001002800 0x00000004000400a0 0x024007c0478c7fef 0xbc09001f011e31ff

def z434 : W := mkw 0x04008c0088035004 0x0010023002200d40 0x7c00fc03f803fc3d 0xfdf003f00fe00ff0

def z435 : W := mkw 0x0001011403042d48 0x40000404500c10b5 0x024307fc070c7fe4 0x98090c1ff01c31ff

def z436 : W := mkw 0x11401841804a4085 0x0045006106012902 0x71c0384380fc60fa 0xe9c700e10e03f183

def z437 : W := mkw 0x1152104800000000 0x0845484120000000 0x0043004c00000000 0x00010c0130000000

def z438 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f80380ff803a 0xe1c703e00e03fe00

def z439 : W := mkw 0x40000903ad5bfa87 0x010000240eb56fea 0x00000003fffffff8 0x140000000fffffff

def z440 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0x7243fffc00000004 0x89c90ffff0000000

def z441 : W := mkw 0x3b77011777ec2d78 0x44eddc045ddfb0b5 0xbfff0003fffc7ffb 0xf6fffc000ffff1ff

def z442 : W := mkw 0x84adc5b45bb5bf78 0xc212b716d16ed6fd 0x8dbcc4b07fffffff 0x7636f312c1ffffff

def z443 : W := mkw 0x15c8f6e800000000 0x085723dba0000000 0x71c0fffc00000006 0xe9c703fff0000000

def z444 : W := mkw 0x8488c4b008119700 0x82122312c020465c 0x0180c4b000f39f1e 0x70060312c003ce7c

def z445 : W := mkw 0x0000090081026804 0x00000024020409a0 0x7200ff03c703fc3d 0xfdc803fc0f1c0ff0

def z446 : W := mkw 0x0000001000000500 0x0000000040000014 0x000004b000001f04 0x10000012c000007c

def z447 : W := mkw 0x40000902ad037806 0x010000240ab40de0 0x02000703ff03fc3d 0xbc08001c0ffc0ff0

def z448 : W := mkw 0x11c050c000000000 0x0047014300000000 0x71c0f8c0008c63ee 0xf9c703e30002318f

def z449 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0x8fff00007ffc0003 0x063ffc0001fff000

def z450 : W := mkw 0x2e00a60224000000 0x00b8029808900000 0x7e00ff03ff00003d 0xedf803fc0ffc0000

def z451 : W := mkw 0x6e37a7027fa5383a 0x05b8de9c09fe94e0 0x8e3f07007f001c01 0x0638fc1c01fc0070

def z452 : W := mkw 0x11c050c100588281 0x004701430401620a 0x0180000000700000 0x000600000001c000

def z453 : W := mkw 0x3fdaf6e900480000 0x08ff6bdba4012000 0xffffffff80fc003f 0xebfffffffe03f000

def z454 : W := mkw 0x008058c08012c285 0x0002016302004b0a 0x4040f8c0008fe3ee 0xb90103e300023f8f

def z455 : W := mkw 0x3b77010377ec2838 0x04eddc040ddfb0a0 0xbfff0703fffc7c3f 0xfefffc1c0ffff1f0

def z456 : W := mkw 0x00804881805ac285 0x0002012206016b0a 0x0180c08380ffe3fe 0x700603020e03ff8f

def z457 : W := mkw 0x008048808012c204 0x0002012202004b08 0x7180f88380f3e33e 0xf9c603e20e03cf8c

def z458 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x01c000c380ffe3fa 0x100700030e03ff8f

def z459 : W := mkw 0x8488f6f808119700 0x8a1223dbe020465c 0x4000fffc00039f04 0x190003fff0000e7c

def z460 : W := mkw 0x0021000042840028 0x00008400010a1000 0x026300c0478c63ef 0xbc098c03011e318f

def z461 : W := mkw 0x4400a70009013802 0x0110029c002404e0 0x0000070000001c00 0x0000001c00000070

def z462 : W := mkw 0x802501145bb5bf78 0xc2009404516ed6fd 0x026307fc7fffffff 0xbc098c1ff1ffffff

def z463 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000800080030e 0x300000020002000c

def z464 : W := mkw 0xbfdef6e818319210 0x8aff7bdba060c648 0xfffffffc38738017 0xebfffffff0e1ce00

def z465 : W := mkw 0x008058c1805ac285 0x0002016306016b0a 0x4000f8c380ffe3fc 0x190003e30e03ff8f

def z466 : W := mkw 0xaeace6b058b19730 0x82bab39ac162c65c 0xffbcffb078f39f1f 0xfffef3fec1e3ce7c

def z467 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x0000000380738010 0x000000000e01ce00

def z468 : W := mkw 0x1164000150e80030 0x004590000543a000 0xbdfc0003f8fc003b 0xe6f7f0000fe3f000

def z469 : W := mkw 0x0400840008011000 0x0010021000200440 0x0000c40000039c04 0x1000031000000e70

def z470 : W := mkw 0x7b523b4aa5026806 0x09ed48ed2a9409a0 0x72433b4f87006020 0x89c90ced3e1c0180

def z471 : W := mkw 0x04a9c5b443842d68 0x4012a716d10e10b5 0x8fffc7fc478c7fef 0xfe3fff1ff11e31ff

def z472 : W := mkw 0x0020001040800520 0x0000800041020014 0x0000000040801f08 0x140000000102007c

def z473 : W := mkw 0x0488c4a000000000 0x0012231280000000 0x8fffc7fc00000007 0xea3fff1ff0000000

def z474 : W := mkw 0x11e058d1c0dac7a5 0x0047816347036b1e 0x71e0fcf3c0ffffff 0xfdc783f3cf03ffff

def z475 : W := mkw 0xffffefb3ffffff3e 0x87ffffbecffffffc 0xffffffb3ffffff3f 0xfffffffecffffffc

def z476 : W := mkw 0x11c050c100588281 0x004701430401620a 0x31c000c380fc03fa 0xe0c700030e03f00f

def z477 : W := mkw 0x1177000152ec0038 0x0445dc00054bb000 0x8dff000078fc001b 0x6637fc0001e3f000

def z478 : W := mkw 0x3b530003264c0008 0x04ed4c000c993000 0x3e430003ff0c0039 0xe4f90c000ffc3000

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000c0000063c4 0x180000030000018f

def z480 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x024303cc078c63ee 0xb8090c0f301e318f

def z481 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfddcf8c000000006 0xebf773e300000000

def z482 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x004000c380ffe3fe 0xb80100030e03ff8f

def z483 : W := mkw 0x40210916ef877d6e 0x410084245bbe1df5 0x00000003ff8ffff8 0x140000000ffe3fff

def z484 : W := mkw 0x3b76000050a00030 0x00edd80001428000 0xbfff000078f0001b 0xe6fffc0001e3c000

def z485 : W := mkw 0x8488c5b40911bf40 0xc2122316d02446fd 0x0000c7fc0003ffc4 0x1800031ff0000fff

def z486 : W := mkw 0x3bf750c376ec0038 0x04efdd430ddbb000 0xfffff8c3fffc003f 0xefffffe30ffff000

def z487 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0243034c478c7fe8 0x9c090c0d311e31ff

def z488 : W := mkw 0x0025000376ec0038 0x040094000ddbb000 0x8dbc0003fffc003b 0x6636f0000ffff000

def z489 : W := mkw 0x7f77ae03feef503e 0x05fddeb80ffbbd40 0xfffff803ffff803b 0xe7ffffe00ffffe00

def z490 : W := mkw 0x6e1aaf2aad037806 0x09b86abcaab40de0 0xfe3fff3fff03fc3d 0xfff8fffcfffc0ff0

def z491 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x000007fc478c7fec 0x1c00001ff11e31ff

def z492 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfbf0003ff700011 0x46fefc000ffdc000

def z493 : W := mkw 0x7f56af03bd6b7816 0x05fd5abc0ef5ade0 0xff9cff03ff73fc3d 0xfffe73fc0ffdcff0

def z494 : W := mkw 0xae3ea63858a11530 0x8ab8fa98e1628454 0x8e3f073c78001c01 0x0638fc1cf1e00070

def z495 : W := mkw 0x0000080080024004 0x0000002002000900 0x7000380380006020 0x89c000e00e000180

def z496 : W := mkw 0x00a159d4c396efed 0x40028567530e5bbf 0x4263fffc478fffef 0xbd098ffff11e3fff

def z497 : W := mkw 0x04a8c4b040800520 0x0012a312c1020014 0x8dbcc4b040801f0f 0x7636f312c102007c

def z498 : W := mkw 0x842c843058b19730 0x8210b210c162c65c 0x8c3c043078f39f19 0x1630f010c1e3ce7c

def z499 : W := mkw 0x11fb51fc43842d68 0x4847ed47f10e10b5 0x83ff07fc478c7fef 0xbe0ffc1ff11e31ff

def z500 : W := mkw 0xc4accdb2fdb3ff36 0x8312b336cbf6cffc 0x8dbcc4b3fff3ff3f 0x7636f312cfffcffc

def z501 : W := mkw 0x2e00a60008011000 0x00b8029800200440 0x7e00ff0078039c1d 0xfdf803fc01e00e70

def z502 : W := mkw 0x7bc07bc3a55aea87 0x01ef01ef0e956baa 0x73c0fbc387ffe3fe 0xf9cf03ef0e1fff8f

def z503 : W := mkw 0x2e00a70001002800 0x00b8029c000400a0 0x7e00ff0047007c2d 0xfdf803fc011c01f0

def z504 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbdff0003b8fc0012 0x42f7fc000ee3f000

def z505 : W := mkw 0x11c058c1804a4085 0x0047016306012902 0x71c0f8c3800c60e6 0xe9c703e30e003183

def z506 : W := mkw 0x84acc5b459b1bf70 0xc212b316d166c6fd 0x8dbcc7fc78f3ffdf 0x7e36f31ff1e3cfff

def z507 : W := mkw 0x3b77000276a40038 0x04eddc0009da9000 0xbfff00007f000003 0xe6fffc0001fc0000

def z508 : W := mkw 0x0000000000000000 0x0000000000000000 0x8dbc000000000003 0x6236f00000000000

def z509 : W := mkw 0x11c050c100480000 0x0047014304012000 0x71c0f8c380fc003e 0xe9c703e30e03f000

def z510 : W := mkw 0x6e25af03ffef783e 0x05b896bc0fffbde0 0x7e00ff03fffffc3d 0xfdf803fc0ffffff0

def z511 : W := mkw 0x840c842018211010 0x8210321080608440 0x8c1c000038000000 0x0230700000e00000

def z512 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e40ffc3ff8fffff 0xfdf903ff0ffe3fff

def z513 : W := mkw 0x40000902a5026806 0x010000240a9409a0 0x0000000387006020 0x000000000e1c0180

def z514 : W := mkw 0x80ac40b058b19730 0x8202b102c162c65c 0x81bc00b078f39f1a 0x1606f002c1e3ce7c

def z515 : W := mkw 0x2a16000234200010 0x04a8580008d08000 0x8c1c000038000000 0x0230700000e00000

def z516 : W := mkw 0x7fdafeeaac035006 0x09ff6bfbaab00d40 0xffffffffb8038017 0xebfffffffee00e00

def z517 : W := mkw 0x3b52000224000000 0x00ed480008900000 0xbfff0003ff00003b 0xe6fffc000ffc0000

def z518 : W := mkw 0x6a002b02a5026806 0x01a800ac0a9409a0 0x7200fb038703e03c 0xf9c803ec0e1c0f80

def z519 : W := mkw 0x3b76000374e80030 0x04edd8000dd3a000 0xbdbc0003f8f0001b 0x66f6f0000fe3c000

def z520 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0x32430003fffc0038 0x84c90c000ffff000

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x0263000000000003 0xa0098c0000000000

def z522 : W := mkw 0x84acccb1d8fbd7b5 0x8212b332c763ef5e 0x8dbcc4b3f8ffffff 0x7636f312cfe3ffff

def z523 : W := mkw 0x40000902ad037806 0x010000240ab40de0 0x7000f803ff03fc3c 0xfdc003e00ffc0ff0

def z524 : W := mkw 0x802c003050a00530 0x8200b000c1428014 0x803c003000000000 0x0200f000c0000000

def z525 : W := mkw 0x8024001050b08730 0x820090004142c21c 0x0000000000f00300 0x000000000003c00c

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x002004b000000007 0x20008012c0000000

def z527 : W := mkw 0x1152000000000000 0x0045480000000000 0x81ff000000000002 0x0207fc0000000000

def z528 : W := mkw 0x11e558c3f6fec2bd 0x044795630fdbfb0a 0x71c0f8c3ffffe3fe 0xfdc703e30fffff8f

def z529 : W := mkw 0x3ffbfffdc3deefed 0x48ffeffff70f7bbf 0xffffffffc7ffffff 0xffffffffff1fffff

def z530 : W := mkw 0x0020001040800520 0x0000800041020014 0x0020043040001c01 0x04008010c1000070

def z531 : W := mkw 0x3b531843a64e408d 0x04ed4c610e993902 0x72433843870c60e0 0x89c90ce10e1c3183

def z532 : W := mkw 0x0025011777ec2d78 0x440094045ddfb0b5 0x026307fffffc7fff 0xbc098c1ffffff1ff

def z533 : W := mkw 0x11c058c080024004 0x0047016302000900 0x71c0f8c38003e03e 0xf9c703e30e000f80

def z534 : W := mkw 0x40210916ef877d6e 0x410084245bbe1df5 0x026307ffff8fffff 0xbc098c1ffffe3fff

def z535 : W := mkw 0x3f52b64800000000 0x08fd4ad920000000 0x7e43ff4c00000005 0xe9f90ffd30000000

def z536 : W := mkw 0x0080408000108200 0x0002010200004208 0x0180c00000738010 0x400603000001ce00

def z537 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0263073c478c1c2b 0xa4098c1cf11e3070

def z538 : W := mkw 0x15c8dce1805ac285 0x0057237386016b0a 0xfdfcfcf380ffe3ff 0xfbf7f3f3ce03ff8f

def z539 : W := mkw 0x11c050c100588281 0x004701430401620a 0x01c000c000fc63ee 0xb80700030003f18f

def z540 : W := mkw 0xeeaceeb2fcb3d736 0x83bab3bacbf2cf5c 0xfdbcfcb3f8f39f1f 0x77f6f3f2cfe3ce7c

def z541 : W := mkw 0x1140000100480000 0x0045000004012000 0x01c0000000fc0002 0x000700000003f000

def z542 : W := mkw 0x55c0ffc1895bfa87 0x015703ff06256fea 0x71c0ffc380fffffe 0xf9c703ff0e03ffff

def z543 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x41c0f8c000ffe3c6 0x190703e30003ff8f

def z544 : W := mkw 0x6e1aa72a2d013802 0x09b86a9ca8b404e0 0x8e3f073c7f001c01 0x0638fc1cf1fc0070

def z545 : W := mkw 0x0001010403042848 0x40000404100c10a1 0x026307fc070c60e7 0xa8098c1ff01c3183

def z546 : W := mkw 0x84adc4b37efd9738 0x8612b712cdfbf65c 0x8dbcc4b3ffff9f3f 0x7636f312cffffe7c

def z547 : W := mkw 0x80ad41b453b4af78 0xc202b506d14ed2bd 0x83ff07fc47fc7fef 0xbe0ffc1ff11ff1ff

def z548 : W := mkw 0x0020000040800020 0x0000800001020000 0x002000004080000b 0x2400800001020000

def z549 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbfff0003b8700013 0xe2fffc000ee1c000

def z550 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0263077c470c7ce1 0x8c098c1df11c31f3

def z551 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x02000700478c7fed 0xbc08001c011e31ff

def z552 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z553 : W := mkw 0xeeadefb6ffb7ff7e 0xc3bab7bedbfedffd 0xffffffffffffffff 0xffffffffffffffff

def z554 : W := mkw 0x8000001008119700 0x820000004020465c 0x0000000000039f00 0x1000000000000e7c

def z555 : W := mkw 0xae3f84327ea51538 0x86b8fe10c9fa9454 0x8e3f04307f001c01 0x0638fc10c1fc0070

def z556 : W := mkw 0x8488c4a008119200 0x8212231280204648 0x0000c00000038000 0x0000030000000e00

def z557 : W := mkw 0x0025000276a40038 0x0400940009da9000 0x000000007f000000 0x0400000001fc0000

def z558 : W := mkw 0x3f7fa62b76ec0038 0x0cfdfe98addbb000 0xbfff073ffffc003b 0xe6fffc1cfffff000

def z559 : W := mkw 0x80a4409058b19730 0x820291024162c65c 0x0180c08078f39f1e 0x7406030201e3ce7c

def z560 : W := mkw 0x3b77324b76ec0038 0x0ceddcc92ddbb000 0xffff3b4ffffc003b 0xeffffced3ffff000

def z561 : W := mkw 0x95ecc4b158f99730 0x8257b312c563e65c 0xbdfcc4b3f8ff9f3f 0xf6f7f312cfe3fe7c

def z562 : W := mkw 0x7fc0fec3ac5bd287 0x01ff03fb0eb16f4a 0x7d80f803b8738010 0x41f603e00ee1ce00

def z563 : W := mkw 0x2e21a71443842d68 0x40b8869c510e10b5 0x7e63fffc478c7fef 0xfdf98ffff11e31ff

def z564 : W := mkw 0x11c050c100588281 0x004701430401620a 0x71c0f8c000fc03c6 0xe9c703e30003f00f

def z565 : W := mkw 0x11c159c5835eeacd 0x40470567160d7bab 0x73c3fbcf87ffe3fe 0xf9cf0fef3e1fff8f

def z566 : W := mkw 0x1177000376ec0038 0x0445dc000ddbb000 0x81ff0003fffc003a 0x0607fc000ffff000

def z567 : W := mkw 0x3fdef6eb34680010 0x0cff7bdbacd1a000 0xfd9cf803b8700010 0x43f673e00ee1c000

def z568 : W := mkw 0x2a00000224000000 0x00a8000008900000 0x3200000387000020 0x80c800000e1c0000

def z569 : W := mkw 0x0021010443842868 0x40008404110e10a1 0x0263034c478c60eb 0xac098c0d311e3183

def z570 : W := mkw 0xee8ceea2bc33d216 0x83ba33ba8af0cf48 0xfd9cf803b8738010 0x43f673e00ee1ce00

def z571 : W := mkw 0x7fffffebffef783e 0x0dffffffafffbde0 0xfffffffffffffc3f 0xfffffffffffffff0

def z572 : W := mkw 0x1177001552ec0578 0x4445dc00554bb015 0x81ff00fc00fc03c2 0x0207fc03f003f00f

def z573 : W := mkw 0x91ec50f150f887b1 0x8247b143c543e21e 0x81fc00f000fc03c2 0x0207f003c003f00f

def z574 : W := mkw 0x6a002a02a4024006 0x01a800a80a900900 0x7000380380000000 0x01c000e00e000000

def z575 : W := mkw 0x80ac40b050b08730 0x8202b102c142c21c 0x8dbc00b078f0031b 0x6636f002c1e3c00c

def z576 : W := mkw 0xbffef6f850b08730 0x8afffbdbe142c21c 0xfffffffc00f00307 0xebfffffff003c00c

def z577 : W := mkw 0x3ffff6ea76a40038 0x0cffffdba9da9000 0xfffffffc7f000007 0xeffffffff1fc0000

def z578 : W := mkw 0x6e00af03ad5bfa87 0x01b802bc0eb56fea 0x7e00ff03fffffffd 0xfdf803fc0fffffff

def z579 : W := mkw 0x6e21af16ef877d6e 0x41b886bc5bbe1df5 0x7e00ff03ff8ffffd 0xfdf803fc0ffe3fff

def z580 : W := mkw 0x7fc0fec3ac5bd287 0x01ff03fb0eb16f4a 0x7dc0f8c3b8ffe3fe 0xf9f703e30ee3ff8f

def z581 : W := mkw 0x11c059c1815aea85 0x0047016706056baa 0x73c0ffc3c7ffffff 0xfdcf03ff0f1fffff

def z582 : W := mkw 0x44008d02ad037806 0x011002340ab40de0 0x0c00c403ff03fc3d 0x743003100ffc0ff0

def z583 : W := mkw 0x6e01af06af07784e 0x41b806bc1abc1de1 0x7e43ff4fff0ffcfd 0xfdf90ffd3ffc3ff3

def z584 : W := mkw 0x3fdafee88012c285 0x08ff6bfba2004b0a 0xfffffffc0003e3c7 0xfbfffffff0000f8f

def z585 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0223073c478c7fe9 0x14088c1cf11e31ff

def z586 : W := mkw 0x7f40af03ad4b7806 0x01fd02bc0eb52de0 0x7fc0ff03fffffc3f 0xfdff03fc0ffffff0

def z587 : W := mkw 0x95ecd4f158f997b1 0x8257b353c563e65e 0x8dfcc4f078ff9fdf 0x7637f313c1e3fe7f

def z588 : W := mkw 0x2e00a60000000000 0x00b8029800000000 0x7c00f80000000000 0x41f003e000000000

def z589 : W := mkw 0x6a012b06a706684e 0x41a804ac1a9c19a1 0x72433b4f870c60e0 0x89c90ced3e1c3183

def z590 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f88380f3831e 0x71c603e20e03ce0c

def z591 : W := mkw 0x0000001400000540 0x4000000050000015 0x000000fc000003c0 0x00000003f000000f

def z592 : W := mkw 0x0000080080024004 0x0000002002000900 0x4000f8000003e004 0x190003e000000f80

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x004000c000000006 0xa801000300000000

def z594 : W := mkw 0x842c843058a11530 0x8210b210c1628454 0x8dbc043078f01c1b 0x6636f010c1e3c070

def z595 : W := mkw 0x2a00000224000000 0x00a8000008900000 0x0e0000007f000001 0x0438000001fc0000

def z596 : W := mkw 0x0400840000000000 0x0010021000000000 0x0c00c40000000005 0x6030031000000000

def z597 : W := mkw 0x3bf759d7f7feeffd 0x44efdd675fdffbbf 0xffffffffffffffff 0xffffffffffffffff

def z598 : W := mkw 0x0000010001002800 0x00000004000400a0 0x0000070000007c04 0x1800001c000001f0

def z599 : W := mkw 0x3b52000000000000 0x00ed480000000000 0x3243000000000000 0x80c90c0000000000

def z600 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7e00f803ff038039 0xe5f803e00ffc0e00

def z601 : W := mkw 0x0000080080024004 0x0000002002000900 0x7040f8c3808fe3fe 0xf9c103e30e023f8f

def z602 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f843807fe0f0 0xc9c703e10e01ff83

def z603 : W := mkw 0x7b772b03f7ee683e 0x05eddcac0fdfb9a0 0xffff3b03fffc603b 0xeffffcec0ffff180

def z604 : W := mkw 0x3b73000366cc0028 0x04edcc000d9b3000 0x32630003c78c002b 0xa4c98c000f1e3000

def z605 : W := mkw 0x3b73011767cc2d68 0x44edcc045d9f30b5 0x326307ffc78c7fef 0xbcc98c1fff1e31ff

def z606 : W := mkw 0xee24af12fdb3ff36 0x83b892bc4bf6cffc 0x7e00ff03fff3ff3d 0xfdf803fc0fffcffc

def z607 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8dbcc4b038738017 0x6236f312c0e1ce00

def z608 : W := mkw 0x0488f6e800000000 0x081223dba0000000 0xcdbcfffc00000007 0x6b36f3fff0000000

def z609 : W := mkw 0x2a21000266840028 0x00a88400099a1000 0x3e630003ff8c003b 0xe4f98c000ffe3000

def z610 : W := mkw 0x6e37af02ffa7783e 0x05b8debc0bfe9de0 0xfe3fff03ff03fc3d 0xfff8fffc0ffc0ff0

def z611 : W := mkw 0x0000000000000000 0x0000000000000000 0x7000f80000000004 0xe9c003e000000000

def z612 : W := mkw 0x04acc4a050a00030 0x0012b31281428000 0x8dbcc4b078f0001f 0x6636f312c1e3c000

def z613 : W := mkw 0x2a21011667842d68 0x40a88404599e10b5 0x3e6307ffff8c7fff 0xfcf98c1ffffe31ff

def z614 : W := mkw 0x11e158d5c2dec7ed 0x40478563570b7b1f 0x71e3f8ff80ffe3fe 0xf9c78fe3fe03ff8f

def z615 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x026307fc00007fc7 0xb8098c1ff00001ff

def z616 : W := mkw 0x0080408000108200 0x0002010200004208 0x01c0c0c000ffe3fe 0xf80703030003ff8f

def z617 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x020007fc47007fed 0xbc08001ff11c01ff

def z618 : W := mkw 0x91fe50f850b08730 0x8a47f943e142c21c 0x81ff00fc00f00302 0x0207fc03f003c00c

def z619 : W := mkw 0x3ffff6eb76ec0038 0x0cffffdbaddbb000 0xfffff803fffc003b 0xe7ffffe00ffff000

def z620 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e003f03ff007c21 0x8df800fc0ffc01f0

def z621 : W := mkw 0x3f77a60376ec0038 0x04fdde980ddbb000 0xffffff03fffc003f 0xeffffffc0ffff000

def z622 : W := mkw 0xbffef6f858a11530 0x8afffbdbe1628454 0xfffffffc78001c07 0xeffffffff1e00070

def z623 : W := mkw 0xaeacc4b27cb19730 0x82bab312c9f2c65c 0xbfbcc4b3fff39f3f 0xf6fef312cfffce7c

def z624 : W := mkw 0x0000000000000000 0x0000000000000000 0x006300fc00000002 0x00018c03f0000000

def z625 : W := mkw 0x3bf7408376fc8238 0x04efdd020ddbf208 0xbfffc083ffff833f 0xf6ffff020ffffe0c

def z626 : W := mkw 0xbffec4b37cf99730 0x86fffb12cdf3e65c 0xbdbcc4b3f8f39f1f 0x76f6f312cfe3ce7c

def z627 : W := mkw 0x7fdaffebad5bfa87 0x09ff6bffaeb56fea 0xffffffffffffffff 0xffffffffffffffff

def z628 : W := mkw 0x7ffbfffeef877d6e 0x49ffeffffbbe1df5 0xffffffffff8fffff 0xfffffffffffe3fff

def z629 : W := mkw 0x3bd258c1805ac285 0x00ef496306016b0a 0xfffff8c380ffe3ff 0xfbffffe30e03ff8f

def z630 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0000000047001c00 0x04000000011c0070

def z631 : W := mkw 0x11c059d5815aefc5 0x4047016756056bbf 0x71c0ffff80fffffe 0xf9c703fffe03ffff

def z632 : W := mkw 0x3b52000324480000 0x04ed48000c912000 0x3000000380000000 0x00c000000e000000

def z633 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380738016 0xe9c703e30e01ce00

def z634 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7c00fc03f8039c1d 0x75f003f00fe00e70

def z635 : W := mkw 0x0020011441802d60 0x40008004510600b5 0x002007fc40807fcf 0x3c00801ff10201ff

def z636 : W := mkw 0xee88efb2ad13ff06 0x83ba23becab44ffc 0x7e00ffb3ff03ff3d 0xfdf803fecffc0ffc

def z637 : W := mkw 0x95fed4f858b19730 0x8a57fb53e162c65c 0x8dffc4fc78f39f1f 0x7637ff13f1e3ce7c

def z638 : W := mkw 0xbfffc5b77ffdbf78 0xc6ffff16ddfff6fd 0xbfffc7ffffffffff 0xfeffff1fffffffff

def z639 : W := mkw 0x1156000110680010 0x044558000441a000 0x819c000000700000 0x020670000001c000

def z640 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ff83d2 0x41c703e30e03fe0f

def z641 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc0b038f38312 0x4236f302c0e3ce0c

def z642 : W := mkw 0x11e458c1d0fac2b5 0x004791630743eb0a 0xfdfcf8c3f8ffe3ff 0xfff7f3e30fe3ff8f

def z643 : W := mkw 0x2a00000224000000 0x00a8000008900000 0x3c000003b8000010 0x40f000000ee00000

def z644 : W := mkw 0x3b52000100480000 0x00ed480004012000 0xbfff000380fc003b 0xe2fffc000e03f000

def z645 : W := mkw 0x3f7784037eed1038 0x04fdde100dfbb440 0xbfffc403ffff9c3f 0xf6ffff100ffffe70

def z646 : W := mkw 0x0488fee88012c285 0x081223fba2004b0a 0x4000fffc0003e3c4 0x190003fff0000f8f

def z647 : W := mkw 0x11c050c000000000 0x0047014300000000 0x73e3fffc00000007 0xe9cf8ffff0000000

def z648 : W := mkw 0x0400840008011000 0x0010021000200440 0x0c00c00038038010 0x4030030000e00e00

def z649 : W := mkw 0x00a141944394af68 0x40028506510e52bd 0x03e3c7fc47ffffff 0xfc0f8f1ff11fffff

def z650 : W := mkw 0xbfdec4a33c799210 0x86ff7b128cf1e648 0xbd9cc003b8738010 0x42f673000ee1ce00

def z651 : W := mkw 0x0000010001002800 0x00000004000400a0 0x026307fc47007c2f 0xbc098c1ff11c01f0

def z652 : W := mkw 0x7b770903ffef783e 0x05eddc240fffbde0 0xbfff0003fffffc3b 0xf6fffc000ffffff0

def z653 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbe7f0003ff0c0021 0x86f9fc000ffc3000

def z654 : W := mkw 0x1161000142cc0028 0x00458400050b3000 0x33e30003c7fc003b 0xe4cf8c000f1ff000

def z655 : W := mkw 0x0024001050a00530 0x0000900041428014 0x8dbc04b078f01f1f 0x7636f012c1e3c07c

def z656 : W := mkw 0x3b523a49804a4085 0x08ed48e926012902 0x72433b4f800c60e0 0x89c90ced3e003183

def z657 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc08038f3831e 0x7236730200e3ce0c

def z658 : W := mkw 0x2e3ba73c43842d68 0x48b8ee9cf10e10b5 0x8e3f073c47001c01 0x0638fc1cf11c0070

def z659 : W := mkw 0x0020001040800520 0x0000800041020014 0x002000b000800302 0x00008002c002000c

def z660 : W := mkw 0x008058c08012c285 0x0002016302004b0a 0x7000f8c38003e3fc 0xf9c003e30e000f8f

def z661 : W := mkw 0x11e150d542dc87e9 0x40478543550b721f 0x01e300fc00fc03c2 0x00078c03f003f00f

def z662 : W := mkw 0x0021001442840568 0x40008400510a1015 0x026307fc008c03c7 0xa8098c1ff002300f

def z663 : W := mkw 0x11401841804a4085 0x0045006106012902 0x704038c3808c63ee 0xb9c100e30e02318f

def z664 : W := mkw 0x3bda50e800000000 0x08ef6943a0000000 0xbfff00fc00000003 0xe2fffc03f0000000

def z665 : W := mkw 0x4400ae0088035006 0x011002b802200d40 0x4000f80000038000 0x010003e000000e00

def z666 : W := mkw 0x3ffbf6fc42840568 0x48ffefdbf10a1015 0xfffffffc008c03c7 0xebfffffff002300f

def z667 : W := mkw 0x2e88e6a000000000 0x00ba239a80000000 0xffbcffb000000007 0xebfef3fec0000000

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000008c63e8 0x100000000002318f

def z669 : W := mkw 0x00a0409040908720 0x000281024102421c 0x01a0c4b040f39f1f 0x74068312c103ce7c

def z670 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026303fc078c63e2 0x88098c0ff01e318f

def z671 : W := mkw 0x6a00230225002802 0x01a8008c089400a0 0x0200030007000000 0x0008000c001c0000

def z672 : W := mkw 0x80ac40b050b08730 0x8202b102c142c21c 0x81bcc0b000f3831e 0x7206f302c003ce0c

def z673 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8c3cc4b078039f05 0x1630f312c1e00e7c

def z674 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000047000029 0xa4080000011c0000

def z675 : W := mkw 0x3bd658c3b47ac295 0x04ef59630ed1eb0a 0xfddcf8c3b8ffe3fe 0xfbf773e30ee3ff8f

def z676 : W := mkw 0x11da50e800000000 0x08476943a0000000 0x819c000000000000 0x0206700000000000

def z677 : W := mkw 0x7f52af02ad037806 0x01fd4abc0ab40de0 0xffffff03ff03fc3f 0xfffffffc0ffc0ff0

def z678 : W := mkw 0x3b530003264c0008 0x04ed4c000c993000 0x33c3000387fc003a 0xe0cf0c000e1ff000

def z679 : W := mkw 0x0020011041802d20 0x00008004410600b4 0x022007b047807f2f 0xbc08801ec11e01fc

def z680 : W := mkw 0x11da50e800000000 0x08476943a0000000 0x83ff07fc00000007 0xaa0ffc1ff0000000

def z681 : W := mkw 0x04a9f7fc43842d68 0x4812a7dff10e10b5 0x4263fffc478c7fef 0xbd098ffff11e31ff

def z682 : W := mkw 0x3fdbf6eb264c0008 0x0cff6fdbac993000 0xffffffff870c0027 0xebfffffffe1c3000

def z683 : W := mkw 0x0488f6e800000000 0x081223dba0000000 0x4263fffc00000007 0xa9098ffff0000000

def z684 : W := mkw 0x84acccb0d8b3d734 0x8212b332c362cf5c 0xfdbcfcb3f8f3ff3f 0xfff6f3f2cfe3cffc

def z685 : W := mkw 0x7fdaffeaad037806 0x09ff6bffaab40de0 0xff9cff03ff03fc3d 0xfffe73fc0ffc0ff0

def z686 : W := mkw 0x15dad4e800000000 0x08576b53a0000000 0x8dffc4fc00000007 0x6237ff13f0000000

def z687 : W := mkw 0x6e21af02ef87782e 0x01b886bc0bbe1de0 0x7e63ff03ff8ffc3f 0xfdf98ffc0ffe3ff0

def z688 : W := mkw 0x8024001058b19730 0x820090004162c65c 0x002004b078f39f1f 0x34008012c1e3ce7c

def z689 : W := mkw 0x6e21a7166f853d6a 0x41b8869c59be14f5 0x0e23073c7f001c01 0x04388c1cf1fc0070

def z690 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f8038073e03c 0xf9c603e00e01cf80

def z691 : W := mkw 0x0020001040800520 0x0000800041020014 0x006004f0408c7fef 0xbc018013c10231ff

def z692 : W := mkw 0x0021000042840028 0x00008400010a1000 0x026307fc478c002f 0xac098c1ff11e3000

def z693 : W := mkw 0x6e00a6022c011002 0x01b8029808b00440 0x0c00000038000000 0x0030000000e00000

def z694 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x0000073c00001c00 0x0000001cf0000070

def z695 : W := mkw 0x0004000010200010 0x0000100000408000 0x8d9c000038700010 0x4236700000e1c000

def z696 : W := mkw 0x15c8fee9805ac285 0x085723fba6016b0a 0x71c0ffff80ffe3fe 0xf9c703fffe03ff8f

def z697 : W := mkw 0x2e3ba73c43842d68 0x48b8ee9cf10e10b5 0x8e7f07fc478c7fef 0xbe39fc1ff11e31ff

def z698 : W := mkw 0x6e00af02a5026806 0x01b802bc0a9409a0 0x7e00ff0387006025 0xe9f803fc0e1c0180

def z699 : W := mkw 0x95ecdcf1d8fbd7b5 0x8257b373c763ef5e 0xfdbcfcb3f8f39f1f 0x77f6f3f2cfe3ce7c

def z700 : W := mkw 0xeeace7b27db1bf32 0x83bab39ec9f6c6fc 0x8fbcc7b07ff39f1f 0x763ef31ec1ffce7c

def z701 : W := mkw 0x11411945834e68cd 0x40450465160d39a3 0x72433b4f870c60e0 0x89c90ced3e1c3183

def z702 : W := mkw 0x84adc5b45bb5bf78 0xc212b716d16ed6fd 0x8fbfc7bc7ff39f1f 0x763eff1ef1ffce7c

def z703 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xff9cff0000000005 0xebfe73fc00000000

def z704 : W := mkw 0x3bd358c3a65ec28d 0x04ef4d630e997b0a 0x73c3f8c387ffe3fe 0xf9cf0fe30e1fff8f

def z705 : W := mkw 0x0000011401002d40 0x40000004500400b5 0x004007fc008c7fee 0xb801001ff00231ff

def z706 : W := mkw 0xffecfff3fdfbffb7 0x83ffb3ffcff7effe 0xfffcfff3ffffffff 0xfffff3ffcfffffff

def z707 : W := mkw 0x11c858e9805ac285 0x08472163a6016b0a 0x71c0f8ff80ffe3fe 0xf9c703e3fe03ff8f

def z708 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbd9c0003ff700038 0x46f670000ffdc000

def z709 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0xfe3fff3c00000001 0x43f8fffcf0000000

def z710 : W := mkw 0x11e159d5c3deefed 0x40478567570f7bbf 0x73a3ff3fc7739c11 0x45ce8ffcff1dce70

def z711 : W := mkw 0x848dc5a41b35ba58 0xc2123716906cd6e9 0x8fdfc34c3f7fe0f0 0xca3f7f0d30fdff83

def z712 : W := mkw 0x2ab758c2f6b6c2bd 0x04aadd630bdadb0a 0xce3ff8c07f03e3c5 0x1f38ffe301fc0f8f

def z713 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x73c0f8c3c7ffe3ff 0xfdcf03e30f1fff8f

def z714 : W := mkw 0x6e37a7167fa53d7a 0x45b8de9c59fe94f5 0x8e3f073c7f001c01 0x0638fc1cf1fc0070

def z715 : W := mkw 0x3fdaf6e900588281 0x08ff6bdba401620a 0xfffffffc00fc63ef 0xfbfffffff003f18f

def z716 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfbf0003fff0001b 0x66fefc000fffc000

def z717 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc0b078f39f1a 0x5636f302c1e3ce7c

def z718 : W := mkw 0x3fdaf6e800108200 0x08ff6bdba0004208 0xfffffffc00ffe3ff 0xfbfffffff003ff8f

def z719 : W := mkw 0x51da59eaad037806 0x09476967aab40de0 0x81ff00ffff03fc3a 0x1607fc03fffc0ff0

def z720 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8d9cc4b078f39f1c 0x56367312c1e3ce7c

def z721 : W := mkw 0x2a25000376ec0038 0x04a894000ddbb000 0xbfbc0003fffc003b 0xe6fef0000ffff000

def z722 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff00b3fffc033b 0xe6fffc02cffff00c

def z723 : W := mkw 0x04adf6eb76ec0038 0x0c12b7dbaddbb000 0x4000fffffffc003c 0x0d0003fffffff000

def z724 : W := mkw 0x84ace6b058b19730 0x8212b39ac162c65c 0xcdbcffb078f39f1f 0x7f36f3fec1e3ce7c

def z725 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbf9c0003ff700011 0x46fe70000ffdc000

def z726 : W := mkw 0x7b530903a74e680e 0x05ed4c240e9d39a0 0x32430003870c6020 0x80c90c000e1c3180

def z727 : W := mkw 0xbb76325858b19730 0x8aedd8c96162c65c 0x72433b4c78f39f18 0x9dc90ced31e3ce7c

def z728 : W := mkw 0x3b56011735682d50 0x44ed58045cd5a0b5 0xbd9c07ffb8707fd4 0x5af6701ffee1c1ff

def z729 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc00f0001f 0xebfffffff003c000

def z730 : W := mkw 0x3f52a60000000000 0x00fd4a9800000000 0xfffffffc00000007 0xebfffffff0000000

def z731 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff8ffffd 0xfdf803fc0ffe3fff

def z732 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff00c3fffc03fb 0xe6fffc030ffff00f

def z733 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff04b3fffc003f 0xe6fffc12cffff000

def z734 : W := mkw 0x0001011403042d48 0x40000404500c10b5 0x024307fc078c7fee 0xb8090c1ff01e31ff

def z735 : W := mkw 0x008058c1805ac285 0x0002016306016b0a 0x7000f8c380ffe3fc 0xf9c003e30e03ff8f

def z736 : W := mkw 0x3bda72e800000000 0x08ef69cba0000000 0xffff3bfc00000003 0xebfffceff0000000

def z737 : W := mkw 0x6e21ae16ee87556e 0x41b886b85bba1d55 0x7c63f8ffb88f83d2 0x41f18fe3fee23e0f

def z738 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8d9cc00078739c10 0x4636730001e1ce70

def z739 : W := mkw 0x04008d0089037804 0x0010023402240de0 0x7e00ff03ff03fc3d 0xfdf803fc0ffc0ff0

def z740 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x73c3fbcf80ffe3fe 0xf9cf0fef3e03ff8f

def z741 : W := mkw 0x2a25000276a40038 0x00a8940009da9000 0xbfff0003fffc003b 0xe6fffc000ffff000

def z742 : W := mkw 0x956c9c71d8eb55b5 0x8255b271c763ad56 0xfc7c3c73f80c7ce1 0x8ff1f0f1cfe031f3

def z743 : W := mkw 0x11d258c9805ac285 0x0847496326016b0a 0x71c3f8cf80ffe3fe 0xf9c70fe33e03ff8f

def z744 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffffff7c00000001 0xcbfffffdf0000000

def z745 : W := mkw 0x91ff50f952fc8738 0x8e47fd43e54bf21c 0x81ff00fc00fc0302 0x0207fc03f003f00c

def z746 : W := mkw 0x11c858e1805ac285 0x0047216386016b0a 0xf1fcf8f380ffe3fe 0xfbc7f3e3ce03ff8f

def z747 : W := mkw 0x2a37000276a40038 0x04a8dc0009da9000 0xbfbf0003fff0003b 0xe6fefc000fffc000

def z748 : W := mkw 0x3fdaf6e808011000 0x08ff6bdba0200440 0xfffffffc78001c07 0xeffffffff1e00070

def z749 : W := mkw 0x842c843058a11530 0x8210b210c1628454 0x8dbcc43078f39c1f 0x7636f310c1e3ce70

def z750 : W := mkw 0x0024000058a11030 0x0000900001628440 0x8dbc000078f39c1b 0x7636f00001e3ce70

def z751 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x73c0ffc380ffe3ff 0xf9cf03ff0e03ff8f

def z752 : W := mkw 0xc0250916ffb7ff7e 0xc30094245bfedffd 0x00000003fffffff8 0x140000000fffffff

def z753 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0043fffc60fb 0xeefffc010ffff183

def z754 : W := mkw 0x2a000902a5026804 0x00a800240a9409a0 0x7e00ff03ff03fc3d 0xfdf803fc0ffc0ff0

def z755 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x7040f8c380ffe3fe 0xf9c103e30e03ff8f

def z756 : W := mkw 0x0488c4a008119200 0x0012231280204648 0x8dbcc4b078f39f1f 0x7636f312c1e3ce7c

def z757 : W := mkw 0x3b77104376ec00b9 0x04eddc410ddbb002 0xbfff0043fffc00fb 0xe6fffc010ffff003

def z758 : W := mkw 0x3f5ab66800000000 0x08fd6ad9a0000000 0xfe7f3ffc00000007 0xabf9fcfff0000000

def z759 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfdf0003fffc0038 0xc6ff7c000ffff000

def z760 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b038f39f16 0x5236f312c0e3ce7c

def z761 : W := mkw 0x1165000376ec0038 0x044594000ddbb000 0xbdfc0003fffc003b 0xe6f7f0000ffff000

def z762 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffff3ffc00000003 0x8bfffcfff0000000

def z763 : W := mkw 0x7fdaf6ea2c011002 0x09ff6bdba8b00440 0xfffffffc38000007 0xebfffffff0e00000

def z764 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff0003fffc1f3b 0xf6fffc000ffff07c

def z765 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbfdf0003ff7c0039 0xe6ff7c000ffdf000

def z766 : W := mkw 0xeaac6bb2f5b2ef36 0x83aab1aecbd6cbbc 0xf3bc3bb387f06322 0x8bcef0eece1fc18c

def z767 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078f39f07 0x1636f312c1e3ce7c

def z768 : W := mkw 0x3b77220376ec0038 0x04eddc880ddbb000 0xffff3b03fffc003b 0xeffffcec0ffff000

def z769 : W := mkw 0x2e1aae29805ac285 0x08b86ab8a6016b0a 0x8e3f073f80ffe3f9 0x1238fc1cfe03ff8f

def z770 : W := mkw 0xc488fff08913ff87 0x831223ffc2244ffe 0x4000fff00003ffc4 0x190003ffc0000fff

def z771 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ffffff03fc3d 0xfdf803fffffc0ff0

def z772 : W := mkw 0xbfdbc4b32e5d9708 0x86ff6f12ccb9765c 0x3243c4b3870f9f24 0x90c90f12ce1c3e7c

def z773 : W := mkw 0x3fdaf6e900588281 0x08ff6bdba401620a 0xfffffffc00ff83df 0xfbfffffff003fe0f

def z774 : W := mkw 0x3fdaf6e808011000 0x08ff6bdba0200440 0xfffffffc38038017 0xebfffffff0e00e00

def z775 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc43078739c1d 0x7636f310c1e1ce70

def z776 : W := mkw 0xc488efb48913ff46 0xc31223bed2244ffd 0x4000fffc0003ffc4 0x190003fff0000fff

def z777 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0403fffc1c3f 0xf6fffc100ffff070

def z778 : W := mkw 0x84acd4f858b19730 0x8a12b353e162c65c 0x8dbcc4fc78f39f1f 0x7636f313f1e3ce7c

def z779 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71e3f8ff80ffe3fe 0xf9c78fe3fe03ff8f

def z780 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc470c7fe5 0x9c098c1ff11c31ff

def z781 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003fffc0023 0x86fffc000ffff000

def z782 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x8fff07fc478c7fef 0xfe3ffc1ff11e31ff

def z783 : W := mkw 0x7fc0f7c32d59ba83 0x01ff03df0cb566ea 0x0fc007c07ffc1fc3 0x043f001f01fff07f

def z784 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc43078f39f19 0x5636f310c1e3ce7c

def z785 : W := mkw 0x84acd4f058b19730 0x8212b353c162c65c 0xcdbcfcf078f39f1f 0x7f36f3f3c1e3ce7c

def z786 : W := mkw 0x3fdaf6e808011000 0x08ff6bdba0200440 0xfffffffc00039c07 0xfbfffffff0000e70

def z787 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff03fc39 0x55f803fc0ffc0ff0

def z788 : W := mkw 0xbfdaf6e808119200 0x8aff6bdba0204648 0xfffffffc00038007 0xebfffffff0000e00

def z789 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc43078f39c1b 0x6636f310c1e3ce70

def z790 : W := mkw 0x84acf6f858b19730 0x8a12b3dbe162c65c 0xcffffffc78f39f1f 0xff3ffffff1e3ce7c

def z791 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e20ffb3ff03fc3f 0xfdf883fecffc0ff0

def z792 : W := mkw 0x15daf6e800000000 0x08576bdba0000000 0xf1fffffc00000006 0xebc7fffff0000000

def z793 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71e0fcf380ffe3ff 0xf9c783f3ce03ff8f

def z794 : W := mkw 0x3b77324b76ec0038 0x0ceddcc92ddbb000 0xffff3803fffc003b 0xe7fffce00ffff000

def z795 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff03fc31 0xcdf803fc0ffc0ff0

def z796 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff039c1d 0x75f803fc0ffc0e70

def z797 : W := mkw 0x11da72e800000000 0x084769cba0000000 0xc1ff3bfc00000002 0x0b07fceff0000000

def z798 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00fb03ff03fc38 0xddf803ec0ffc0ff0

def z799 : W := mkw 0x3bda72e800000000 0x08ef69cba0000000 0xf3ff3ffc00000007 0xabcffcfff0000000

def z800 : W := mkw 0x3fdaf6e800108200 0x08ff6bdba0004208 0xfffffffc00038307 0xfbfffffff0000e0c

def z801 : W := mkw 0x0025011453a42d78 0x40009404514e90b5 0x83ff07fc47fc7fef 0xbe0ffc1ff11ff1ff

def z802 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4f078f3ffdf 0x7e36f313c1e3cfff

def z803 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff039c15 0xedf803fc0ffc0e70

def z804 : W := mkw 0xc488efa08913fa06 0x831223be82244fe8 0x4000ff000003fc04 0x190003fc00000ff0

def z805 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbdbc0003fffc003b 0x66f6f0000ffff000

def z806 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc00078739c18 0x5636730001e1ce70

def z807 : W := mkw 0x3fdaf6eb24480000 0x0cff6bdbac912000 0xffffffff80000007 0xebfffffffe000000

def z808 : W := mkw 0x3b77104376ec0038 0x04eddc410ddbb000 0xffff3843fffc003b 0xeffffce10ffff000

def z809 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0xfe3f3f3c00000001 0x8bf8fcfcf0000000

def z810 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff0433fffc1c3b 0xe6fffc10cffff070

def z811 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbfdc0003fffc003b 0xe6ff70000ffff000

def z812 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00fc03ff03fc3d 0x75f003f00ffc0ff0

def z813 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbfff0003ff70003b 0xe6fffc000ffdc000

def z814 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff00fffffc003b 0xe6fffc03fffff000

def z815 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dfcc4f078f39f1f 0xfe37f313c1e3ce7c

def z816 : W := mkw 0x3fdaf6e800108200 0x08ff6bdba0004208 0xfffffffc00738017 0xebfffffff001ce00

def z817 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff073ffffc003b 0xe6fffc1cfffff000

def z818 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x326307ffc78c7fff 0xfcc98c1fff1e31ff

def z819 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff83ff83ff3f 0xfdf803fe0ffe0ffc

def z820 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0xce3fff3c00000005 0x0b38fffcf0000000

def z821 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0263c7fc478fffff 0xfc098f1ff11e3fff

def z822 : W := mkw 0x5577af01dbef783e 0x0555debc076fbde0 0xc1ffff0000fffc06 0x1b07fffc0003fff0

def z823 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8dbfc4bc78f39f1f 0x7636ff12f1e3ce7c

def z824 : W := mkw 0xee2da7367fa53d7a 0xc3b8b69cd9fe94f5 0x8e3f073c7f001c01 0x0638fc1cf1fc0070

def z825 : W := mkw 0x2e9af6e800000000 0x08ba6bdba0000000 0xfe3ffffc00000005 0xebf8fffff0000000

def z826 : W := mkw 0x3fdaf6ea24000000 0x08ff6bdba8900000 0xfffffffc7f000007 0xeffffffff1fc0000

def z827 : W := mkw 0x3fdaf6e900480000 0x08ff6bdba4012000 0xffffffff80700017 0xebfffffffe01c000

def z828 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ffe3d6 0x59c703e30e03ff8f

def z829 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00f803ff039c10 0x45f003e00ffc0e70

def z830 : W := mkw 0x3f5ab66800000000 0x08fd6ad9a0000000 0xffff3f7c00000003 0xebfffcfdf0000000

def z831 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc478c7fe3 0x8c098c1ff11e31ff

def z832 : W := mkw 0x04acc4a058a11030 0x0012b31281628440 0x8dbcc4b078f39c1f 0x7636f312c1e3ce70

def z833 : W := mkw 0x3b56000334680010 0x04ed58000cd1a000 0xbf9c0003bf700030 0xc2fe70000efdc000

def z834 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff00c3fffc003f 0xeefffc030ffff000

def z835 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc40038739c14 0x5236731000e1ce70

def z836 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7040f8c380ffe3fc 0x99c103e30e03ff8f

def z837 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7200ff03ff03fc3c 0x9dc803fc0ffc0ff0

def z838 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbfdf0003bffc003a 0xe2ff7c000efff000

def z839 : W := mkw 0x7b533b43a74e688f 0x05ed4ced0e9d39a2 0x72433b43870c60e0 0x89c90ced0e1c3183

def z840 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e63ffffff8fffff 0xfdf98ffffffe3fff

def z841 : W := mkw 0x3fdaf6e900588200 0x08ff6bdba4016208 0xffffffff80ff833f 0xfbfffffffe03fe0c

def z842 : W := mkw 0x84acf6f858b19730 0x8a12b3dbe162c65c 0xcdbcfcb078f39f1f 0x7736f3f2c1e3ce7c

def z843 : W := mkw 0x7b532b07a74e684e 0x45ed4cac1e9d39a1 0x72433b4f870c60e0 0x89c90ced3e1c3183

def z844 : W := mkw 0x6e12af02ad037806 0x01b84abc0ab40de0 0xfe3fff03ff03fc3d 0xfff8fffc0ffc0ff0

def z845 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffbffffc00000005 0x4bfefffff0000000

def z846 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffbfff3c00000005 0xebfefffcf0000000

def z847 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc000c60e7 0xebfffffff0003183

def z848 : W := mkw 0x3bd250c000000000 0x00ef494300000000 0xfffffffc00000007 0xebfffffff0000000

def z849 : W := mkw 0x3fdaf6e800108281 0x08ff6bdba000420a 0xfffffffc000003c7 0xebfffffff000000f

def z850 : W := mkw 0x0000010001002800 0x00000004000400a0 0x026307fc478c7fef 0xbc098c1ff11e31ff

def z851 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff07fffffc1f3f 0xfefffc1ffffff07c

def z852 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff04fffffc1fff 0xf6fffc13fffff07f

def z853 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e40ffc3ff03fc3f 0xfdf903ff0ffc0ff0

def z854 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003ff7c0031 0xc6fffc000ffdf000

def z855 : W := mkw 0x2e9af6e800000000 0x08ba6bdba0000000 0xce7ffffc00000007 0xab39fffff0000000

def z856 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc48078f39f1f 0x7636731201e3ce7c

def z857 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x024307fc478c7fec 0x9c090c1ff11e31ff

def z858 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e40ff03ff8ffc3f 0xfdf903fc0ffe3ff0

def z859 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbf9f0003bf700010 0x42fe7c000efdc000

def z860 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f84380ffe3f8 0xd9c703e10e03ff8f

def z861 : W := mkw 0x3ffbf7fc43842d68 0x48ffefdff10e10b5 0xfd9cf800478c7fe8 0x57f673e0011e31ff

def z862 : W := mkw 0x0025011453a42d78 0x40009404514e90b5 0x8e7f07fc7f8c7fef 0xbe39fc1ff1fe31ff

def z863 : W := mkw 0xc488fff88913ff06 0x8b1223ffe2244ffc 0x4000fffc0003ff04 0x190003fff0000ffc

def z864 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc008c002f 0xebfffffff0023000

def z865 : W := mkw 0x3fdaf6eb24480000 0x08ff6bdbac912000 0xfffffffffffc003f 0xeffffffffffff000

def z866 : W := mkw 0x3b77324b76ec0038 0x0ceddcc92ddbb000 0xffff3ffffffc003f 0xeffffcfffffff000

def z867 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbddc0003fffc003a 0xe6f770000ffff000

def z868 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003fffc63fb 0xf6fffc000ffff18f

def z869 : W := mkw 0x0025011453a42d78 0x40009404514e90b5 0x026307fc7ffc7fff 0xbc098c1ff1fff1ff

def z870 : W := mkw 0x15c8d4e000000000 0x0057235380000000 0xfffffffc00000007 0xebfffffff0000000

def z871 : W := mkw 0x8024001058b19730 0x820090004162c65c 0x8d9c000078f39f18 0x5636700001e3ce7c

def z872 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e43ff4fff03fc3d 0xfdf90ffd3ffc0ff0

def z873 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0fcc3c0ffffff 0xfdc703f30f03ffff

def z874 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8fffc7fc78ff9fdf 0xfe3fff1ff1e3fe7f

def z875 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8d9cc4b038f39f1e 0x72367312c0e3ce7c

def z876 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f80380ffe3fc 0xf9c603e00e03ff8f

def z877 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff03fc25 0x9df803fc0ffc0ff0

def z878 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc0003801f 0xfbfffffff0000e00

def z879 : W := mkw 0x00804881805ac285 0x0002012206016b0a 0x7180f88380ffe3fe 0xf9c603e20e03ff8f

def z880 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x03e307fc47fc7fff 0xfc0f8c1ff11ff1ff

def z881 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffbfc00000002 0xcbffffeff0000000

def z882 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc478c7fc7 0x1c098c1ff11e31ff

def z883 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8d9cc40078739c11 0x4636731001e1ce70

def z884 : W := mkw 0x11401841805ac285 0x0045006106016b0a 0x7040f84380ffe3fc 0xf9c103e10e03ff8f

def z885 : W := mkw 0x1165000152ec0038 0x00459400054bb000 0xbfff0003fffc003b 0xe6fffc000ffff000

def z886 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e63ff03ff03fc3f 0xfdf98ffc0ffc0ff0

def z887 : W := mkw 0x7b522b03a54a6806 0x05ed48ac0e9529a0 0x72003b0387006020 0x89c800ec0e1c0180

def z888 : W := mkw 0x4488ffe88913fa87 0x091223ffa2244fea 0x4000fffc0003ffc4 0x190003fff0000fff

def z889 : W := mkw 0x3b531947a74e68cd 0x44ed4c651e9d39a3 0x72433b4f870c60e0 0x89c90ced3e1c3183

def z890 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8d9cc00038739f10 0x5236730000e1ce7c

def z891 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbd9c0003ff700010 0x46f670000ffdc000

def z892 : W := mkw 0x2e9ae6a800000000 0x08ba6b9aa0000000 0xffbfffbc00000007 0xebfefffef0000000

def z893 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfdfffffc00000006 0x4bf7fffff0000000

def z894 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078739f15 0x5636f312c1e1ce7c

def z895 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003ff700013 0xe6fffc000ffdc000

def z896 : W := mkw 0x3fdaf6ea24000000 0x08ff6bdba8900000 0xffffffff87000027 0xebfffffffe1c0000

def z897 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc008c03c7 0xebfffffff002300f

def z898 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbdff0003fffc003a 0x46f7fc000ffff000

def z899 : W := mkw 0x3b77220b76ec0038 0x0ceddc882ddbb000 0xbfff030ffffc003b 0xe6fffc0c3ffff000

def z900 : W := mkw 0x3fdaf6e900588281 0x08ff6bdba401620a 0xffffffff80fc03ff 0xebfffffffe03f00f

def z901 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078739c17 0x6636f312c1e1ce70

def z902 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e23ff3fff03fc3d 0xfdf88ffcfffc0ff0

def z903 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff003ffffc003b 0xe6fffc00fffff000

def z904 : W := mkw 0x6e00af06ad037846 0x41b802bc1ab40de1 0x7e00ff4fff03fcfd 0xfdf803fd3ffc0ff3

def z905 : W := mkw 0x3fdaf6ea24000000 0x08ff6bdba8900000 0xffffffffb8000017 0xebfffffffee00000

def z906 : W := mkw 0x2a04000234200010 0x00a8100008d08000 0xbf9c0003ff700039 0xe6fe70000ffdc000

def z907 : W := mkw 0x3fdaf6e800108200 0x08ff6bdba0004208 0xfffffffc00f00307 0xebfffffff003c00c

def z908 : W := mkw 0x3fdaf6e900480081 0x08ff6bdba4012002 0xfffffffc000c00c7 0xebfffffff0003003

def z909 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00f803ff03fc3c 0xfdf003e00ffc0ff0

def z910 : W := mkw 0x3fdaf6e900588281 0x08ff6bdba401620a 0xfffffffc00700007 0xebfffffff001c000

def z911 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fbcc4b07ff39f3f 0xf63ef312c1ffce7c

def z912 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f8c380ffe3fc 0x59c603e30e03ff8f

def z913 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078f39f13 0x4636f312c1e3ce7c

def z914 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff034ffffc003b 0xeefffc0d3ffff000

def z915 : W := mkw 0x3b77000776ec0078 0x44eddc001ddbb001 0xbfff004ffffc00fb 0xe6fffc013ffff003

def z916 : W := mkw 0x44008d02ad037806 0x011002340ab40de0 0x7c00fc03ff03fc3d 0xfdf003f00ffc0ff0

def z917 : W := mkw 0x6e08af22ad037806 0x01b822bc8ab40de0 0xfe3cff33ff03fc3d 0xfff8f3fccffc0ff0

def z918 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8d9cc43038739c10 0x42367310c0e1ce70

def z919 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8dffc4b078ff9f1f 0x7637ff12c1e3fe7c

def z920 : W := mkw 0x049af6e800000000 0x08126bdba0000000 0xc03ffffc00000004 0x0b00fffff0000000

def z921 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fffc7fc78ffffff 0xfe3fff1ff1e3ffff

def z922 : W := mkw 0x3bda72e800000000 0x08ef69cba0000000 0xf3fffbfc00000006 0xebcfffeff0000000

def z923 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8fbfc4b07ff39f1f 0x763eff12c1ffce7c

def z924 : W := mkw 0x6a000902ad037806 0x01a800240ab40de0 0x7e00f803ff03fc3d 0xfdf803e00ffc0ff0

def z925 : W := mkw 0x0001011403042d48 0x40000404500c10b5 0x024307fc470c7fed 0xbc090c1ff11c31ff

def z926 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003fffc0013 0x46fffc000ffff000

def z927 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff0003fffc03fb 0xe6fffc000ffff00f

def z928 : W := mkw 0x7b523b4ba54a6887 0x09ed48ed2e9529a2 0x72433b4f870c60e0 0x89c90ced3e1c3183

def z929 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8fffc7fc7fff9f3f 0xfe3fff1ff1fffe7c

def z930 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7180f88380ffe3fe 0x71c603e20e03ff8f

def z931 : W := mkw 0x0024000274a00030 0x0000900009d28000 0x8dbc0003fff0003b 0x6636f0000fffc000

def z932 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc0000602f 0xfbfffffff0000180

def z933 : W := mkw 0x6e12af0aad037806 0x09b84abc2ab40de0 0x7e03ff0fff03fc3d 0xfdf80ffc3ffc0ff0

def z934 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfffc003ffff803f 0xf6ffff000ffffe00

def z935 : W := mkw 0x00000801805ac285 0x0000002006016b0a 0x7000f80380ffe3f8 0x51c003e00e03ff8f

def z936 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fbcc7b078f39f1f 0xfe3ef31ec1e3ce7c

def z937 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0703fffc003f 0xeefffc1c0ffff000

def z938 : W := mkw 0x11da58e9805ac285 0x08476963a6016b0a 0xf3ffffff80ffe3ff 0xfbcffffffe03ff8f

def z939 : W := mkw 0x0025000376ec0038 0x040094000ddbb000 0x8d9c0003fffc0038 0x463670000ffff000

def z940 : W := mkw 0x3b77104b76ec0038 0x0ceddc412ddbb000 0xbfff004ffffc003b 0xe6fffc013ffff000

def z941 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x73e3f8c380ffe3ff 0xf9cf8fe30e03ff8f

def z942 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003bffc0032 0xc2fffc000efff000

def z943 : W := mkw 0x04a4c48058b19230 0x001293120162c648 0x8dbcc48078f39f1f 0x7636f31201e3ce7c

def z944 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ffe3e6 0x99c703e30e03ff8f

def z945 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fffc4b078f39f1f 0xf63fff12c1e3ce7c

def z946 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc4700002f 0xeffffffff11c0000

def z947 : W := mkw 0x7b533b4ba74e680e 0x0ded4ced2e9d39a0 0x72433b4f870c6020 0x89c90ced3e1c3180

def z948 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbd9c0003bf7c0030 0x42f670000efdf000

def z949 : W := mkw 0x1177000376ec0038 0x0445dc000ddbb000 0x8dff0003fffc003b 0x6637fc000ffff000

def z950 : W := mkw 0x6e1aaf2aad037806 0x09b86abcaab40de0 0xfe1cff03ff03fc3d 0xfff873fc0ffc0ff0

def z951 : W := mkw 0x3b570003366c0018 0x04ed5c000cd9b000 0xbfff0003bf7c0033 0xe2fffc000efdf000

def z952 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc7800001f 0xeffffffff1e00000

def z953 : W := mkw 0x2e1ab66800000000 0x08b86ad9a0000000 0xce3f3f7c00000001 0x0b38fcfdf0000000

def z954 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8dbcc4b078ff9fdf 0x7636f312c1e3fe7f

def z955 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xfffff803fffc003f 0xefffffe00ffff000

def z956 : W := mkw 0x3f5aa62800000000 0x08fd6a98a0000000 0xffffff3c00000007 0xebfffffcf0000000

def z957 : W := mkw 0x4400af02ad037806 0x011002bc0ab40de0 0x7000ff03ff03fc3c 0xfdc003fc0ffc0ff0

def z958 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ffe3f2 0xc9c703e30e03ff8f

def z959 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc40001c0f 0xfffffffff1000070

def z960 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xf3fffffc00000006 0x8bcffffff0000000

def z961 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8fffc4fc7fff9fff 0xf63fff13f1fffe7f

def z962 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0ffff80ffe3fe 0xf9c703fffe03ff8f

def z963 : W := mkw 0x84acc4b458b19770 0xc212b312d162c65d 0x8dbcc4fc78f39fdf 0x7636f313f1e3ce7f

def z964 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0xfdbcfcb078f39f1f 0xfff6f3f2c1e3ce7c

def z965 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc000063c7 0xfbfffffff000018f

def z966 : W := mkw 0x0424841058a11530 0x0010921041628454 0x8dbcc4b078f39f1f 0x7636f312c1e3ce7c

def z967 : W := mkw 0x3fdaf6e900480000 0x08ff6bdba4012000 0xfffffffc00fc0007 0xebfffffff003f000

def z968 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff03fc15 0x5df803fc0ffc0ff0

def z969 : W := mkw 0x40250917ffef7d7e 0x450094245fffbdf5 0x00000003fffffff8 0x140000000fffffff

def z970 : W := mkw 0x15daf6e800000000 0x08576bdba0000000 0xc3fffffc00000007 0xab0ffffff0000000

def z971 : W := mkw 0x3b77001376ec0538 0x04eddc004ddbb014 0xbfff04f3fffc7fff 0xfefffc13cffff1ff

def z972 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x0e6307fc7f8c7fff 0xfc398c1ff1fe31ff

def z973 : W := mkw 0x2e1aa62800000000 0x08b86a98a0000000 0xfe7ffffc00000007 0xebf9fffff0000000

def z974 : W := mkw 0x0025000376ec0038 0x040094000ddbb000 0x8fff0003fffc003b 0xe63ffc000ffff000

def z975 : W := mkw 0x40000902ad037806 0x010000240ab40de0 0x7200ff03ff03fc3d 0xfdc803fc0ffc0ff0

def z976 : W := mkw 0x8488ddf48913ffc5 0xc2122377d2244fff 0x4000fffc0003ffc4 0x190003fff0000fff

def z977 : W := mkw 0x848cc4a018319210 0x821233128060c648 0x8dbcc4b078739c1f 0x7636f312c1e1ce70

def z978 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x7dc0f8c3f8ffe3ff 0xfdf703e30fe3ff8f

def z979 : W := mkw 0x3f5ab66800000000 0x08fd6ad9a0000000 0xfe3f3f3c00000001 0x03f8fcfcf0000000

def z980 : W := mkw 0x3fdaf6ea2c011000 0x08ff6bdba8b00440 0xffffffffff039c3f 0xfffffffffffc0e70

def z981 : W := mkw 0x80250915dbfffffd 0xc2009424576fffff 0x00000003fffffff8 0x140000000fffffff

def z982 : W := mkw 0x84acc4a058b19230 0x8212b3128162c648 0x8dbcc40078f39c1f 0x7636f31001e3ce70

def z983 : W := mkw 0x2a37000376ec0038 0x04a8dc000ddbb000 0x8fbf0003fffc003b 0x663efc000ffff000

def z984 : W := mkw 0x3fdaf6e808119200 0x08ff6bdba0204648 0xfffffffc78f39f1f 0xfffffffff1e3ce7c

def z985 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f80380ffe3fa 0xf1c703e00e03ff8f

def z986 : W := mkw 0x3fdaf6e900480000 0x08ff6bdba4012000 0xffffffff800c0027 0xebfffffffe003000

def z987 : W := mkw 0x3b76000274a00030 0x00edd80009d28000 0xbfff0003fff0003b 0xe6fffc000fffc000

def z988 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc0080030f 0xfbfffffff002000c

def z989 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0x8fff0003fffc003b 0x063ffc000ffff000

def z990 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078ffffff 0x7636f312c1e3ffff

def z991 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0003fffc603f 0xfefffc000ffff180

def z992 : W := mkw 0x11da50e800000000 0x08476943a0000000 0xf3fffffc00000007 0xebcffffff0000000

def z993 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0xfdfcf8c380ffe3ff 0xfbf7f3e30e03ff8f

def z994 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8dbcc4b07fff9f3f 0x7636f312c1fffe7c

def z995 : W := mkw 0x3b52000324480000 0x00ed48000c912000 0xbfff0003fffc003b 0xe6fffc000ffff000

def z996 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ff03ff039c39 0xe5f803fc0ffc0e70

def z997 : W := mkw 0x84ace6b858b19730 0x8a12b39ae162c65c 0x8dbcc7bc78f39f1f 0x7636f31ef1e3ce7c

def z998 : W := mkw 0x11f750d552fc87f9 0x4447dd43554bf21f 0x81ff00fc00fc03c2 0x0207fc03f003f00f

def z999 : W := mkw 0x7fdafeebac5bd287 0x09ff6bfbaeb16f4a 0xfd9cf803b8738010 0x43f673e00ee1ce00

def z1000 : W := mkw 0x6e00ae02ac035006 0x01b802b80ab00d40 0x7e00fc03ff039c3d 0xf5f803f00ffc0e70

def z1001 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dfcc4b078ff9f3f 0xf637f312c1e3fe7c

def z1002 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00ffc3ff03fffd 0xfdf803ff0ffc0fff

def z1003 : W := mkw 0x40000902ad037806 0x010000240ab40de0 0x7000f803ff03fc38 0x55c003e00ffc0ff0

def z1004 : W := mkw 0x11c058c1805ac285 0x0047016306016b0a 0x71c0f8c380ffe3fa 0x51c703e30e03ff8f

def z1005 : W := mkw 0x6e08af2aad037806 0x09b822bcaab40de0 0x7e00ff3fff03fc3d 0xfdf803fcfffc0ff0

def z1006 : W := mkw 0x2e00a6022c011000 0x00b8029808b00440 0x7e00ff03ff039c3d 0xfdf803fc0ffc0e70

def z1007 : W := mkw 0x3f5ab66800000000 0x08fd6ad9a0000000 0xfe7fff7c00000005 0xebf9fffdf0000000

def z1008 : W := mkw 0x3fdaf6e900480000 0x08ff6bdba4012000 0xffffffff80fc63ff 0xfbfffffffe03f18f

def z1009 : W := mkw 0x0404840018211010 0x0010121000608440 0x8d9cc40078739c1d 0x7636731001e1ce70

def z1010 : W := mkw 0x008048808012c204 0x0002012202004b08 0x71c0f8c380ffe3fe 0xf9c703e30e03ff8f

def z1011 : W := mkw 0x91ff50f152fc87b9 0x8647fd43c54bf21e 0x81ff00f000fc03c2 0x0207fc03c003f00f

def z1012 : W := mkw 0x2e008c02ac035004 0x00b802300ab00d40 0x7e00fc03ff03fc3d 0xfdf803f00ffc0ff0

def z1013 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc4b078f3ff3f 0xfe36f312c1e3cffc

def z1014 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x7263fffc478c7fef 0xfdc98ffff11e31ff

def z1015 : W := mkw 0x00250917f7feeffd 0x440094245fdffbbf 0x00000003fffffff8 0x140000000fffffff

def z1016 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xcffffffc00000007 0x0b3ffffff0000000

def z1017 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff07fffffc03ff 0xeefffc1ffffff00f

def z1018 : W := mkw 0x0001011403042d48 0x40000404500c10b5 0x026307fc070c7fe7 0xb8098c1ff01c31ff

def z1019 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfffffffc00000003 0x43fffffff0000000

def z1020 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbf9c0003fffc0039 0xe6fe70000ffff000

def z1021 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffffffff8000003f 0xebfffffffe000000

def z1022 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0xffbcff03ff03fc3f 0xfffef3fc0ffc0ff0

def z1023 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffffff3c00000003 0xe3fffffcf0000000

def z1024 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfbf0003ff700039 0xe6fefc000ffdc000

def z1025 : W := mkw 0x80ac40b058b19730 0x8202b102c162c65c 0x8dbc00b078f39f1b 0x7636f002c1e3ce7c

def z1026 : W := mkw 0xc488cdb08913ff06 0x83122336c2244ffc 0x0000c4b00003ff04 0x10000312c0000ffc

def z1027 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc7fc78f39f1f 0x7e36f31ff1e3ce7c

def z1028 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7c00ff03ff03fc3c 0x5df003fc0ffc0ff0

def z1029 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dffc4fc78f39f1f 0x7637ff13f1e3ce7c

def z1030 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0xbdbcc4b3f8f39f3f 0xf6f6f312cfe3ce7c

def z1031 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8d9cc4b078739f1d 0x76367312c1e1ce7c

def z1032 : W := mkw 0x91ed50f552fc87f9 0xc247b543d54bf21f 0x81ff00fc00fc03c2 0x0207fc03f003f00f

def z1033 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e00f803ff03fc39 0xf5f803e00ffc0ff0

def z1034 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xfe7ffffc00000005 0x8bf9fffff0000000

def z1035 : W := mkw 0x3fdaf6e800000000 0x08ff6bdba0000000 0xffbfffbc00000007 0x63fefffef0000000

def z1036 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbcc00078f39f1b 0x7636f30001e3ce7c

def z1037 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8d9cc40078f39f1d 0x7636731001e3ce7c

def z1038 : W := mkw 0x80a4409058b19730 0x820291024162c65c 0x8dbcc08078f39f1f 0x7636f30201e3ce7c

def z1039 : W := mkw 0x3b5a326800000000 0x08ed68c9a0000000 0xf27f3b7c00000000 0x8bc9fcedf0000000

def z1040 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7f80ff03fff3fc3f 0xfdfe03fc0fffcff0

def z1041 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfbf0003fffc0039 0x46fefc000ffff000

def z1042 : W := mkw 0x2e9af6e800000000 0x08ba6bdba0000000 0xcfbffffc00000007 0x6b3efffff0000000

def z1043 : W := mkw 0x11d258c1805ac285 0x0047496306016b0a 0xf1fff8c380ffe3fe 0xfbc7ffe30e03ff8f

def z1044 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc478c7feb 0x14098c1ff11e31ff

def z1045 : W := mkw 0x6e00af02ad037806 0x01b802bc0ab40de0 0x7e40ff43ff0ffcfd 0xfdf903fd0ffc3ff3

def z1046 : W := mkw 0x11400801804a4004 0x0045002006012900 0x71c0f8c380ffe3fe 0xf9c703e30e03ff8f

def z1047 : W := mkw 0x84acd4f058b197b1 0x8212b353c162c65e 0x8dbcc4f078f39fdf 0x7636f313c1e3ce7f

def z1048 : W := mkw 0x15daf6e800000000 0x08576bdba0000000 0xcdfffffc00000007 0x6b37fffff0000000

def z1049 : W := mkw 0x842c843058b19730 0x8210b210c162c65c 0x8dbc043078f39f1b 0x7636f010c1e3ce7c

def z1050 : W := mkw 0x11400801805ac285 0x0045002006016b0a 0x71c0f80380ffe3fe 0xf9c703e00e03ff8f

def z1051 : W := mkw 0x6a002b02ad037806 0x01a800ac0ab40de0 0x7200fb03ff03fc3c 0xfdc803ec0ffc0ff0

def z1052 : W := mkw 0x0021011443842d68 0x40008404510e10b5 0x026307fc078c7fe6 0x98098c1ff01e31ff

def z1053 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8fbfc7bc78f39f1f 0x763eff1ef1e3ce7c

def z1054 : W := mkw 0x6e1aaf2aad037806 0x09b86abcaab40de0 0xfe7fffffff03fc3f 0xfff9fffffffc0ff0

def z1055 : W := mkw 0x8024001058b19730 0x820090004162c65c 0x8dbc04b078f39f1f 0x7636f012c1e3ce7c

def z1056 : W := mkw 0x2e88e6a000000000 0x00ba239a80000000 0xfffffffc00000007 0xebfffffff0000000

def z1057 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dfcc4f078ff9fdf 0x7637f313c1e3fe7f

def z1058 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8dbc04b078f39f1b 0x1636f012c1e3ce7c

def z1059 : W := mkw 0x3b64000374e80030 0x00ed90000dd3a000 0xbffc0003fffc003b 0xe6fff0000ffff000

def z1060 : W := mkw 0x3b76000374e80030 0x04edd8000dd3a000 0xbfbc0003fff0003b 0xe6fef0000fffc000

def z1061 : W := mkw 0x84adc4b45ab59778 0xc212b712d16ad65d 0x8dffc4fc78ffffff 0xfe37ff13f1e3ffff

def z1062 : W := mkw 0x00a4409050b08730 0x000291024142c21c 0x8dbcc4b078f39f1f 0x7636f312c1e3ce7c

def z1063 : W := mkw 0x3b52324800000000 0x08ed48c920000000 0xffff3ffc00000007 0xebfffcfff0000000

def z1064 : W := mkw 0x3b77001776ec0578 0x44eddc005ddbb015 0xbfff00fffffc63ff 0xfefffc03fffff18f

def z1065 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff0083fffc033f 0xf6fffc020ffff00c

def z1066 : W := mkw 0x0488f6e800000000 0x081223dba0000000 0xcffffffc00000007 0xeb3ffffff0000000

def z1067 : W := mkw 0x84adc4b05ab59738 0x8212b712c16ad65c 0x8fffc4f07fffffff 0xfe3fff13c1ffffff

def z1068 : W := mkw 0x11da58e9805ac285 0x08476963a6016b0a 0xf1dcf8c380ffe3fe 0xfbc773e30e03ff8f

def z1069 : W := mkw 0x2e9af6e800000000 0x08ba6bdba0000000 0xce3fff3c00000001 0x0338fffcf0000000

def z1070 : W := mkw 0x3b77000376ec0038 0x04eddc000ddbb000 0xbfff07fffffc63ff 0xfefffc1ffffff18f

def z1071 : W := mkw 0x8424841058b19730 0x821092104162c65c 0x8dbcc40078f39f1f 0x7636f31001e3ce7c

def z1072 : W := mkw 0x84acc4b058b19730 0x8212b312c162c65c 0x8d9cc08078f39f1e 0x7636730201e3ce7c

def z1073 : W := mkw 0x848cc4b018319710 0x82123312c060c65c 0x8dbcc4b038739f17 0x7236f312c0e1ce7c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z0,z1,z2,z3,z4,z9,z10]),(0,[z0,z1,z2,z3,z4,z5,z11]),(0,[z0,z1,z2,z3,z4,z12,z5])],[(0,[z0,z13,z1,z2,z3,z4,z5]),(0,[z14,z0,z1,z2,z3,z4,z5]),(0,[z0,z15,z1,z2,z3,z4,z5])],[(0,[z16,z0,z2,z3,z17,z4,z5]),(0,[z0,z1,z18,z2,z3,z4,z5]),(1,[z0,z1,z2,z19,z4,z5])],[(0,[z20,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z21])],[(0,[z22,z0,z1,z2,z3,z4,z5]),(0,[z23,z0,z1,z2,z3,z24,z5])],[(0,[z0,z1,z2,z3,z4,z9,z25]),(0,[z0,z26,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z28]),(0,[z0,z29,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z2,z3,z4,z9]),(0,[z0,z1,z31,z2,z3,z4,z5])],[(0,[z0,z32,z1,z2,z3,z4,z5]),(0,[z0,z1,z33,z2,z3,z4,z5]),(0,[z0,z1,z34,z2,z3,z4,z5]),(0,[z0,z1,z2,z35,z3,z4,z5]),(0,[z0,z36,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z17,z5]),(0,[z0,z1,z2,z3,z4,z37,z5]),(0,[z0,z38,z1,z2,z3,z4,z5]),(0,[z0,z1,z39,z2,z4,z5,z40]),(0,[z41,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z43])],[(0,[z0,z1,z44,z3,z45,z4,z5]),(0,[z0,z46,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z47,z5]),(0,[z0,z48,z1,z2,z3,z4,z5]),(0,[z49,z0,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z51,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z3,z4,z5,z54]),(0,[z0,z53,z1,z2,z3,z4,z9]),(0,[z0,z1,z2,z3,z55,z4,z5]),(1,[z0,z1,z2,z3,z42,z43])],[(0,[z0,z56,z1,z2,z3,z4,z5]),(0,[z0,z57,z1,z2,z3,z4,z5]),(0,[z0,z58,z1,z2,z3,z4,z5]),(1,[z0,z1,z59,z3,z4,z5]),(0,[z0,z1,z2,z3,z60,z4,z5]),(0,[z0,z61,z1,z62,z3,z4,z5]),(0,[z0,z1,z2,z3,z63,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z65,z5]),(0,[z0,z1,z2,z3,z4,z66,z5])],[(0,[z0,z1,z2,z44,z3,z4,z5]),(0,[z67,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z68,z5,z69])],[(0,[z0,z1,z70,z71,z3,z4,z5]),(0,[z0,z1,z72,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z25,z54])],[(0,[z73,z0,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z3,z4,z5,z75]),(0,[z0,z1,z2,z3,z76,z4,z5]),(0,[z0,z77,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z78,z4,z79,z5])],[(0,[z80,z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z3,z4,z82,z5]),(0,[z83,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z84,z5]),(0,[z0,z1,z2,z3,z4,z85,z5])],[(0,[z0,z1,z86,z2,z3,z4,z5]),(0,[z0,z1,z87,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z88]),(0,[z0,z1,z2,z3,z89,z4,z5]),(0,[z0,z1,z90,z2,z3,z4,z5]),(0,[z0,z1,z39,z2,z78,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z5])],[(0,[z91,z92,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z93,z4,z5]),(0,[z0,z1,z2,z3,z4,z94,z5]),(0,[z95,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z96,z3,z4,z5]),(0,[z97,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z98,z3,z4,z5]),(0,[z0,z1,z99,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z100])],[(0,[z0,z1,z2,z3,z101,z4,z5]),(0,[z0,z1,z2,z3,z102,z4,z5]),(0,[z0,z103,z1,z2,z3,z4,z5]),(0,[z0,z1,z104,z2,z3,z4,z5]),(0,[z0,z53,z105,z1,z2,z3,z4]),(0,[z0,z1,z2,z106,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z40]),(0,[z0,z107,z1,z2,z3,z4,z5]),(1,[z0,z1,z3,z4,z5,z108])],[(0,[z0,z1,z2,z3,z109,z4,z5]),(0,[z0,z110,z1,z2,z3,z4,z5]),(0,[z0,z111,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z112,z4,z5])],[(0,[z0,z1,z113,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z10]),(0,[z0,z1,z2,z114,z3,z4,z5])],[(0,[z0,z53,z1,z3,z115,z4,z5]),(1,[z0,z1,z116,z2,z4,z9])],[(0,[z117,z0,z1,z2,z3,z4,z118]),(0,[z0,z119,z1,z2,z3,z4,z5]),(0,[z120,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z121,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z122])],[(0,[z0,z1,z2,z3,z4,z5,z123]),(0,[z124,z0,z1,z71,z3,z4,z5]),(0,[z125,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z126,z5])],[(0,[z0,z1,z127,z2,z3,z4,z5]),(1,[z73,z1,z2,z128,z4,z5]),(0,[z0,z129,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z130,z4,z5]),(1,[z131,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z132,z5]),(0,[z0,z1,z2,z133,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z25]),(0,[z0,z1,z2,z3,z4,z134,z5]),(0,[z0,z1,z2,z3,z4,z68,z5]),(0,[z0,z1,z2,z3,z4,z5,z135]),(0,[z0,z1,z2,z3,z4,z136,z5])],[(0,[z16,z0,z137,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z138,z4,z5])],[(0,[z139,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z140,z5]),(0,[z0,z141,z1,z2,z3,z4,z5]),(1,[z0,z53,z1,z3,z4,z54]),(0,[z0,z1,z2,z4,z79,z5,z40])],[(0,[z0,z1,z142,z2,z3,z4,z5]),(0,[z143,z0,z1,z2,z3,z4,z5]),(0,[z0,z144,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z145,z4,z5]),(0,[z0,z1,z2,z3,z4,z146,z5]),(0,[z0,z1,z147,z2,z3,z4,z5])],[(0,[z148,z0,z1,z2,z3,z4,z5]),(1,[z117,z127,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z149,z5]),(1,[z0,z1,z150,z2,z4,z5]),(0,[z0,z151,z1,z2,z3,z4,z5]),(0,[z0,z152,z1,z2,z3,z4,z5])],[(0,[z0,z1,z153,z2,z3,z4,z5]),(0,[z0,z154,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z68,z10]),(0,[z155,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z79,z5])],[(0,[z0,z1,z156,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z157,z5]),(0,[z0,z158,z1,z2,z3,z4,z5])],[(0,[z0,z1,z159,z2,z3,z4,z5]),(0,[z0,z160,z1,z2,z3,z4,z5]),(0,[z0,z152,z1,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z161,z5])]],
   [[],[(0,[z162,z0,z1,z2,z3,z4,z5]),(0,[z0,z163,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z164,z5])],[(0,[z0,z1,z165,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z68,z25]),(0,[z0,z1,z2,z166,z3,z4,z5]),(0,[z167,z0,z1,z2,z3,z4,z5])],[],[(0,[z92,z1,z127,z2,z3,z4,z5]),(0,[z168,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z169,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z170]),(0,[z0,z1,z2,z3,z4,z5,z171])],[(0,[z80,z0,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z172,z3,z4,z5]),(0,[z173,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z174,z5])],[(0,[z0,z61,z1,z175,z2,z4,z5]),(0,[z0,z176,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z177,z3,z4,z5]),(0,[z178,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z91,z0,z127,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z179,z4,z5])],[(0,[z0,z103,z1,z2,z3,z79,z5]),(0,[z0,z1,z2,z3,z4,z5,z180]),(0,[z0,z1,z181,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z182,z4,z5]),(0,[z0,z183,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z184,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z185,z0,z1,z2,z3,z4,z5]),(0,[z0,z186,z1,z2,z3,z4,z5])],[(0,[z187,z0,z1,z2,z3,z4,z5]),(0,[z0,z53,z186,z1,z3,z4,z5]),(0,[z0,z188,z1,z2,z3,z4,z5]),(0,[z189,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z190,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z191,z5]),(0,[z0,z192,z1,z2,z3,z4,z5]),(0,[z193,z0,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z70,z3,z4,z5]),(0,[z0,z39,z194,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z195,z4,z5])],[(0,[z0,z1,z2,z3,z4,z10,z54]),(0,[z0,z1,z196,z2,z3,z4,z5]),(0,[z0,z197,z1,z2,z3,z4,z5])],[(0,[z198,z0,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z199,z2,z4,z5]),(0,[z0,z1,z200,z2,z4,z79,z5]),(0,[z0,z201,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z202,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z82,z84,z5]),(0,[z0,z137,z1,z2,z3,z4,z5]),(0,[z0,z203,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z74]),(0,[z0,z1,z2,z3,z204,z4,z5]),(0,[z0,z1,z2,z3,z17,z24,z5]),(0,[z0,z205,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z206,z4,z5]),(0,[z207,z0,z1,z2,z3,z4,z5])],[(0,[z208,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z209,z5]),(0,[z0,z1,z2,z3,z210,z4,z5]),(1,[z0,z1,z70,z3,z174,z5])],[],[(1,[z0,z1,z2,z3,z4,z211]),(0,[z0,z1,z199,z2,z128,z4,z5]),(0,[z0,z1,z2,z3,z212,z4,z5]),(0,[z0,z1,z39,z2,z3,z78,z5]),(1,[z0,z1,z213,z3,z4,z5])],[(0,[z0,z1,z2,z3,z214,z4,z5]),(0,[z215,z1,z2,z44,z3,z4,z5]),(0,[z73,z0,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z217,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z218,z5])],[(0,[z91,z0,z92,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z219,z5]),(0,[z0,z1,z2,z220,z3,z4,z5]),(0,[z0,z1,z2,z3,z221,z4,z5]),(0,[z0,z1,z2,z3,z4,z222,z5])],[(0,[z73,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z223,z5])],[(0,[z224,z0,z1,z2,z3,z4,z5]),(0,[z0,z127,z2,z3,z130,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z225]),(0,[z226,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z227,z4,z5]),(0,[z0,z1,z2,z3,z228,z4,z5]),(0,[z0,z1,z30,z2,z3,z4,z40])],[(0,[z0,z1,z2,z3,z4,z229,z5]),(0,[z0,z1,z2,z3,z4,z230,z5]),(0,[z231,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z232,z3,z4,z5]),(0,[z0,z233,z1,z70,z3,z4,z5]),(0,[z0,z1,z3,z45,z4,z234,z5])],[(0,[z0,z1,z2,z3,z235,z4,z5]),(0,[z0,z1,z30,z44,z3,z4,z5]),(0,[z0,z236,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z237,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z238])],[(0,[z239,z0,z1,z2,z3,z4,z5]),(0,[z240,z1,z2,z3,z4,z82,z5]),(0,[z0,z1,z241,z2,z3,z4,z5])],[(0,[z0,z1,z2,z242,z3,z4,z5]),(0,[z53,z131,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z234])],[(0,[z0,z1,z216,z2,z3,z4,z5]),(0,[z240,z0,z1,z2,z3,z24,z5]),(0,[z0,z243,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z244]),(0,[z16,z0,z199,z2,z3,z4,z5]),(1,[z0,z1,z2,z145,z4,z5])],[(1,[z0,z1,z245,z3,z4,z5]),(0,[z246,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z175,z2,z3,z4,z5]),(0,[z0,z1,z2,z247,z3,z4,z5]),(0,[z0,z1,z2,z248,z3,z4,z5]),(1,[z249,z0,z2,z3,z4,z5]),(0,[z0,z1,z250,z2,z3,z4,z5])]],
   [[(0,[z251,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z252]),(0,[z0,z253,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z254,z5]),(0,[z0,z1,z255,z2,z3,z4,z5]),(0,[z0,z1,z256,z2,z3,z4,z5]),(0,[z0,z1,z2,z257,z3,z4,z5]),(0,[z0,z258,z1,z2,z3,z4,z5])],[(0,[z0,z152,z2,z3,z4,z5,z69]),(0,[z0,z1,z2,z3,z259,z4,z5]),(0,[z0,z1,z2,z3,z4,z260,z5]),(0,[z0,z1,z2,z3,z4,z261,z5]),(0,[z0,z1,z2,z3,z4,z79,z5])],[(1,[z0,z1,z2,z3,z4,z262]),(0,[z263,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z264,z2,z3,z4,z5]),(0,[z0,z265,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z130,z4,z5]),(0,[z0,z1,z2,z3,z4,z266,z5]),(0,[z0,z1,z2,z3,z267,z4,z5]),(0,[z0,z1,z2,z3,z268,z4,z5])],[(0,[z0,z1,z70,z44,z3,z4,z5]),(0,[z0,z269,z1,z2,z3,z4,z5]),(0,[z0,z270,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z271])],[(1,[z0,z1,z87,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z118,z5]),(1,[z97,z1,z2,z184,z4,z5]),(0,[z0,z1,z2,z3,z4,z25,z40]),(0,[z0,z272,z1,z2,z3,z4,z5]),(1,[z0,z1,z30,z3,z4,z234]),(0,[z0,z1,z213,z2,z3,z4,z5])]],
   [[(0,[z91,z0,z1,z2,z3,z4,z5]),(0,[z273,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z274,z5])],[(0,[z0,z1,z275,z2,z3,z4,z5]),(0,[z0,z103,z2,z3,z17,z4,z5]),(0,[z276,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z277,z3,z4,z5])],[(0,[z0,z1,z2,z3,z45,z4,z5])],[(0,[z0,z278,z1,z2,z3,z4,z5]),(0,[z0,z279,z1,z2,z3,z4,z5])],[(0,[z0,z1,z280,z2,z3,z4,z5]),(0,[z0,z1,z2,z281,z3,z4,z5]),(0,[z0,z1,z2,z3,z282,z4,z5]),(0,[z0,z1,z2,z3,z4,z262,z5])],[(1,[z0,z1,z2,z182,z4,z5]),(0,[z0,z1,z283,z2,z3,z4,z5]),(0,[z0,z1,z284,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z285,z5]),(0,[z0,z105,z1,z2,z3,z4,z43])],[(0,[z0,z1,z2,z3,z4,z286,z5]),(0,[z0,z1,z30,z3,z4,z234,z5])],[(0,[z287,z0,z1,z2,z3,z4,z5]),(0,[z288,z0,z1,z2,z3,z4,z5]),(0,[z73,z0,z1,z2,z3,z289,z5]),(0,[z0,z62,z2,z290,z3,z4,z5]),(0,[z0,z291,z1,z2,z3,z4,z5])]],
   [[(0,[z124,z0,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z292]),(0,[z0,z1,z293,z2,z3,z4,z5]),(0,[z0,z294,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z295,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z296,z4,z5]),(0,[z0,z1,z2,z4,z9,z5,z40])],[(0,[z0,z1,z2,z3,z17,z82,z5]),(0,[z297,z0,z1,z2,z3,z4,z5])],[(0,[z298,z0,z1,z2,z3,z4,z5]),(0,[z0,z299,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z78,z24,z5]),(0,[z0,z1,z70,z2,z212,z4,z5]),(0,[z0,z1,z300,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z3,z4,z40]),(0,[z0,z1,z2,z3,z4,z301,z5])],[(0,[z73,z1,z2,z3,z128,z4,z5]),(0,[z0,z1,z2,z302,z3,z4,z5]),(0,[z303,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z304,z4,z5]),(0,[z0,z1,z305,z2,z3,z4,z5]),(0,[z0,z1,z306,z2,z3,z4,z5]),(1,[z0,z194,z2,z3,z4,z5]),(0,[z0,z105,z1,z2,z3,z4,z5])],[(1,[z27,z0,z2,z3,z84,z5]),(0,[z0,z1,z307,z2,z3,z4,z5]),(1,[z0,z1,z2,z212,z4,z5])],[(0,[z0,z1,z308,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z309,z4,z5]),(0,[z0,z1,z71,z3,z45,z4,z5]),(0,[z0,z1,z310,z2,z3,z4,z5]),(0,[z311,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z312,z5]),(0,[z313,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z200,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z314])]],
   [[(0,[z0,z92,z1,z2,z3,z4,z5]),(0,[z0,z1,z315,z2,z3,z4,z5])],[(0,[z0,z1,z2,z316,z3,z4,z5]),(0,[z317,z1,z2,z3,z4,z5,z10]),(0,[z318,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z199,z2,z78,z4,z5]),(0,[z0,z319,z1,z2,z3,z4,z5]),(0,[z0,z1,z70,z3,z4,z234,z5])],[(0,[z124,z215,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z320]),(0,[z321,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z105,z1,z2,z3,z4,z10]),(0,[z322,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z323,z3,z4,z5]),(0,[z0,z52,z1,z39,z2,z4,z5]),(0,[z0,z1,z2,z3,z324,z4,z5]),(0,[z0,z1,z3,z4,z5,z108,z325]),(0,[z0,z1,z2,z3,z326,z4,z5])],[(0,[z0,z1,z62,z44,z3,z4,z5]),(1,[z215,z1,z2,z3,z4,z25]),(0,[z0,z327,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z328,z5])],[(0,[z1,z2,z44,z3,z4,z5,z10]),(0,[z0,z103,z1,z150,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z329,z5]),(0,[z0,z1,z330,z2,z3,z4,z5]),(0,[z0,z331,z2,z3,z4,z68,z5]),(0,[z0,z332,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z333,z5]),(0,[z0,z2,z3,z130,z17,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z69]),(0,[z0,z1,z2,z3,z334,z4,z5])],[(0,[z0,z1,z71,z2,z3,z4,z5]),(0,[z0,z1,z335,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z336,z5]),(0,[z0,z1,z2,z3,z4,z5,z337])],[(0,[z0,z1,z2,z3,z4,z320,z5]),(0,[z338,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z0,z105,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z5,z339]),(0,[z27,z0,z103,z2,z3,z4,z5])]],
   [[(0,[z117,z0,z1,z2,z3,z4,z211]),(0,[z0,z1,z2,z3,z340,z4,z5]),(0,[z341,z0,z1,z2,z3,z4,z5])],[(0,[z317,z0,z1,z177,z3,z4,z5]),(0,[z0,z1,z342,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z343]),(0,[z0,z1,z2,z3,z344,z4,z5]),(1,[z0,z1,z342,z2,z4,z5]),(0,[z0,z1,z39,z116,z2,z4,z5])],[(0,[z23,z0,z1,z2,z3,z4,z225]),(1,[z0,z1,z2,z172,z4,z5]),(0,[z0,z1,z345,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z82,z79,z5]),(0,[z0,z1,z199,z2,z115,z4,z5])],[(0,[z0,z1,z2,z3,z346,z4,z5]),(0,[z0,z1,z2,z3,z347,z4,z5])],[(1,[z0,z1,z2,z348,z4,z5]),(0,[z0,z1,z349,z2,z3,z4,z5]),(0,[z350,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z351,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z352])],[(0,[z16,z0,z127,z2,z3,z4,z5]),(1,[z0,z152,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z353,z5])]],
   [[(0,[z0,z1,z354,z2,z3,z4,z5]),(0,[z0,z355,z1,z2,z3,z4,z5]),(0,[z0,z1,z356,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z357,z4,z5]),(0,[z0,z1,z2,z3,z358,z4,z5]),(0,[z0,z1,z2,z359,z3,z4,z5]),(0,[z23,z0,z1,z2,z3,z82,z5]),(0,[z0,z1,z2,z3,z4,z5,z360])],[(0,[z0,z1,z361,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z362]),(0,[z0,z105,z1,z2,z363,z4,z5])],[(0,[z0,z364,z1,z2,z3,z4,z5]),(0,[z80,z0,z1,z2,z3,z4,z123]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z0,z1,z2,z3,z365,z4,z5]),(0,[z0,z1,z366,z2,z3,z4,z5]),(0,[z0,z1,z70,z2,z3,z45,z5]),(0,[z0,z367,z1,z2,z3,z4,z5])],[(0,[z117,z0,z1,z245,z3,z4,z5]),(0,[z1,z2,z3,z24,z4,z82,z5]),(0,[z0,z1,z2,z3,z4,z368,z5]),(0,[z0,z1,z2,z3,z4,z369,z5])],[(0,[z0,z370,z1,z2,z3,z4,z5]),(0,[z371,z0,z1,z2,z3,z4,z5]),(0,[z372,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z373,z5]),(0,[z0,z1,z2,z3,z374,z4,z5]),(0,[z0,z1,z375,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z376])],[(0,[z1,z71,z2,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z377,z5]),(0,[z0,z1,z200,z2,z3,z79,z5]),(0,[z0,z1,z2,z3,z378,z4,z5]),(0,[z0,z201,z1,z2,z3,z4,z9])]],
   [[(0,[z0,z1,z2,z3,z379,z4,z5]),(0,[z240,z23,z1,z2,z3,z4,z5]),(1,[z0,z1,z380,z115,z4,z5]),(0,[z0,z233,z1,z2,z3,z45,z5])],[(0,[z0,z1,z2,z3,z381,z4,z5]),(0,[z0,z1,z380,z2,z3,z4,z5]),(0,[z0,z382,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z383])],[(0,[z0,z1,z2,z3,z384,z4,z5]),(1,[z0,z385,z2,z3,z4,z5]),(0,[z0,z386,z1,z2,z3,z4,z5]),(0,[z0,z387,z1,z2,z3,z4,z174]),(1,[z0,z233,z1,z3,z45,z5]),(0,[z0,z1,z2,z3,z4,z388,z5])],[(0,[z0,z1,z2,z3,z289,z4,z5]),(0,[z0,z1,z2,z3,z4,z389,z5]),(0,[z0,z1,z2,z3,z4,z390,z5]),(1,[z0,z1,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z391]),(0,[z0,z1,z116,z2,z4,z79,z5])],[(0,[z0,z1,z392,z2,z3,z4,z5]),(0,[z393,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z394,z2,z3,z4,z5]),(1,[z124,z1,z71,z3,z4,z5]),(0,[z73,z0,z1,z98,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z395,z5]),(0,[z0,z1,z2,z396,z3,z4,z5])],[(0,[z397,z0,z1,z2,z3,z4,z5]),(1,[z0,z159,z2,z3,z4,z5]),(0,[z0,z1,z398,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z157,z5]),(0,[z0,z1,z399,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z400]),(0,[z0,z1,z2,z3,z4,z401,z5]),(1,[z0,z331,z2,z3,z4,z68]),(0,[z0,z1,z39,z2,z3,z79,z5]),(0,[z0,z402,z1,z2,z3,z4,z5])],[(0,[z0,z61,z1,z2,z3,z4,z5]),(0,[z0,z403,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z2,z3,z4,z218]),(0,[z0,z1,z404,z2,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z117,z0,z1,z2,z182,z4,z5]),(0,[z0,z405,z1,z2,z3,z4,z5])],[(0,[z406,z0,z1,z2,z3,z4,z5]),(0,[z73,z0,z1,z2,z128,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z407]),(0,[z0,z331,z1,z2,z3,z4,z5])],[(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z0,z409,z1,z2,z3,z4,z5]),(0,[z0,z410,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z411,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z412]),(0,[z0,z1,z30,z2,z3,z42,z4]),(0,[z0,z1,z2,z3,z4,z5,z413])],[(0,[z0,z1,z2,z414,z3,z4,z5]),(0,[z0,z415,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z416,z5]),(0,[z417,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z418,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z43,z5])],[(0,[z0,z1,z44,z290,z3,z4,z5]),(0,[z0,z419,z1,z2,z3,z4,z5]),(0,[z420,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z175,z2,z4,z5]),(0,[z0,z1,z2,z290,z3,z4,z5]),(0,[z0,z421,z1,z2,z3,z4,z5]),(0,[z0,z331,z1,z2,z3,z4,z69]),(0,[z0,z53,z1,z2,z3,z4,z40])],[(0,[z0,z1,z2,z3,z4,z422,z5]),(0,[z0,z1,z39,z200,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z423,z5]),(0,[z0,z1,z424,z2,z3,z4,z5]),(0,[z425,z0,z1,z2,z3,z4,z5])],[(0,[z426,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z427,z5]),(0,[z0,z1,z30,z2,z3,z4,z5])],[(0,[z0,z1,z2,z130,z128,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z428]),(0,[z0,z1,z2,z3,z429,z4,z5])],[(0,[z73,z0,z1,z2,z3,z157,z5]),(0,[z0,z1,z3,z45,z4,z174,z5]),(0,[z0,z430,z1,z2,z3,z4,z5])],[(0,[z117,z1,z127,z2,z3,z4,z5]),(0,[z0,z1,z2,z431,z3,z4,z5]),(0,[z0,z1,z2,z3,z432,z4,z5])],[(0,[z433,z0,z1,z2,z3,z4,z5]),(0,[z0,z434,z1,z2,z3,z4,z5]),(0,[z435,z53,z1,z2,z3,z4,z5]),(0,[z0,z436,z1,z2,z3,z4,z5]),(0,[z0,z437,z1,z2,z3,z4,z5])],[(0,[z0,z438,z1,z2,z3,z4,z5]),(0,[z23,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z439,z4,z5]),(0,[z0,z152,z331,z2,z3,z4,z5]),(0,[z0,z105,z1,z2,z19,z4,z5])],[(0,[z0,z1,z70,z2,z3,z174,z5]),(0,[z0,z1,z2,z440,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z441,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z442]),(0,[z0,z1,z2,z59,z3,z4,z5]),(0,[z0,z158,z62,z2,z3,z4,z5])],[(0,[z0,z1,z443,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z444,z5])],[(0,[z317,z0,z1,z2,z3,z4,z5])],[(0,[z445,z0,z1,z2,z3,z4,z5]),(0,[z446,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z216,z3,z4,z5]),(0,[z0,z1,z2,z3,z447,z4,z5]),(0,[z0,z1,z70,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z4,z325])],[(1,[z0,z1,z2,z3,z4,z123]),(0,[z0,z448,z1,z2,z3,z4,z5]),(0,[z0,z1,z449,z2,z3,z4,z5]),(0,[z0,z1,z450,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z451,z5])],[(0,[z0,z452,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z453,z4,z5]),(0,[z0,z158,z1,z290,z3,z4,z5])],[(0,[z0,z454,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z455,z3,z4,z5]),(0,[z0,z456,z1,z2,z3,z4,z5]),(0,[z0,z457,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z98,z3,z4,z5]),(1,[z240,z1,z2,z3,z82,z5]),(0,[z0,z1,z2,z3,z4,z25,z5]),(0,[z317,z0,z1,z2,z3,z4,z10]),(0,[z0,z458,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z459,z5]),(0,[z0,z105,z1,z2,z3,z4,z325])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z460,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z461,z4,z5]),(0,[z0,z201,z1,z2,z4,z5,z40]),(0,[z0,z1,z2,z3,z4,z462,z5])],[(0,[z463,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z44,z3,z4,z5,z54]),(0,[z0,z1,z2,z3,z24,z84,z5]),(0,[z0,z1,z2,z3,z4,z5,z464]),(0,[z0,z2,z3,z17,z4,z84,z5]),(0,[z0,z465,z1,z2,z3,z4,z5]),(0,[z435,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z54]),(0,[z0,z1,z2,z3,z4,z5,z466])],[(0,[z117,z0,z1,z2,z348,z4,z5]),(0,[z467,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z25,z69]),(0,[z0,z137,z1,z199,z2,z4,z5]),(0,[z0,z468,z1,z2,z3,z4,z5]),(0,[z0,z469,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z470,z5]),(0,[z0,z471,z1,z2,z3,z4,z5])],[(0,[z472,z0,z1,z2,z3,z4,z5]),(0,[z0,z473,z1,z2,z3,z4,z5]),(0,[z0,z1,z199,z2,z4,z5,z40]),(0,[z0,z105,z1,z2,z3,z42,z5])],[(0,[z0,z1,z474,z2,z3,z4,z5]),(0,[z317,z0,z1,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z4,z5,z475]),(0,[z0,z476,z1,z2,z3,z4,z5]),(0,[z0,z477,z1,z2,z3,z4,z5]),(0,[z0,z1,z478,z2,z3,z4,z5])],[(0,[z479,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z97,z0,z1,z2,z128,z4,z5]),(0,[z480,z0,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z3,z115,z4,z5])],[(0,[z0,z1,z2,z481,z3,z4,z5]),(0,[z482,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z483,z4,z5]),(0,[z0,z1,z484,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z43,z5])],[(0,[z0,z1,z2,z3,z4,z485,z5]),(0,[z0,z1,z2,z486,z3,z4,z5]),(1,[z0,z137,z2,z130,z4,z5]),(0,[z0,z137,z2,z3,z130,z4,z5]),(0,[z487,z0,z1,z2,z3,z4,z5]),(1,[z0,z488,z1,z3,z4,z5])],[(0,[z117,z0,z127,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z489,z5]),(0,[z1,z2,z3,z4,z25,z5,z10]),(1,[z0,z1,z2,z3,z490,z5]),(0,[z491,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z492,z3,z4,z5]),(0,[z0,z1,z492,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z357,z5]),(1,[z91,z92,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z493,z5]),(0,[z0,z61,z1,z2,z453,z4,z5]),(0,[z0,z152,z1,z2,z3,z4,z68]),(0,[z0,z1,z2,z3,z4,z5,z494])],[(0,[z495,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z3,z4,z5])],[(0,[z0,z1,z44,z3,z115,z4,z5]),(0,[z0,z496,z1,z2,z3,z4,z5])],[(0,[z0,z1,z71,z3,z4,z5,z54]),(0,[z0,z497,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z498,z5]),(0,[z0,z1,z499,z2,z3,z4,z5])]],
   [[(0,[z0,z186,z1,z2,z115,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z500]),(0,[z0,z1,z501,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z502,z5])],[(0,[z0,z1,z503,z2,z3,z4,z5]),(0,[z0,z1,z504,z2,z3,z4,z5]),(0,[z0,z1,z3,z115,z4,z234,z5]),(0,[z249,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z62,z2,z3,z4,z5]),(0,[z0,z201,z1,z2,z3,z4,z40]),(0,[z0,z505,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z506]),(0,[z240,z0,z1,z2,z3,z82,z5]),(0,[z0,z1,z507,z2,z3,z4,z5]),(0,[z508,z0,z1,z2,z3,z4,z5]),(0,[z0,z509,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z510,z5]),(0,[z0,z1,z70,z3,z4,z174,z5]),(0,[z0,z1,z39,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z511,z5]),(0,[z0,z1,z2,z184,z130,z4,z5]),(0,[z23,z1,z2,z3,z24,z4,z5]),(0,[z0,z1,z380,z2,z115,z4,z5])],[(1,[z0,z1,z2,z3,z512,z5]),(0,[z0,z1,z2,z3,z513,z4,z5])],[(0,[z0,z61,z1,z290,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z514,z5])],[(0,[z0,z1,z515,z2,z3,z4,z5]),(0,[z124,z1,z71,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z3,z4,z516,z5]),(1,[z0,z1,z177,z3,z4,z5]),(0,[z0,z1,z517,z2,z3,z4,z5])]],
   [[(0,[z124,z1,z2,z3,z4,z5,z10]),(0,[z0,z1,z2,z130,z78,z4,z5]),(0,[z0,z1,z2,z3,z518,z4,z5])],[(0,[z0,z186,z1,z71,z3,z4,z5]),(0,[z97,z1,z2,z184,z3,z4,z5]),(0,[z0,z1,z519,z2,z3,z4,z5]),(0,[z0,z137,z1,z2,z130,z4,z5]),(0,[z0,z1,z520,z2,z3,z4,z5])],[(1,[z0,z61,z290,z3,z4,z5])],[(0,[z521,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z522]),(1,[z0,z1,z2,z3,z523,z5]),(0,[z0,z1,z2,z3,z4,z524,z5]),(0,[z0,z1,z2,z3,z4,z525,z5])],[(0,[z526,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z40]),(0,[z0,z527,z1,z2,z3,z4,z5]),(0,[z0,z1,z528,z2,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z529,z4,z5]),(0,[z530,z0,z1,z2,z3,z4,z5]),(1,[z80,z1,z44,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z225]),(0,[z0,z1,z531,z2,z3,z4,z5]),(0,[z0,z152,z1,z2,z172,z4,z5]),(0,[z0,z532,z1,z2,z3,z4,z5]),(0,[z0,z533,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z534,z4,z5]),(0,[z0,z1,z2,z535,z3,z4,z5])],[(0,[z0,z536,z1,z2,z3,z4,z5]),(0,[z80,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z24,z4,z5]),(0,[z537,z0,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z199,z2,z4,z5]),(0,[z0,z1,z538,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z128,z4,z5]),(0,[z0,z539,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z540]),(1,[z435,z1,z2,z3,z4,z5])],[(0,[z0,z541,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z542,z4,z5])],[(1,[z0,z158,z62,z3,z4,z5]),(0,[z0,z1,z2,z3,z17,z4,z5]),(0,[z0,z543,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z544,z5]),(0,[z545,z0,z1,z2,z3,z4,z5])],[(0,[z27,z0,z2,z3,z130,z4,z5]),(0,[z0,z1,z2,z130,z115,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z546]),(1,[z0,z1,z39,z2,z78,z5]),(0,[z0,z1,z2,z3,z4,z547,z5])],[(0,[z548,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z549,z2,z3,z4,z5]),(0,[z550,z0,z1,z2,z3,z4,z5]),(0,[z551,z0,z1,z2,z3,z4,z5])],[(0,[z552,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z553]),(0,[z0,z1,z2,z3,z4,z554,z5]),(0,[z0,z1,z2,z3,z4,z5,z555])],[(0,[z0,z1,z2,z3,z4,z556,z5]),(0,[z0,z385,z1,z2,z3,z4,z5]),(0,[z0,z557,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z558,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z559,z5]),(0,[z0,z1,z2,z560,z3,z4,z5])],[(0,[z16,z0,z92,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z561]),(0,[z0,z1,z2,z3,z4,z562,z5]),(0,[z0,z1,z2,z3,z43,z5,z325])]],
   [[(0,[z0,z1,z199,z2,z3,z490,z5]),(0,[z0,z331,z1,z2,z3,z4,z68]),(0,[z0,z1,z563,z2,z3,z4,z5]),(0,[z0,z564,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z363,z3,z4,z5])],[(0,[z0,z1,z2,z3,z78,z82,z5]),(0,[z0,z1,z565,z2,z3,z4,z5]),(0,[z0,z1,z30,z2,z3,z4,z54]),(0,[z0,z566,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z567,z4,z5]),(0,[z0,z1,z568,z2,z3,z4,z5]),(0,[z569,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z570])],[(0,[z215,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z200,z199,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z571,z5])],[(0,[z0,z1,z2,z3,z4,z5,z211]),(0,[z0,z572,z1,z2,z3,z4,z5]),(0,[z23,z0,z1,z2,z3,z4,z94]),(1,[z23,z1,z2,z3,z24,z5]),(0,[z0,z1,z2,z3,z4,z5,z573])],[(0,[z0,z1,z30,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z574,z4,z5]),(0,[z0,z1,z2,z3,z4,z575,z5]),(0,[z0,z1,z2,z3,z4,z5,z576])],[(0,[z23,z0,z1,z59,z3,z4,z5]),(0,[z0,z1,z2,z3,z577,z4,z5]),(0,[z0,z1,z380,z3,z115,z4,z5])],[(0,[z0,z1,z2,z245,z3,z4,z5]),(0,[z73,z0,z1,z2,z3,z4,z320]),(0,[z0,z1,z2,z3,z4,z578,z5]),(0,[z0,z152,z1,z2,z89,z4,z5]),(0,[z0,z1,z116,z560,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z579,z5]),(0,[z240,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z580,z5]),(0,[z215,z0,z1,z2,z3,z4,z10]),(0,[z0,z61,z2,z290,z3,z4,z5]),(0,[z0,z186,z52,z1,z3,z4,z5]),(0,[z0,z53,z1,z3,z45,z4,z5]),(0,[z0,z105,z1,z2,z3,z5,z325])],[(0,[z73,z97,z1,z2,z3,z4,z5]),(0,[z0,z1,z581,z2,z3,z4,z5]),(0,[z0,z103,z1,z2,z145,z4,z5]),(0,[z0,z1,z2,z3,z582,z4,z5])],[(0,[z0,z1,z2,z3,z4,z583,z5]),(0,[z0,z1,z2,z3,z584,z4,z5]),(0,[z585,z0,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z2,z3,z42,z4])],[(0,[z0,z92,z2,z3,z130,z4,z5]),(0,[z0,z1,z2,z3,z4,z586,z5]),(0,[z0,z105,z1,z30,z2,z3,z4])],[(1,[z0,z1,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z4,z5,z587]),(1,[z0,z201,z1,z2,z4,z40])],[(0,[z0,z1,z588,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z589,z4,z5]),(0,[z0,z590,z1,z2,z3,z4,z5]),(0,[z215,z0,z1,z2,z3,z4,z25]),(0,[z0,z52,z1,z2,z130,z4,z5]),(0,[z0,z1,z2,z3,z4,z262,z174]),(1,[z0,z1,z200,z2,z79,z5])],[(0,[z591,z0,z1,z2,z3,z4,z5]),(0,[z592,z0,z1,z2,z3,z4,z5])],[(0,[z593,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z24,z79,z5]),(0,[z215,z317,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z594,z5]),(0,[z0,z1,z2,z3,z523,z4,z5]),(0,[z0,z53,z1,z2,z3,z4,z5]),(0,[z0,z53,z1,z30,z3,z4,z5])]],
   [[(0,[z0,z1,z595,z2,z3,z4,z5]),(0,[z0,z1,z199,z2,z3,z523,z5]),(0,[z0,z596,z1,z2,z3,z4,z5])],[(0,[z117,z0,z1,z492,z3,z4,z5]),(0,[z117,z0,z1,z2,z3,z357,z5]),(0,[z0,z1,z2,z597,z3,z4,z5]),(0,[z598,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z599,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z600,z4,z5]),(0,[z601,z0,z1,z2,z3,z4,z5]),(0,[z0,z602,z1,z2,z3,z4,z5]),(0,[z0,z158,z61,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z3,z4,z5]),(0,[z249,z0,z39,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z603,z5])],[(0,[z0,z1,z604,z2,z3,z4,z5]),(0,[z27,z16,z0,z2,z3,z4,z5]),(0,[z0,z52,z1,z380,z2,z4,z5]),(0,[z0,z1,z605,z2,z3,z4,z5])],[(0,[z0,z233,z1,z3,z45,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z606])],[(0,[z0,z1,z71,z290,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z607,z5]),(0,[z0,z608,z1,z2,z3,z4,z5]),(0,[z0,z1,z213,z3,z4,z5,z325])],[(0,[z0,z1,z609,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z610,z5]),(0,[z611,z0,z1,z2,z3,z4,z5]),(0,[z0,z103,z1,z2,z3,z17,z5]),(0,[z0,z612,z1,z2,z3,z4,z5]),(0,[z0,z1,z613,z2,z3,z4,z5]),(0,[z0,z233,z1,z2,z3,z174,z5])]],
   [[(0,[z0,z1,z614,z2,z3,z4,z5]),(0,[z615,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z616,z1,z2,z3,z4,z5]),(0,[z0,z1,z200,z2,z130,z4,z5]),(0,[z617,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z618])],[(0,[z117,z0,z1,z2,z3,z512,z5])],[(0,[z0,z1,z2,z3,z619,z4,z5]),(0,[z0,z1,z2,z3,z620,z4,z5]),(0,[z0,z1,z2,z621,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z622]),(0,[z0,z233,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z623]),(0,[z0,z1,z2,z3,z4,z5,z108])],[(0,[z624,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z625,z3,z4,z5]),(0,[z0,z186,z52,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z626]),(0,[z0,z1,z2,z115,z4,z79,z5]),(0,[z0,z1,z39,z2,z115,z4,z5]),(1,[z0,z387,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z78,z4,z5])],[(0,[z0,z1,z2,z3,z4,z627,z5]),(0,[z0,z131,z1,z2,z3,z4,z5])]],
   [[(0,[z73,z0,z385,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z628,z5]),(0,[z27,z0,z1,z2,z3,z78,z5]),(0,[z0,z1,z2,z629,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z325])],[(0,[z630,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z631,z2,z3,z4,z5]),(0,[z0,z1,z632,z2,z3,z4,z5]),(0,[z0,z633,z1,z2,z3,z4,z5]),(0,[z0,z1,z199,z2,z184,z4,z5]),(0,[z0,z1,z2,z3,z634,z4,z5]),(0,[z0,z186,z1,z380,z3,z4,z5]),(0,[z635,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z636]),(0,[z0,z1,z2,z3,z4,z5,z637])],[(0,[z124,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z638]),(0,[z0,z639,z1,z2,z3,z4,z5]),(0,[z73,z0,z159,z2,z3,z4,z5]),(0,[z0,z640,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z641,z5]),(0,[z27,z0,z2,z3,z4,z84,z5]),(0,[z0,z1,z150,z2,z3,z4,z5]),(0,[z0,z1,z342,z70,z2,z4,z5]),(0,[z0,z1,z642,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z234,z5])],[(0,[z117,z91,z1,z2,z3,z4,z5]),(0,[z0,z1,z643,z2,z3,z4,z5]),(0,[z1,z2,z184,z3,z128,z4,z5]),(0,[z0,z1,z644,z2,z3,z4,z5])],[(0,[z0,z488,z1,z116,z3,z4,z5]),(0,[z0,z1,z2,z645,z3,z4,z5]),(1,[z0,z105,z1,z2,z3,z325])],[(0,[z0,z1,z62,z71,z3,z4,z5]),(0,[z73,z0,z1,z2,z184,z4,z5]),(0,[z0,z199,z2,z3,z130,z4,z5]),(0,[z0,z1,z116,z2,z3,z4,z9])],[(0,[z0,z646,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z2,z4,z79,z5]),(0,[z0,z1,z2,z3,z19,z4,z5])]],
   [[(0,[z0,z647,z1,z2,z3,z4,z5]),(0,[z0,z648,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z234,z10]),(0,[z0,z649,z1,z2,z3,z4,z5]),(0,[z0,z52,z1,z2,z3,z4,z352]),(0,[z0,z1,z2,z3,z4,z5,z650]),(0,[z651,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z652,z5])],[(0,[z0,z1,z2,z3,z115,z4,z5])],[(1,[z317,z1,z2,z3,z4,z10]),(0,[z0,z1,z653,z2,z3,z4,z5])],[(0,[z0,z654,z1,z2,z3,z4,z5]),(0,[z0,z186,z1,z44,z3,z4,z5]),(0,[z0,z655,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z130,z4,z5,z40]),(0,[z0,z1,z656,z2,z3,z4,z5])],[(0,[z0,z103,z1,z2,z3,z78,z5])],[(0,[z80,z1,z2,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z234,z25]),(0,[z0,z1,z2,z3,z130,z4,z5])],[(0,[z0,z1,z2,z3,z4,z657,z5]),(0,[z0,z1,z658,z2,z3,z4,z5]),(0,[z659,z0,z1,z2,z3,z4,z5]),(0,[z0,z660,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z363,z4,z5])],[(0,[z0,z1,z661,z2,z3,z4,z5]),(0,[z0,z1,z200,z2,z3,z78,z5]),(0,[z662,z0,z1,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z2,z3,z4,z118]),(0,[z0,z663,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z84,z5])],[(0,[z0,z1,z2,z664,z3,z4,z5])],[(0,[z0,z1,z2,z3,z665,z4,z5]),(1,[z0,z1,z2,z3,z289,z5]),(0,[z0,z1,z116,z2,z4,z9,z5])],[(0,[z117,z0,z92,z2,z3,z4,z5]),(0,[z80,z0,z1,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z666,z4,z5]),(0,[z0,z1,z667,z2,z3,z4,z5])],[(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z0,z669,z1,z2,z3,z4,z5]),(0,[z670,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z671,z4,z5]),(0,[z0,z1,z2,z3,z4,z672,z5]),(0,[z0,z201,z1,z116,z2,z4,z5])],[(0,[z0,z1,z71,z3,z115,z4,z5]),(0,[z0,z1,z2,z3,z4,z673,z5]),(0,[z0,z1,z199,z2,z3,z4,z5])],[(0,[z674,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z675,z3,z4,z5]),(0,[z0,z1,z676,z2,z3,z4,z5]),(0,[z317,z0,z1,z34,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z677,z5]),(0,[z0,z1,z2,z3,z4,z5,z352])]],
   [[(0,[z0,z1,z199,z116,z2,z4,z5]),(0,[z0,z1,z678,z2,z3,z4,z5]),(0,[z0,z488,z1,z2,z3,z4,z5])],[(0,[z0,z158,z1,z62,z3,z4,z5]),(0,[z679,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z680,z2,z3,z4,z5]),(1,[z0,z1,z34,z3,z4,z5]),(0,[z0,z681,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z234,z5,z54]),(0,[z0,z1,z2,z3,z682,z4,z5])],[(0,[z0,z683,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z684]),(1,[z0,z1,z560,z3,z4,z5])],[(1,[z0,z1,z2,z453,z4,z5]),(0,[z0,z1,z2,z3,z4,z490,z5]),(0,[z0,z103,z1,z2,z3,z84,z5])],[(0,[z0,z1,z2,z3,z4,z685,z5]),(0,[z0,z1,z686,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z687,z5]),(0,[z0,z1,z2,z3,z4,z688,z5])],[(0,[z0,z1,z2,z3,z4,z689,z5]),(0,[z0,z690,z1,z2,z3,z4,z5]),(0,[z691,z0,z1,z2,z3,z4,z5]),(0,[z692,z0,z1,z2,z3,z4,z5]),(0,[z0,z186,z1,z3,z4,z234,z5]),(0,[z0,z1,z30,z2,z3,z4,z234])]],
   [[(0,[z0,z1,z2,z3,z693,z4,z5]),(0,[z694,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z695,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z69]),(0,[z0,z1,z696,z2,z3,z4,z5])],[(0,[z0,z1,z697,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z698,z4,z5])],[(0,[z0,z387,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z699]),(0,[z97,z0,z1,z2,z184,z4,z5]),(0,[z23,z0,z1,z87,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z9,z5])],[(0,[z0,z1,z2,z348,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z700])],[(0,[z0,z701,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z702]),(0,[z0,z1,z2,z703,z3,z4,z5]),(0,[z215,z1,z2,z3,z4,z25,z5]),(0,[z0,z1,z2,z704,z3,z4,z5])],[(0,[z117,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z512,z5]),(0,[z124,z80,z1,z2,z3,z4,z5]),(0,[z705,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z194,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z706]),(1,[z0,z1,z2,z3,z4,z218]),(0,[z0,z53,z1,z2,z3,z4,z54])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z216,z3,z157,z5]),(0,[z0,z1,z150,z2,z4,z5])],[(1,[z1,z44,z3,z4,z123]),(0,[z615,z1,z71,z3,z4,z5]),(0,[z0,z707,z2,z3,z4,z5]),(0,[z0,z1,z708,z3,z4,z5])],[(0,[z0,z1,z2,z3,z157,z5])],[(0,[z0,z1,z709,z2,z4,z5]),(0,[z0,z1,z30,z3,z4,z459])],[(0,[z27,z0,z2,z3,z627,z5]),(0,[z0,z105,z1,z2,z3,z325])],[],[(0,[z92,z710,z2,z3,z4,z5]),(0,[z662,z1,z2,z3,z24,z5]),(0,[z1,z2,z3,z4,z25,z711]),(0,[z0,z158,z712,z3,z4,z5])],[(0,[z0,z1,z2,z130,z4,z352]),(0,[z27,z0,z2,z145,z4,z5]),(0,[z186,z131,z1,z3,z4,z5]),(0,[z0,z53,z1,z3,z179,z4])]],
   [[(0,[z0,z713,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z714,z5])],[],[(0,[z0,z1,z2,z715,z4,z5]),(0,[z0,z1,z604,z3,z4,z234])],[(0,[z0,z1,z716,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z717]),(0,[z0,z1,z2,z718,z4,z5]),(0,[z0,z1,z2,z78,z719,z5])],[(0,[z0,z1,z2,z3,z4,z720]),(0,[z655,z1,z2,z3,z4,z10]),(0,[z0,z1,z721,z3,z4,z5])],[(0,[z0,z1,z98,z3,z289,z5]),(0,[z0,z1,z98,z3,z4,z74]),(0,[z0,z1,z59,z3,z4,z225]),(0,[z0,z1,z722,z3,z4,z5]),(0,[z0,z616,z2,z3,z4,z69]),(0,[z0,z723,z1,z380,z4,z5]),(0,[z0,z1,z2,z363,z4,z5])],[(0,[z117,z127,z492,z3,z4,z5]),(0,[z117,z127,z2,z3,z357,z5])],[(0,[z0,z1,z2,z3,z4,z118]),(0,[z0,z1,z2,z3,z4,z724])]],
   [[(0,[z0,z1,z725,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z726]),(1,[z0,z1,z2,z4,z727])],[(0,[z0,z127,z2,z182,z4,z5]),(0,[z80,z1,z728,z3,z4,z5]),(0,[z0,z1,z2,z729,z4,z5]),(0,[z0,z105,z1,z2,z19,z325])],[(0,[z124,z1,z728,z3,z4,z5]),(0,[z0,z1,z315,z2,z78,z5]),(0,[z0,z387,z1,z70,z3,z174])],[(0,[z0,z1,z2,z730,z4,z5]),(0,[z0,z335,z2,z130,z4,z5]),(0,[z0,z36,z1,z2,z4,z40])],[(0,[z0,z1,z2,z3,z731,z5]),(0,[z73,z1,z2,z128,z4,z74]),(0,[z27,z0,z2,z3,z195,z5]),(0,[z0,z105,z1,z213,z3,z4])],[(0,[z0,z1,z732,z3,z4,z5]),(0,[z0,z1,z733,z3,z4,z5]),(0,[z734,z1,z2,z3,z4,z5]),(0,[z0,z735,z2,z3,z4,z5]),(0,[z0,z1,z70,z3,z174,z5]),(0,[z0,z1,z2,z736,z4,z5])],[(1,[z710,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z737,z5]),(0,[z0,z1,z2,z3,z4,z738])],[(0,[z0,z1,z2,z3,z4,z211]),(0,[z117,z127,z2,z3,z512,z5]),(0,[z0,z739,z1,z2,z3,z5]),(0,[z0,z740,z2,z3,z4,z5]),(0,[z0,z1,z213,z3,z4,z5])]],
   [[(0,[z0,z1,z741,z3,z4,z5]),(0,[z0,z1,z150,z2,z79,z5]),(0,[z0,z2,z3,z4,z5,z742]),(0,[z0,z743,z2,z3,z4,z5])],[(0,[z0,z1,z2,z744,z4,z5]),(0,[z0,z1,z34,z3,z4,z5]),(0,[z23,z1,z2,z3,z24,z94]),(0,[z0,z1,z2,z3,z5,z745]),(0,[z0,z746,z2,z3,z4,z5])],[(0,[z0,z1,z747,z3,z4,z5]),(0,[z0,z1,z560,z3,z4,z5])],[(0,[z243,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z157,z74]),(0,[z23,z1,z59,z3,z24,z5]),(0,[z0,z1,z2,z748,z4,z5])],[(0,[z0,z1,z2,z3,z4,z749])],[(0,[z91,z710,z2,z3,z4,z5]),(0,[z0,z750,z1,z2,z3,z4])],[(0,[z0,z92,z2,z182,z4,z5]),(0,[z0,z1,z2,z348,z512,z5]),(0,[z0,z751,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z752])],[(0,[z0,z1,z753,z3,z4,z5]),(0,[z0,z53,z1,z3,z4,z546])]],
   [[(0,[z0,z1,z754,z2,z3,z5]),(0,[z755,z0,z2,z3,z4,z5]),(0,[z0,z62,z712,z3,z4,z5]),(0,[z0,z152,z2,z172,z4,z69]),(0,[z435,z53,z1,z3,z4,z54])],[],[],[(0,[z0,z1,z245,z3,z4,z5]),(0,[z0,z1,z59,z3,z4,z94]),(0,[z0,z473,z1,z2,z4,z40]),(0,[z249,z0,z2,z3,z4,z5]),(0,[z0,z756,z1,z2,z3,z4]),(0,[z0,z1,z757,z3,z4,z5])],[],[(0,[z0,z1,z492,z3,z4,z211]),(0,[z0,z1,z2,z3,z357,z211])],[(0,[z0,z1,z2,z758,z4,z5]),(0,[z0,z159,z2,z3,z4,z320]),(0,[z0,z1,z2,z3,z4,z218])],[(0,[z0,z1,z759,z3,z4,z5])]],
   [[(0,[z1,z710,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z760])],[(0,[z0,z1,z354,z2,z4,z9]),(0,[z0,z761,z1,z3,z4,z5]),(0,[z0,z1,z2,z762,z4,z5]),(0,[z0,z1,z2,z19,z4,z5])],[(0,[z0,z1,z87,z3,z4,z5]),(0,[z0,z1,z44,z3,z4,z123]),(0,[z317,z1,z34,z3,z4,z10]),(0,[z0,z52,z1,z2,z490,z5]),(0,[z0,z387,z1,z3,z45,z4])],[(0,[z0,z1,z2,z4,z763,z5]),(0,[z97,z1,z2,z184,z4,z5]),(0,[z0,z1,z764,z3,z4,z5]),(0,[z0,z1,z765,z3,z4,z5]),(0,[z0,z723,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z766])],[(0,[z0,z1,z2,z3,z4,z767]),(0,[z0,z509,z2,z130,z4,z5])],[(0,[z0,z1,z768,z3,z4,z5])],[(0,[z0,z1,z2,z19,z4,z10]),(0,[z0,z1,z769,z2,z4,z5])],[(0,[z0,z183,z290,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z770])]],
   [[(0,[z0,z1,z2,z3,z771,z5]),(0,[z0,z1,z3,z4,z234,z772]),(0,[z0,z105,z1,z3,z108,z325]),(0,[z0,z1,z2,z773,z4,z5])],[(0,[z0,z1,z245,z3,z357,z5]),(0,[z0,z1,z2,z774,z4,z5])],[(0,[z0,z1,z2,z3,z4,z775]),(0,[z0,z1,z3,z4,z5,z776]),(0,[z0,z1,z70,z3,z261,z5])],[(0,[z80,z1,z44,z3,z4,z81]),(0,[z0,z1,z777,z3,z4,z5]),(0,[z0,z1,z2,z19,z4,z25]),(0,[z0,z1,z2,z3,z4,z778])],[(0,[z0,z779,z2,z3,z4,z5]),(0,[z1,z2,z3,z24,z737,z5]),(0,[z780,z1,z2,z3,z4,z5]),(0,[z0,z1,z781,z3,z4,z5]),(0,[z782,z1,z2,z3,z4,z5]),(0,[z0,z402,z1,z2,z4,z40])],[(0,[z240,z1,z2,z3,z737,z5]),(0,[z0,z2,z3,z783,z84,z5])],[(0,[z695,z0,z1,z3,z4,z54])],[(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z2,z3,z4,z785]),(0,[z0,z1,z2,z786,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z787,z5]),(0,[z0,z1,z2,z4,z5,z788]),(0,[z124,z1,z519,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z1,z3,z4,z5,z108])],[(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z3,z4,z790]),(0,[z0,z1,z2,z3,z791,z5]),(1,[z0,z712,z3,z4,z5]),(0,[z0,z1,z792,z2,z4,z5])],[(0,[z1,z44,z3,z4,z5,z123]),(0,[z27,z0,z2,z3,z84,z5])],[(0,[z1,z728,z44,z3,z4,z5]),(0,[z0,z793,z2,z3,z4,z5]),(0,[z0,z1,z794,z3,z4,z5]),(0,[z27,z0,z2,z3,z783,z5]),(0,[z249,z0,z2,z3,z79,z5]),(0,[z0,z194,z116,z2,z4,z5]),(0,[z0,z1,z116,z2,z4,z9])],[(0,[z0,z1,z2,z3,z795,z5]),(0,[z0,z1,z2,z3,z796,z5]),(0,[z0,z1,z216,z3,z4,z320]),(0,[z0,z1,z797,z2,z4,z5])],[(0,[z263,z1,z2,z3,z4,z10]),(0,[z0,z2,z3,z130,z523,z5]),(0,[z0,z1,z2,z4,z9,z727])],[(0,[z0,z1,z2,z3,z4,z320]),(0,[z73,z1,z2,z128,z4,z5]),(0,[z0,z1,z2,z3,z798,z5]),(0,[z131,z1,z30,z3,z4,z5])],[(0,[z0,z1,z492,z182,z4,z5]),(0,[z0,z1,z2,z182,z357,z5]),(0,[z0,z710,z2,z3,z4,z5]),(0,[z0,z1,z2,z799,z4,z5]),(0,[z0,z1,z2,z800,z4,z5]),(0,[z801,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z1,z2,z3,z803,z5]),(0,[z0,z1,z3,z4,z5,z804]),(0,[z0,z723,z1,z2,z4,z5])],[(0,[z0,z1,z805,z3,z4,z5]),(0,[z0,z53,z1,z3,z4,z54]),(0,[z0,z105,z1,z2,z3,z261]),(0,[z0,z1,z2,z3,z4,z806])],[(0,[z0,z1,z2,z807,z4,z5]),(0,[z0,z1,z644,z115,z4,z5])],[(0,[z117,z127,z2,z3,z4,z5]),(0,[z0,z1,z808,z3,z4,z5]),(0,[z0,z1,z3,z4,z234,z337]),(0,[z0,z1,z809,z2,z4,z5])],[(0,[z0,z1,z810,z3,z4,z5]),(0,[z322,z92,z2,z3,z4,z5])],[(0,[z0,z1,z811,z3,z4,z5]),(0,[z0,z159,z2,z184,z4,z5]),(0,[z0,z1,z2,z3,z812,z5]),(0,[z0,z283,z2,z130,z4,z5]),(0,[z0,z488,z1,z3,z4,z9])],[(0,[z0,z1,z813,z3,z4,z5])],[(0,[z0,z1,z2,z172,z4,z5])]],
   [[(0,[z0,z1,z2,z182,z512,z5]),(0,[z249,z0,z39,z2,z78,z5]),(0,[z0,z1,z39,z560,z4,z5])],[(0,[z0,z2,z3,z4,z783,z5])],[(0,[z0,z1,z2,z348,z4,z5]),(0,[z0,z1,z814,z3,z4,z5]),(0,[z0,z1,z87,z3,z4,z225]),(0,[z670,z1,z2,z3,z4,z25])],[(0,[z0,z1,z39,z2,z582,z5])],[(0,[z0,z1,z2,z3,z4,z815]),(0,[z0,z1,z2,z816,z4,z5])],[(0,[z0,z1,z817,z3,z4,z5]),(0,[z818,z1,z2,z3,z4,z5])],[(0,[z215,z1,z177,z3,z4,z5]),(0,[z545,z1,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z819,z5])]],
   [[(0,[z1,z2,z177,z3,z4,z10]),(0,[z0,z1,z820,z2,z4,z5]),(0,[z0,z105,z1,z2,z363,z325])],[(0,[z1,z44,z3,z4,z10,z54]),(0,[z821,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z822,z174,z5])],[(0,[z0,z1,z2,z3,z4,z823]),(0,[z313,z1,z71,z3,z4,z5])],[],[(0,[z0,z2,z3,z4,z5,z824]),(0,[z0,z769,z2,z130,z4,z5])],[(0,[z0,z385,z216,z3,z4,z5]),(0,[z0,z1,z825,z2,z4,z5]),(0,[z0,z387,z1,z70,z3,z4]),(0,[z0,z1,z213,z3,z42,z4])],[(0,[z0,z1,z2,z3,z4,z81]),(0,[z0,z1,z2,z826,z4,z5]),(0,[z16,z0,z2,z3,z523,z5]),(0,[z0,z1,z2,z3,z783,z5]),(0,[z0,z1,z3,z822,z4,z5]),(0,[z0,z53,z1,z645,z3,z4])],[(0,[z0,z1,z2,z3,z289,z320]),(0,[z73,z1,z2,z128,z289,z5])]],
   [[(0,[z0,z1,z492,z348,z4,z5]),(0,[z0,z1,z2,z348,z357,z5]),(0,[z0,z1,z2,z827,z4,z5]),(0,[z0,z828,z2,z3,z4,z5]),(0,[z23,z1,z87,z3,z24,z5]),(0,[z0,z1,z2,z89,z4,z5]),(0,[z0,z194,z200,z2,z4,z5])],[(0,[z124,z1,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z829,z5])],[(0,[z117,z127,z2,z3,z4,z118]),(0,[z0,z1,z72,z2,z79,z5]),(0,[z0,z1,z2,z830,z4,z5])],[(0,[z831,z1,z2,z3,z4,z5]),(0,[z0,z832,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z5,z766]),(0,[z0,z1,z833,z3,z4,z5])],[(0,[z0,z1,z834,z3,z4,z5]),(0,[z0,z331,z2,z3,z4,z68])],[(0,[z0,z1,z3,z45,z5,z636])],[(0,[z0,z1,z2,z3,z4,z835])],[(0,[z692,z1,z44,z3,z4,z5]),(0,[z0,z331,z2,z3,z4,z742]),(0,[z0,z836,z2,z3,z4,z5]),(0,[z0,z1,z212,z4,z234,z5])]],
   [[(0,[z0,z1,z87,z3,z4,z94]),(0,[z0,z1,z2,z3,z837,z5]),(0,[z131,z1,z70,z3,z4,z5])],[(0,[z0,z1,z838,z3,z4,z5]),(0,[z0,z61,z712,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z2,z3,z840,z5])],[(0,[z0,z1,z2,z841,z4,z5])],[(0,[z0,z364,z2,z130,z4,z5]),(0,[z0,z1,z2,z3,z4,z842]),(0,[z0,z1,z2,z3,z4,z772])],[(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z1,z2,z3,z844,z5]),(0,[z0,z1,z2,z4,z79,z352])],[(0,[z0,z1,z2,z845,z4,z5]),(0,[z0,z1,z2,z145,z4,z5])],[(0,[z0,z1,z2,z846,z4,z5]),(0,[z0,z647,z2,z130,z4,z5])],[(1,[z1,z177,z3,z4,z10])]],
   [[(0,[z0,z1,z2,z847,z4,z5]),(0,[z0,z1,z2,z848,z4,z5]),(0,[z0,z2,z145,z17,z4,z5])],[(0,[z0,z1,z2,z849,z4,z5]),(0,[z850,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z262]),(0,[z0,z1,z851,z3,z4,z5]),(0,[z0,z1,z2,z3,z42,z766])],[(0,[z710,z127,z2,z3,z4,z5]),(0,[z0,z1,z852,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z772])],[(0,[z0,z1,z2,z3,z853,z5]),(0,[z0,z1,z854,z3,z4,z5]),(0,[z0,z1,z855,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z856]),(0,[z857,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z3,z4,z234]),(1,[z0,z1,z3,z4,z772])],[(0,[z0,z1,z2,z3,z858,z5]),(0,[z120,z1,z2,z3,z4,z10]),(0,[z0,z1,z859,z3,z4,z5]),(0,[z0,z201,z1,z2,z4,z727])]],
   [[(0,[z0,z385,z2,z3,z4,z74]),(0,[z0,z860,z2,z3,z4,z5]),(0,[z97,z1,z2,z861,z4,z5])],[(0,[z0,z1,z2,z3,z4,z123]),(0,[z371,z1,z44,z3,z4,z5]),(0,[z131,z1,z2,z3,z4,z234])],[(0,[z862,z1,z2,z3,z4,z5])],[(0,[z0,z159,z2,z3,z4,z74]),(0,[z0,z1,z30,z2,z19,z4]),(0,[z0,z1,z3,z4,z5,z863])],[(0,[z0,z1,z2,z182,z4,z5]),(0,[z0,z712,z2,z3,z4,z5]),(0,[z0,z1,z517,z115,z4,z5])],[],[(0,[z0,z448,z2,z130,z4,z5]),(0,[z0,z564,z2,z130,z4,z5]),(0,[z131,z1,z2,z3,z4,z54])],[(0,[z1,z71,z728,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z864,z4,z5]),(0,[z0,z488,z1,z3,z4,z40])],[(0,[z0,z1,z2,z865,z4,z5]),(0,[z0,z39,z194,z2,z78,z5])],[(0,[z635,z1,z71,z3,z4,z5]),(0,[z0,z1,z866,z3,z4,z5])],[(0,[z0,z1,z867,z3,z4,z5]),(0,[z691,z1,z2,z3,z4,z10])],[(0,[z0,z1,z868,z3,z4,z5]),(0,[z0,z194,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z742,z69]),(0,[z869,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z560,z4,z9])],[(0,[z0,z1,z245,z3,z4,z118]),(0,[z0,z1,z870,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z871]),(0,[z0,z1,z98,z3,z4,z320]),(0,[z73,z1,z98,z128,z4,z5]),(0,[z0,z137,z769,z2,z4,z5]),(0,[z0,z1,z2,z212,z4,z5]),(1,[z131,z1,z3,z4,z54])],[(0,[z0,z1,z2,z3,z872,z5]),(0,[z1,z2,z184,z861,z4,z5]),(0,[z0,z873,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z4,z559]),(0,[z0,z1,z2,z3,z4,z874])],[(0,[z0,z1,z2,z3,z490,z5]),(0,[z0,z1,z39,z2,z210,z5]),(0,[z131,z1,z3,z4,z5,z54]),(0,[z131,z1,z2,z3,z4,z9])]],
   [[(0,[z91,z92,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z875]),(0,[z0,z876,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z877,z5]),(0,[z0,z1,z2,z878,z4,z5]),(0,[z0,z879,z2,z3,z4,z5])],[(1,[z1,z728,z3,z4,z5]),(0,[z880,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z490,z5])],[(0,[z1,z728,z2,z3,z4,z5]),(0,[z67,z1,z2,z3,z24,z5]),(0,[z215,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z719,z4,z5])],[(0,[z0,z1,z2,z881,z4,z5]),(0,[z0,z53,z1,z3,z4,z623])],[(0,[z0,z1,z98,z3,z157,z5]),(0,[z73,z1,z2,z128,z4,z320]),(0,[z0,z53,z1,z2,z19,z4])],[(0,[z882,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z883]),(0,[z0,z884,z2,z3,z4,z5])],[(0,[z0,z885,z1,z3,z4,z5]),(0,[z460,z1,z44,z3,z4,z5]),(0,[z0,z61,z175,z290,z4,z5])],[(0,[z0,z1,z2,z3,z886,z5]),(0,[z705,z1,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z887]),(0,[z215,z1,z2,z3,z4,z711]),(0,[z0,z1,z3,z888,z4,z5])]],
   [[(0,[z0,z1,z889,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z1,z3,z45,z822,z5]),(0,[z131,z105,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z512,z5]),(0,[z0,z1,z216,z3,z4,z74]),(0,[z0,z1,z891,z3,z4,z5]),(0,[z0,z1,z892,z2,z4,z5]),(0,[z0,z1,z342,z2,z4,z5])],[(0,[z0,z1,z2,z893,z4,z5]),(0,[z0,z186,z1,z3,z4,z218])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z2,z182,z4,z118]),(0,[z0,z1,z895,z3,z4,z5]),(0,[z0,z1,z177,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z3,z157,z320]),(0,[z73,z1,z2,z128,z157,z5]),(0,[z131,z1,z3,z115,z4,z5]),(0,[z0,z1,z2,z896,z4,z5])],[(0,[z0,z1,z2,z897,z4,z5]),(0,[z0,z1,z70,z3,z493,z5]),(0,[z0,z1,z898,z3,z4,z5]),(0,[z1,z2,z861,z128,z4,z5]),(0,[z0,z1,z899,z3,z4,z5]),(0,[z0,z52,z194,z2,z4,z5]),(0,[z0,z1,z2,z900,z4,z5])],[(0,[z0,z1,z2,z3,z4,z901]),(0,[z0,z1,z2,z3,z902,z5]),(0,[z0,z1,z903,z3,z4,z5]),(0,[z0,z1,z2,z3,z904,z5]),(0,[z0,z1,z2,z905,z4,z5]),(0,[z0,z1,z906,z3,z4,z5]),(0,[z0,z1,z2,z907,z4,z5]),(0,[z0,z1,z2,z908,z4,z5]),(0,[z0,z1,z2,z3,z4,z352])],[(0,[z0,z1,z492,z3,z357,z5]),(0,[z0,z1,z2,z3,z909,z5]),(0,[z0,z1,z2,z910,z4,z5]),(0,[z0,z1,z2,z3,z4,z911]),(0,[z0,z454,z62,z3,z4,z5]),(0,[z0,z61,z290,z3,z4,z5]),(0,[z0,z152,z2,z3,z4,z69]),(0,[z0,z53,z1,z212,z4,z5])],[(0,[z0,z1,z2,z3,z523,z5]),(0,[z0,z1,z2,z3,z822,z5])]],
   [[(0,[z0,z912,z2,z3,z4,z5]),(0,[z0,z1,z177,z3,z4,z10]),(0,[z0,z1,z305,z3,z4,z234])],[(0,[z80,z1,z44,z3,z4,z123])],[(0,[z0,z1,z2,z3,z4,z913]),(0,[z80,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z225]),(0,[z1,z2,z3,z4,z711,z5])],[(0,[z0,z105,z1,z213,z3,z325])],[(0,[z435,z1,z2,z3,z4,z5]),(0,[z0,z1,z914,z3,z4,z5]),(0,[z0,z1,z560,z130,z4,z5])],[(0,[z0,z1,z915,z3,z4,z5]),(0,[z0,z1,z177,z3,z4,z25]),(0,[z611,z0,z2,z130,z4,z5]),(0,[z0,z1,z2,z3,z916,z5]),(0,[z0,z233,z1,z3,z822,z5])],[(0,[z0,z1,z2,z3,z917,z5])],[(0,[z0,z1,z492,z3,z512,z5]),(0,[z1,z2,z3,z4,z711,z10]),(0,[z0,z1,z2,z3,z4,z918]),(0,[z0,z1,z380,z115,z4,z5]),(0,[z0,z1,z39,z2,z78,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z919]),(0,[z0,z920,z1,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z1,z2,z922,z4,z5])],[(0,[z0,z385,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z923]),(0,[z0,z1,z2,z3,z924,z5]),(0,[z0,z233,z1,z3,z45,z5]),(1,[z0,z1,z3,z822,z5]),(0,[z925,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z772,z54]),(0,[z0,z1,z2,z719,z79,z5]),(0,[z0,z1,z2,z3,z43,z766])],[(0,[z0,z1,z926,z3,z4,z5]),(0,[z0,z159,z216,z3,z4,z5]),(0,[z0,z1,z927,z3,z4,z5]),(1,[z1,z2,z3,z4,z711]),(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z1,z2,z3,z4,z929])],[(0,[z0,z930,z2,z3,z4,z5]),(0,[z372,z1,z2,z128,z4,z5]),(0,[z317,z1,z177,z3,z4,z10]),(0,[z0,z1,z39,z2,z4,z352]),(0,[z0,z931,z1,z3,z4,z5])],[(0,[z0,z1,z2,z932,z4,z5]),(0,[z0,z159,z2,z3,z4,z5]),(0,[z0,z1,z199,z560,z4,z5])],[(0,[z0,z1,z200,z2,z490,z5]),(0,[z0,z1,z2,z3,z933,z5]),(0,[z0,z1,z934,z3,z4,z5])],[(0,[z935,z0,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z719,z5])],[(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z712,z290,z3,z4,z5]),(0,[z0,z723,z1,z115,z4,z5])],[(0,[z0,z1,z937,z3,z4,z5]),(0,[z0,z938,z2,z3,z4,z5]),(0,[z0,z939,z1,z3,z4,z5]),(0,[z0,z1,z940,z3,z4,z5])],[(0,[z0,z941,z2,z3,z4,z5]),(0,[z0,z1,z942,z3,z4,z5]),(0,[z569,z1,z2,z3,z4,z25]),(0,[z0,z943,z1,z2,z3,z4]),(0,[z0,z944,z2,z3,z4,z5]),(0,[z0,z53,z1,z3,z4,z353])],[(0,[z0,z1,z2,z348,z4,z118]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z3,z289,z74]),(0,[z27,z0,z2,z130,z78,z5])],[(0,[z117,z127,z2,z3,z4,z211]),(0,[z0,z1,z2,z946,z4,z5]),(0,[z0,z655,z1,z3,z4,z54]),(0,[z446,z1,z2,z3,z4,z10]),(0,[z0,z1,z175,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z947]),(0,[z0,z1,z948,z3,z4,z5]),(1,[z0,z1,z2,z3,z766])],[(0,[z0,z131,z1,z3,z4,z54]),(0,[z0,z1,z30,z3,z4,z772]),(0,[z0,z949,z1,z3,z4,z5])],[(0,[z0,z1,z2,z3,z950,z5]),(0,[z0,z1,z951,z3,z4,z5]),(0,[z0,z1,z2,z952,z4,z5]),(0,[z0,z1,z953,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z954])],[(0,[z0,z1,z955,z3,z4,z5])],[(0,[z0,z1,z728,z3,z4,z5]),(0,[z0,z1,z2,z956,z4,z5]),(0,[z0,z1,z2,z3,z957,z5])],[],[(0,[z0,z1,z2,z348,z4,z211]),(0,[z0,z958,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z4,z369])],[(0,[z0,z1,z2,z959,z4,z5]),(0,[z0,z1,z680,z2,z78,z5]),(0,[z0,z1,z2,z960,z4,z5])],[(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z53,z1,z306,z3,z4])],[(0,[z0,z962,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z963]),(0,[z1,z2,z3,z4,z737,z5]),(0,[z0,z194,z2,z115,z4,z5]),(0,[z0,z1,z39,z2,z719,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z964])],[(0,[z117,z127,z245,z3,z4,z5]),(0,[z0,z1,z2,z965,z4,z5]),(0,[z0,z572,z1,z3,z45,z5]),(0,[z0,z966,z1,z2,z3,z4]),(0,[z0,z61,z290,z453,z4,z5]),(0,[z0,z1,z2,z967,z4,z5]),(0,[z0,z1,z2,z3,z42,z85])],[(0,[z0,z1,z2,z3,z968,z5]),(0,[z0,z1,z2,z969,z4,z5]),(0,[z0,z1,z970,z2,z4,z5]),(0,[z0,z1,z2,z115,z490,z5]),(0,[z0,z1,z971,z3,z4,z5]),(0,[z131,z1,z2,z3,z4,z40]),(0,[z0,z53,z1,z3,z4,z21])],[(0,[z0,z1,z216,z3,z4,z5]),(0,[z0,z385,z2,z3,z289,z5])],[(0,[z972,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z440,z4,z9])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z973,z2,z4,z5]),(0,[z0,z974,z1,z3,z4,z5]),(0,[z0,z1,z712,z3,z4,z5]),(0,[z0,z1,z70,z3,z262,z174])],[(0,[z0,z1,z2,z3,z975,z5]),(0,[z0,z1,z3,z4,z976,z5]),(0,[z0,z159,z2,z3,z289,z5]),(0,[z0,z1,z3,z115,z4,z218])],[(0,[z240,z1,z2,z3,z82,z5]),(0,[z0,z53,z1,z3,z4,z772])]],
   [[(0,[z0,z1,z245,z348,z4,z5]),(0,[z0,z1,z2,z3,z4,z977]),(0,[z0,z978,z2,z3,z4,z5])],[(0,[z0,z1,z71,z212,z4,z5]),(0,[z0,z1,z18,z115,z4,z5]),(0,[z0,z105,z1,z2,z3,z766])],[],[(0,[z0,z1,z2,z979,z4,z5])],[(1,[z1,z2,z861,z4,z5]),(1,[z0,z2,z3,z4,z742]),(0,[z0,z1,z2,z980,z4,z5])],[(0,[z0,z1,z2,z4,z981,z5]),(0,[z417,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z982]),(0,[z601,z0,z2,z3,z84,z5])],[(0,[z0,z1,z983,z3,z4,z5]),(0,[z0,z1,z2,z984,z4,z5])],[(0,[z117,z127,z2,z182,z4,z5]),(0,[z0,z985,z2,z3,z4,z5]),(0,[z1,z2,z3,z861,z4,z5]),(0,[z0,z1,z2,z986,z4,z5]),(0,[z27,z0,z2,z3,z439,z5]),(0,[z0,z608,z1,z2,z4,z40]),(0,[z0,z1,z200,z2,z719,z5])]],
   [[(0,[z23,z1,z2,z3,z24,z225]),(1,[z0,z1,z2,z719,z5]),(0,[z0,z1,z987,z3,z4,z5])],[(0,[z0,z1,z2,z988,z4,z5]),(0,[z0,z137,z2,z130,z4,z5]),(0,[z0,z488,z1,z3,z4,z5])],[(0,[z0,z1,z989,z3,z4,z5])],[(0,[z0,z1,z492,z3,z4,z5]),(0,[z0,z1,z2,z3,z357,z5]),(0,[z0,z1,z2,z3,z4,z990]),(0,[z0,z1,z991,z3,z4,z5])],[(0,[z0,z1,z992,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z993,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z994]),(0,[z0,z1,z995,z3,z4,z5]),(0,[z0,z1,z2,z490,z5,z40])],[(0,[z0,z1,z2,z3,z996,z5]),(0,[z651,z1,z2,z3,z82,z5]),(0,[z23,z1,z2,z3,z737,z5]),(0,[z317,z1,z2,z3,z4,z10])],[]],
   [[(0,[z0,z1,z245,z3,z4,z211]),(0,[z0,z1,z2,z3,z4,z997]),(0,[z0,z1,z501,z2,z79,z5])],[(0,[z0,z1,z2,z3,z42,z209]),(0,[z0,z1,z450,z2,z79,z5])],[(0,[z0,z1,z150,z2,z490,z5])],[(0,[z0,z152,z2,z3,z4,z742])],[(0,[z0,z1,z216,z3,z289,z5]),(0,[z0,z2,z130,z411,z4,z5]),(0,[z0,z1,z2,z3,z766,z325])],[(0,[z0,z1,z998,z2,z3,z5]),(0,[z0,z1,z30,z3,z4,z423]),(0,[z1,z2,z3,z4,z999,z5])],[(0,[z0,z1,z2,z3,z1000,z5]),(0,[z0,z1,z2,z3,z289,z5])],[(0,[z0,z1,z2,z3,z4,z1001]),(0,[z0,z1,z2,z3,z1002,z5]),(0,[z0,z1,z2,z3,z1003,z5]),(0,[z0,z1004,z2,z3,z4,z5])]],
   [[(0,[z317,z1,z2,z3,z4,z711]),(0,[z0,z1,z2,z3,z1005,z5]),(0,[z0,z1,z1006,z2,z3,z5])],[],[],[(0,[z0,z1,z150,z2,z78,z5]),(0,[z0,z1,z2,z1007,z4,z5])],[(0,[z0,z1,z2,z1008,z4,z5]),(0,[z0,z1009,z1,z2,z3,z4]),(0,[z0,z1010,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z5,z1011])],[(0,[z0,z1,z2,z182,z4,z211]),(0,[z0,z1,z156,z115,z4,z5]),(0,[z0,z1,z1012,z2,z3,z5]),(0,[z0,z2,z3,z4,z68,z742]),(0,[z0,z53,z1,z3,z4,z362])],[(0,[z0,z1,z2,z3,z4,z1013])]],
   [[(0,[z117,z127,z2,z348,z4,z5]),(0,[z1,z2,z3,z737,z82,z5]),(0,[z0,z1,z2,z453,z4,z5]),(0,[z1014,z1,z2,z3,z4,z5])],[(0,[z0,z1015,z1,z2,z4,z5]),(0,[z124,z1,z2,z3,z4,z123]),(0,[z0,z385,z98,z3,z4,z5]),(0,[z0,z158,z62,z3,z4,z5])],[(0,[z0,z1,z492,z3,z4,z118]),(0,[z0,z1,z2,z3,z357,z118]),(0,[z0,z1,z2,z1016,z4,z5]),(0,[z0,z769,z2,z3,z4,z5]),(0,[z0,z1,z2,z431,z78,z5]),(0,[z0,z1,z1017,z3,z4,z5])],[(0,[z1018,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1019,z4,z5]),(0,[z0,z159,z98,z3,z4,z5]),(0,[z0,z1,z1020,z3,z4,z5]),(0,[z0,z1,z2,z1021,z4,z5]),(0,[z0,z1,z2,z3,z1022,z5]),(0,[z0,z1,z342,z70,z174,z5]),(0,[z53,z131,z1,z3,z4,z54])],[(0,[z0,z1,z2,z1023,z4,z5]),(0,[z0,z1,z1024,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z0,z1,z70,z212,z174,z5])],[(0,[z0,z1,z3,z4,z5,z1026])],[(0,[z0,z1,z2,z3,z4,z1027]),(0,[z189,z1,z2,z3,z4,z10]),(0,[z0,z194,z2,z4,z5,z40]),(0,[z0,z1,z2,z4,z5,z727])]],
   [[(0,[z0,z385,z2,z3,z4,z320]),(0,[z73,z385,z2,z128,z4,z5])],[(0,[z0,z1,z2,z3,z1028,z5]),(0,[z215,z1,z2,z3,z4,z219])],[(0,[z0,z1,z245,z182,z4,z5]),(0,[z0,z159,z2,z128,z4,z5]),(0,[z0,z1,z2,z3,z4,z1029]),(0,[z0,z1,z2,z3,z4,z1030]),(0,[z0,z1,z2,z4,z727,z40])],[(0,[z0,z1,z2,z3,z512,z118]),(0,[z0,z1,z2,z3,z4,z1031]),(0,[z73,z159,z2,z128,z4,z5]),(0,[z23,z1,z2,z3,z24,z5]),(0,[z0,z488,z1,z116,z4,z9])],[(0,[z0,z1,z2,z3,z5,z1032])],[(0,[z0,z1,z2,z3,z1033,z5]),(0,[z0,z1,z2,z861,z4,z5]),(0,[z0,z1,z2,z1034,z4,z5])],[(0,[z0,z1,z2,z1035,z4,z5]),(0,[z73,z1,z2,z861,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z385,z2,z3,z157,z5]),(0,[z1,z177,z3,z4,z5,z10]),(0,[z0,z194,z2,z78,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1037])],[(0,[z0,z243,z1,z3,z4,z54]),(0,[z0,z48,z2,z130,z4,z5])],[(0,[z1,z2,z44,z3,z4,z123]),(0,[z0,z159,z2,z3,z157,z5]),(0,[z0,z1,z2,z78,z490,z5])],[(0,[z0,z1,z2,z3,z512,z211]),(0,[z0,z1,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z4,z1038]),(0,[z0,z1,z1039,z2,z4,z5]),(0,[z0,z201,z1,z2,z4,z40])],[(0,[z0,z1,z2,z3,z1040,z5]),(0,[z27,z0,z2,z3,z578,z5]),(0,[z0,z1,z200,z2,z79,z5]),(0,[z0,z1,z2,z3,z42,z43])],[(0,[z0,z1,z1041,z3,z4,z5]),(0,[z117,z710,z2,z3,z4,z5]),(0,[z0,z1,z59,z3,z4,z5]),(1,[z1,z2,z3,z737,z5]),(0,[z0,z1,z1042,z2,z4,z5]),(0,[z0,z1043,z2,z3,z4,z5])],[(0,[z1044,z1,z2,z3,z4,z5]),(0,[z0,z152,z2,z89,z4,z69])],[(0,[z0,z1,z2,z3,z1045,z5]),(0,[z0,z1046,z2,z3,z4,z5]),(0,[z167,z1,z2,z184,z4,z5]),(0,[z480,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z1048,z2,z4,z5])]],
   [[(0,[z0,z1,z71,z3,z4,z123]),(0,[z0,z663,z2,z3,z4,z68]),(0,[z0,z1,z2,z3,z4,z1049]),(0,[z0,z1050,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z727])],[(0,[z263,z1,z44,z3,z4,z5]),(0,[z0,z1,z199,z2,z4,z352]),(0,[z0,z1,z560,z4,z79,z5])],[(0,[z0,z1,z2,z3,z1051,z5]),(0,[z1052,z1,z2,z3,z4,z5]),(0,[z0,z1,z116,z2,z4,z727])],[(0,[z0,z1,z44,z212,z4,z5])],[(0,[z372,z127,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1053]),(0,[z0,z1,z2,z3,z1054,z5]),(0,[z0,z1,z98,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z1,z1056,z2,z4,z5]),(0,[z0,z1,z70,z3,z822,z5]),(0,[z131,z1,z3,z45,z4,z5]),(0,[z0,z1,z30,z3,z4,z603])],[(0,[z0,z1,z2,z3,z4,z1057]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z0,z1,z1059,z3,z4,z5])],[(0,[z131,z1,z2,z3,z42,z4]),(0,[z249,z0,z2,z3,z78,z5])],[(0,[z0,z1,z245,z3,z512,z5]),(0,[z433,z1,z2,z3,z82,z5]),(0,[z0,z1,z1060,z3,z4,z5]),(0,[z0,z105,z1,z2,z3,z88]),(0,[z0,z1,z2,z3,z4,z1061])]],
   [[],[(0,[z73,z1,z216,z128,z4,z5])],[],[(0,[z0,z1062,z1,z2,z3,z4]),(0,[z131,z1,z2,z3,z4,z5]),(0,[z0,z1,z1063,z2,z4,z5]),(0,[z0,z1,z1064,z3,z4,z5])],[(0,[z0,z1,z1065,z3,z4,z5]),(0,[z0,z1066,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1067])],[(0,[z0,z1068,z2,z3,z4,z5]),(0,[z0,z387,z1,z2,z3,z4])],[(0,[z0,z1,z1069,z2,z4,z5]),(0,[z0,z1,z1070,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1071])],[(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1,z2,z3,z4,z1073])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 555) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 555).take 492) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1047)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [555, 492] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 168).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 168).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [168, 88] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_46066

theorem PEqualNP.Outside.L_meta_46066 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276152480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_46066.solve