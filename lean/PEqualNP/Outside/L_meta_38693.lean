import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38693

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
  Nat.testBit (4276808392 * 2 ^ 32 + 4243122376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00113138c40d1b11#64 ++ 0xa00113138c40d1b1#64 ++ 0xb033f3f9c41f3f37#64 ++ 0xdb033f3f9c41f3f3#64 : BitVec 256),
   (0x00c4848301a24462#64 ++ 0x400c4848301a2446#64 ++ 0x71cc8c8f87e3c7ff#64 ++ 0xb71cc8c8f87e3c7f#64 : BitVec 256),
   (0x060b0b0c1854a984#64 ++ 0x8060b0b0c1854a98#64 ++ 0xfe0f0f0e787cf9cf#64 ++ 0x7fe0f0f0e787cf9c#64 : BitVec 256),
   (0x1b700ed06e80f607#64 ++ 0x01b700ed06e80f60#64 ++ 0xdff00ff07f80fe0e#64 ++ 0xfdff00ff07f80fe0#64 : BitVec 256),
   (0x2dbed000777b0008#64 ++ 0x02dbed000777b000#64 ++ 0xaffff0007fff000d#64 ++ 0xfaffff0007fff000#64 : BitVec 256),
   (0x4fefefef80000000#64 ++ 0x04fefefef8000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb033f3f9c41f3f37 0xdb033f3f9c41f3f3

def z1 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc8c8f87e3c7ff 0xb71cc8c8f87e3c7f

def z2 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f0e787cf9cf 0x7fe0f0f0e787cf9c

def z3 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00ff07f80fe0e 0xfdff00ff07f80fe0

def z4 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff0007fff000d 0xfaffff0007fff000

def z5 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x4ffcfcf780000000 0xa4ffcfcf78000000

def z6 : W := mkw 0x448ec00700000000 0x0448ec0070000000 0x000c000600000000 0x0000c00060000000

def z7 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffffff80000003 0xf4fffffff8000000

def z8 : W := mkw 0x068f8b0f1976a9e4 0xc068f8b0f1976a9e 0xfe0f8f0ff87ff9ff 0x7fe0f8f0ff87ff9f

def z9 : W := mkw 0x00c4848300000000 0x000c484830000000 0x41cc8c8f80000003 0xb41cc8c8f8000000

def z10 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x7fffffff87e3c7ff 0xf7fffffff87e3c7f

def z11 : W := mkw 0x02000a000800a004 0x002000a000800a00 0xde000f007800f80e 0x7de000f007800f80

def z12 : W := mkw 0x1f7b0fdc7ed4ff87 0x81f7b0fdc7ed4ff8 0xffff0ffe7ffcffcf 0xfffff0ffe7ffcffc

def z13 : W := mkw 0x0040048301a24462 0x40040048301a2446 0x70000c8f87e3c7fe 0x070000c8f87e3c7f

def z14 : W := mkw 0x0daec00000000000 0x00daec0000000000 0x0ffff00000000001 0xf0ffff0000000000

def z15 : W := mkw 0x20101000777b0008 0x020101000777b000 0xa00000007fff000c 0x0a00000007fff000

def z16 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f3f980000003 0xd0033f3f98000000

def z17 : W := mkw 0x060a0a041854a984 0x8060a0a041854a98 0xfe0c0c06787cf9cc 0x2fe0c0c06787cf9c

def z18 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ff3f0007f9f0000 0xc8ff3f0007f9f000

def z19 : W := mkw 0x0000000001220000 0x0000000000122000 0x2000000007e3000c 0x02000000007e3000

def z20 : W := mkw 0x0040048300804462 0x4004004830080446 0x50000c8f8000c7f2 0x050000c8f8000c7f

def z21 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0x8e337000781c0000 0x48e337000781c000

def z22 : W := mkw 0x3ffeded07ffbf60f 0x03ffeded07ffbf60 0xfffffff07ffffe0f 0xffffffff07ffffe0

def z23 : W := mkw 0x105004906e80f607 0x0105004906e80f60 0xd1c00c807f80fe0e 0xbd1c00c807f80fe0

def z24 : W := mkw 0x42412fef80000000 0x042412fef8000000 0x40000fff80000002 0x040000fff8000000

def z25 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33737000000000 0x40e3373700000000

def z26 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0x01f0f00007830000 0x801f0f0000783000

def z27 : W := mkw 0x2fbfdb0c7f7fa98c 0x82fbfdb0c7f7fa98 0xffffff0e7ffff9cf 0xfffffff0e7ffff9c

def z28 : W := mkw 0x096004c000000000 0x0096004c00000000 0x01f000f000000000 0x801f000f00000000

def z29 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f0f0f180000000 0x801f0f0f18000000

def z30 : W := mkw 0x0feecec000000000 0x00feecec00000000 0x4ffffff000000003 0xf4ffffff00000000

def z31 : W := mkw 0x0b600ec000000000 0x00b600ec00000000 0x4ff00ff000000002 0xf4ff00ff00000000

def z32 : W := mkw 0x0010001044001201 0x0001000104400120 0x903003f044003e06 0xd903003f044003e0

def z33 : W := mkw 0x1b600ec02a80e406 0x01b600ec02a80e40 0x4fc00c003b80c008 0x24fc00c003b80c00

def z34 : W := mkw 0x0040048000804402 0x0004004800080440 0x51c00c800780c60e 0xb51c00c800780c60

def z35 : W := mkw 0x1bf48ed36fa2f667 0x41bf48ed36fa2f66 0xfffc8fffffe3ffff 0xffffc8fffffe3fff

def z36 : W := mkw 0x42c5afef80000000 0x042c5afef8000000 0x41cc8fff80000003 0xb41cc8fff8000000

def z37 : W := mkw 0x0084800001220000 0x0008480000122000 0x71cc8c0e07e3c1cf 0xb71cc8c0e07e3c1c

def z38 : W := mkw 0x4f2b6b6c9854a984 0x84f2b6b6c9854a98 0x8e337370781c3800 0x48e337370781c380

def z39 : W := mkw 0x448fe12f81220060 0x4448fe12f8122006 0x200ff00f806301f1 0x0200ff00f806301f

def z40 : W := mkw 0x0000000001a24462 0x40000000001a2446 0x3000000007e3c7fc 0x03000000007e3c7f

def z41 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z42 : W := mkw 0x0010101044091211 0x2001010104409121 0x0000000004030630 0x0000000000403063

def z43 : W := mkw 0x248ec00011720008 0x0248ec0001172000 0x000c000000600000 0x0000c00000060000

def z44 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000000441f3f34 0x0b0000000441f3f3

def z45 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x8e30037078003800 0x48e3003707800380

def z46 : W := mkw 0x4fffffffc40d1b11 0xa4fffffffc40d1b1 0xffffffffc41f3f37 0xfffffffffc41f3f3

def z47 : W := mkw 0x197004d066805603 0x0197004d06680560 0x51f00cf00780c60e 0xb51f00cf00780c60

def z48 : W := mkw 0x2d2a400032500008 0x02d2a40003250000 0x0e00000038000000 0x00e0000003800000

def z49 : W := mkw 0x040b312c905d0990 0xa040b312c905d099 0x200ff00f807f01f1 0x0200ff00f807f01f

def z50 : W := mkw 0x0001212880000000 0x0000121288000000 0x0003f00980000001 0x00003f0098000000

def z51 : W := mkw 0x0001213880041b11 0xa0001213880041b1 0x100003f980003f32 0x0100003f980003f3

def z52 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x01c0808187830630 0x801c080818783063

def z53 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x4fffffff87830633 0xf4fffffff8783063

def z54 : W := mkw 0x00103030c40d1b11 0xa00103030c40d1b1 0xb030f0f1c41f3f34 0x8b030f0f1c41f3f3

def z55 : W := mkw 0x00d5b5bbc5af5f73 0xe00d5b5bbc5af5f7 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z56 : W := mkw 0x1f7a0ed47ed0f687 0x01f7a0ed47ed0f68 0xdffc0ff67fe0fece 0xfdffc0ff67fe0fec

def z57 : W := mkw 0x2daed000337b0008 0x02daed000337b000 0x2fcff0003bff0009 0x22fcff0003bff000

def z58 : W := mkw 0x0084800301220060 0x4008480030122006 0x200c800f806301f1 0x0200c800f806301f

def z59 : W := mkw 0x1b600ec02a80e406 0x01b600ec02a80e40 0x4ff00ff03b80c00a 0xf4ff00ff03b80c00

def z60 : W := mkw 0x3f7a5ed07ed9f60f 0x03f7a5ed07ed9f60 0xdff37ff07f9cfe0e 0xfdff37ff07f9cfe0

def z61 : W := mkw 0x0001212880000000 0x0000121288000000 0x3033f3f984030737 0xd3033f3f98403073

def z62 : W := mkw 0x3bf4ded06fabf60f 0x03bf4ded06fabf60 0xdff0fff07f83fe0e 0xfdff0fff07f83fe0

def z63 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33f3f980000003 0xd0e33f3f98000000

def z64 : W := mkw 0x00103030c4091211 0x200103030c409121 0x0030f0f184030630 0x80030f0f18403063

def z65 : W := mkw 0x1b700ec06e80e406 0x01b700ec06e80e40 0xcff00c007f80c00c 0xfcff00c007f80c00

def z66 : W := mkw 0x00d5b5bbc5af5f73 0xe00d5b5bbc5af5f7 0xb1f3f3f9c79f3f37 0xdb1f3f3f9c79f3f3

def z67 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xcffffffff81c3803 0xfcffffffff81c380

def z68 : W := mkw 0x4feecec71850a084 0x04feecec71850a08 0x4fcc0c063860c0c8 0x24fcc0c063860c0c

def z69 : W := mkw 0x2dbff138f77f1b19 0xa2dbff138f77f1b1 0xbffff3f9ffff3f3f 0xfbffff3f9ffff3f3

def z70 : W := mkw 0x061b1b1c5c5dbb95 0xa061b1b1c5c5dbb9 0xfe0f0f0e7c7fffff 0x7fe0f0f0e7c7ffff

def z71 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0008089c41f3f37 0x9b0008089c41f3f3

def z72 : W := mkw 0x0001010800040900 0x8000101080004090 0x1000030800003902 0x0100003080000390

def z73 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x61cc8c0f83e3c1f9 0x261cc8c0f83e3c1f

def z74 : W := mkw 0x1b713ff8ee8dff17 0xa1b713ff8ee8dff1 0xfff3fff9ff9fff3f 0xffff3fff9ff9fff3

def z75 : W := mkw 0x2000000033720008 0x0200000003372000 0x000000003be00008 0x0000000003be0000

def z76 : W := mkw 0x248ed000117b0008 0x0248ed000117b000 0x200ff000007f0001 0x0200ff000007f000

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z78 : W := mkw 0x0010101045af5f73 0xe0010101045af5f7 0xb000000047fffffc 0x0b000000047fffff

def z79 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0xffffffffc01c3907 0xfffffffffc01c390

def z80 : W := mkw 0x0b612fe880000000 0x00b612fe88000000 0x4ff3fff980000003 0xf4ff3fff98000000

def z81 : W := mkw 0x0040048300804462 0x4004004830080446 0x70008c8f8403c7f7 0x970008c8f8403c7f

def z82 : W := mkw 0x2dfed48377fb446a 0x42dfed48377fb446 0xaffff081ffff063d 0xfaffff081ffff063

def z83 : W := mkw 0x000000001854a984 0x8000000001854a98 0x80000000781c3800 0x080000000781c380

def z84 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x4ff37ff000000002 0xf4ff37ff00000000

def z85 : W := mkw 0x060b0b0c0804a984 0x8060b0b0c0804a98 0x5e0f0f0e0000f9c3 0x75e0f0f0e0000f9c

def z86 : W := mkw 0x2daec00033720008 0x02daec0003372000 0x0fcc00003be00008 0x20fcc00003be0000

def z87 : W := mkw 0x06cf8f8f19f6ede6 0xc06cf8f8f19f6ede 0xffcf8f8fffffffff 0xfffcf8f8ffffffff

def z88 : W := mkw 0x4fffffffdc5dbb95 0xa4fffffffdc5dbb9 0xfffffffffc7fffff 0xffffffffffc7ffff

def z89 : W := mkw 0x6fffffeff77b0008 0x06fffffeff77b000 0xefffffffffff000f 0xfefffffffffff000

def z90 : W := mkw 0x0010100044090000 0x0001010004409000 0xa0000000441f0004 0x0a0000000441f000

def z91 : W := mkw 0x0084800001220000 0x0008480000122000 0x01c0800007830000 0x801c080000783000

def z92 : W := mkw 0x00c5b5ab81af4d72 0xe00c5b5ab81af4d7 0x71cffc8f87ffc7ff 0xb71cffc8f87ffc7f

def z93 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0x5e0c0f0e3860f9ca 0x25e0c0f0e3860f9c

def z94 : W := mkw 0x4fefefff80041b11 0xa4fefefff80041b1 0x5fffffff80003f33 0xf5fffffff80003f3

def z95 : W := mkw 0x060b0b0c00000000 0x0060b0b0c0000000 0x4e0f0f0e00000003 0x74e0f0f0e0000000

def z96 : W := mkw 0x0000000000804462 0x4000000000080446 0x100000000000c7f0 0x0100000000000c7f

def z97 : W := mkw 0x6fffffeff7fb446a 0x46fffffeff7fb446 0xffffffffffffc7ff 0xfffffffffffffc7f

def z98 : W := mkw 0x0b713ff8c40d1b11 0xa0b713ff8c40d1b1 0xfff3fff9c41f3f37 0xffff3fff9c41f3f3

def z99 : W := mkw 0x02400e800880e406 0x002400e800880e40 0xdfc00f807f80fe0e 0xfdfc00f807f80fe0

def z100 : W := mkw 0x1bf48ed06fa2f607 0x01bf48ed06fa2f60 0xfffc8ff07fe3fe0f 0xffffc8ff07fe3fe0

def z101 : W := mkw 0x040a000010500000 0x0040a00001050000 0xae0f0000787c000d 0x7ae0f0000787c000

def z102 : W := mkw 0x00c5a5ab80000000 0x000c5a5ab8000000 0x41ffffff80000003 0xf41ffffff8000000

def z103 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0x8e030300781c3800 0x48e030300781c380

def z104 : W := mkw 0x02000a000800a004 0x002000a000800a00 0xfe0c0f0e7860f9cf 0x7fe0c0f0e7860f9c

def z105 : W := mkw 0x12400ed00880f607 0x012400ed00880f60 0x50000ff00000fe02 0x050000ff00000fe0

def z106 : W := mkw 0x040a00001854a984 0x8040a00001854a98 0xbe0f0000787cf9cd 0x7be0f0000787cf9c

def z107 : W := mkw 0x000000001854a984 0x8000000001854a98 0xb0000000787cf9cc 0x0b0000000787cf9c

def z108 : W := mkw 0x1bf48ed36fa2f667 0x41bf48ed36fa2f66 0xdffc0ff67fe0fece 0xfdffc0ff67fe0fec

def z109 : W := mkw 0x49e4c4c300000000 0x049e4c4c30000000 0x01c0000000000000 0x001c000000000000

def z110 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0xee0f0c06787cc0cd 0x7ee0f0c06787cc0c

def z111 : W := mkw 0x2fbfdb0c7f7fa98c 0x82fbfdb0c7f7fa98 0xaffff3007fff380d 0xfaffff3007fff380

def z112 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x2033f0f9841f0731 0x82033f0f9841f073

def z113 : W := mkw 0x0000000010500000 0x0000000001050000 0xa0000000787c000c 0x0a0000000787c000

def z114 : W := mkw 0x5fffeffffed4ff87 0x85fffeffffed4ff8 0xfffffffffffcffcf 0xffffffffffffcffc

def z115 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x5fffffff8000c7f3 0xf5fffffff8000c7f

def z116 : W := mkw 0x1010001066805603 0x0101000106680560 0x0000000007800600 0x0000000000780060

def z117 : W := mkw 0x248fd10c117f0988 0x8248fd10c117f098 0x200ff00e007f01c1 0x0200ff00e007f01c

def z118 : W := mkw 0x0001212880000000 0x0000121288000000 0x000003f980000002 0x0000003f98000000

def z119 : W := mkw 0x00d4949345af5f73 0xe00d4949345af5f7 0xf1cc8c8fc7ffffff 0xbf1cc8c8fc7fffff

def z120 : W := mkw 0x1b700ed36e80f667 0x41b700ed36e80f66 0xdff00fffff80fffe 0xfdff00fffff80fff

def z121 : W := mkw 0x42412fef8804a984 0x842412fef8804a98 0x50000fff8000f9c2 0x050000fff8000f9c

def z122 : W := mkw 0x10113138ee8dff17 0xa10113138ee8dff1 0xb033f3f9ff9fff3f 0xdb033f3f9ff9fff3

def z123 : W := mkw 0x06ce8e8719f2e4e6 0x406ce8e8719f2e4e 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z124 : W := mkw 0x2dbfd10c777f0988 0x82dbfd10c777f098 0xaffff00e7fff01cd 0xfaffff00e7fff01c

def z125 : W := mkw 0x00112138c4041b11 0xa00112138c4041b1 0x903003f9c4003f36 0xd903003f9c4003f3

def z126 : W := mkw 0x29301000777b0008 0x029301000777b000 0xaff000007fff000c 0xfaff000007fff000

def z127 : W := mkw 0x0000000001220060 0x4000000000122006 0x20000000006301f0 0x020000000006301f

def z128 : W := mkw 0x0930000066000000 0x0093000006600000 0x8ff000007f80000c 0xf8ff000007f80000

def z129 : W := mkw 0x2dbff128f77f0918 0xa2dbff128f77f091 0xaffff009ffff013d 0xfaffff009ffff013

def z130 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x41cc8c8f83e0c0cb 0xb41cc8c8f83e0c0c

def z131 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0x8ff370007f9c000c 0xf8ff370007f9c000

def z132 : W := mkw 0x09313138e60d1b11 0xa09313138e60d1b1 0xbff3f3f9ff9f3f3f 0xfbff3f3f9ff9f3f3

def z133 : W := mkw 0x5fefefff8880f607 0x05fefefff8880f60 0x5fffffff8000fe03 0xf5fffffff8000fe0

def z134 : W := mkw 0x040b010c1854a984 0x8040b010c1854a98 0xb00f000e787cf9cd 0x0b00f000e787cf9c

def z135 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x80000000401c3800 0x080000000401c380

def z136 : W := mkw 0x00d4849345a25663 0x400d4849345a2566 0xf1fc8fffc7e3ffff 0xff1fc8fffc7e3fff

def z137 : W := mkw 0x44cfe5af81a24462 0x444cfe5af81a2446 0x71cffc8f87e3c7ff 0xb71cffc8f87e3c7f

def z138 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff089ffff073f 0xfbffff089ffff073

def z139 : W := mkw 0x0000100000090000 0x0000010000009000 0x2003f000001f0001 0x02003f000001f000

def z140 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x31c0808187e3c7fc 0x831c0808187e3c7f

def z141 : W := mkw 0x00c4848300000000 0x000c484830000000 0x71cc8c8f8060c1cf 0xb71cc8c8f8060c1c

def z142 : W := mkw 0x000000001850a084 0x0000000001850a08 0x000000003860c0c8 0x0000000003860c0c

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x700c0c0e0060c1cf 0x3700c0c0e0060c1c

def z144 : W := mkw 0x060b0b0c00000000 0x0060b0b0c0000000 0x7e0f0f0e0060c1cf 0x77e0f0f0e0060c1c

def z145 : W := mkw 0x1f6a0ec43ad0e486 0x01f6a0ec43ad0e48 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z146 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff08ff9ff83ff3f 0xffff08ff9ff83ff3

def z147 : W := mkw 0x060b2b2c80000000 0x0060b2b2c8000000 0x4e3fffff80000003 0xf4e3fffff8000000

def z148 : W := mkw 0x1b313b78ee0dbb15 0xa1b313b78ee0dbb1 0xbe33f3f9fc1f3f37 0xdbe33f3f9fc1f3f3

def z149 : W := mkw 0x1b300a506e80f607 0x01b300a506e80f60 0x9e3003707f80fe0c 0x49e3003707f80fe0

def z150 : W := mkw 0x49e4e4e381a24462 0x449e4e4e381a2446 0x01f0f0f187830630 0x801f0f0f18783063

def z151 : W := mkw 0x02010b0c0804a984 0x802010b0c0804a98 0x50000f0e0000f9c2 0x050000f0e0000f9c

def z152 : W := mkw 0x4deee4e380000000 0x04deee4e38000000 0x0ffff0f180000001 0xf0ffff0f18000000

def z153 : W := mkw 0x0000000001a24462 0x40000000001a2446 0x0000000003e0c0c8 0x00000000003e0c0c

def z154 : W := mkw 0x00c5a5ab81a24462 0x400c5a5ab81a2446 0x71ffffff87e3c7ff 0xf71ffffff87e3c7f

def z155 : W := mkw 0x4feecec700000000 0x04feecec70000000 0x4fcc8c8f80000003 0xb4fcc8c8f8000000

def z156 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x80337370401c3800 0x480337370401c380

def z157 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x41cc0c0603e0c0c8 0x241cc0c0603e0c0c

def z158 : W := mkw 0x197004d066805603 0x0197004d06680560 0x01f000f007800600 0x801f000f00780060

def z159 : W := mkw 0x20113138f77f1b19 0xa20113138f77f1b1 0xb033f3f9ffff3f3f 0xdb033f3f9ffff3f3

def z160 : W := mkw 0x1b713ff8ee8dff17 0xa1b713ff8ee8dff1 0xdff37ff07f9cfe0e 0xfdff37ff07f9cfe0

def z161 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x6fffffff806301f3 0xf6fffffff806301f

def z162 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033737000000000 0x4003373700000000

def z163 : W := mkw 0x5bf4eef3ee80f607 0x05bf4eef3ee80f60 0xdff0fff1ff80fe0e 0xfdff0fff1ff80fe0

def z164 : W := mkw 0x52412fff8880f607 0x052412fff8880f60 0x50000fff8000fe02 0x050000fff8000fe0

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000808984030737 0x9300080898403073

def z166 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0x4e0c0c063860c0c8 0x24e0c0c063860c0c

def z167 : W := mkw 0x4fefefef9850a084 0x04fefefef9850a08 0x4fffffffb860c0cb 0xf4fffffffb860c0c

def z168 : W := mkw 0x060b2b3c9854bb95 0xa060b2b3c9854bb9 0xfe0f0ffff87cffff 0x7fe0f0ffff87cfff

def z169 : W := mkw 0x048f810f117609e0 0xc048f810f117609e 0x200f800f807f01f1 0x0200f800f807f01f

def z170 : W := mkw 0x02010b0c0804a984 0x802010b0c0804a98 0x0000030000003800 0x0000003000000380

def z171 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x4e337fff80000002 0x44e337fff8000000

def z172 : W := mkw 0x2dfed48377fb446a 0x42dfed48377fb446 0xfffffc8fffffc7ff 0xffffffc8fffffc7f

def z173 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x0ffff37000000001 0xf0ffff3700000000

def z174 : W := mkw 0x00c4848300000000 0x000c484830000000 0x01c0808180000000 0x801c080818000000

def z175 : W := mkw 0x1f3b0b5c7e54bb85 0x81f3b0b5c7e54bb8 0xfe3f0f7e787cf9cf 0x7fe3f0f7e787cf9c

def z176 : W := mkw 0x1f7b0fdc6e80f607 0x01f7b0fdc6e80f60 0xdfff0ffe7f80fe0f 0xfdfff0ffe7f80fe0

def z177 : W := mkw 0x4feecec700000000 0x04feecec70000000 0x4fcc0c0600000000 0x24fcc0c060000000

def z178 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfffc0ffe7fe0ffcf 0xffffc0ffe7fe0ffc

def z179 : W := mkw 0x00013128800d0910 0xa00013128800d091 0x2033f3f9801f0133 0xd2033f3f9801f013

def z180 : W := mkw 0x20d4948377fb446a 0x420d4948377fb446 0xf1cc8c8fffffc7ff 0xbf1cc8c8fffffc7f

def z181 : W := mkw 0x0010001044001201 0x0001000104400120 0xb03083f9c4033f37 0xdb03083f9c4033f3

def z182 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xde300ff07800fe02 0x4de300ff07800fe0

def z183 : W := mkw 0x5fffefffee80f607 0x05fffefffee80f60 0xdfffffffff80fe0f 0xfdfffffffff80fe0

def z184 : W := mkw 0x4fefefef8800a004 0x04fefefef8800a00 0xdffffffff800f80f 0xfdffffffff800f80

def z185 : W := mkw 0x4defe5ef80000000 0x04defe5ef8000000 0x01fff0ff80000001 0x801fff0ff8000000

def z186 : W := mkw 0x468feb2f80000000 0x0468feb2f8000000 0x4e0fff0f80000003 0x74e0fff0f8000000

def z187 : W := mkw 0x00103030c4091211 0x200103030c409121 0xa033f0f1c41f0635 0xda033f0f1c41f063

def z188 : W := mkw 0x0010000044000000 0x0001000004400000 0x8030000044000004 0xd803000004400000

def z189 : W := mkw 0x1be48ec32ba2e466 0x41be48ec32ba2e46 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z190 : W := mkw 0x448fe12f80000000 0x0448fe12f8000000 0x000ff00f80000001 0x0000ff00f8000000

def z191 : W := mkw 0x301010107ffbf60f 0x0301010107ffbf60 0xb00000007ffffe0c 0x0b00000007ffffe0

def z192 : W := mkw 0x0dbff138c40d1b11 0xa0dbff138c40d1b1 0xbffff3f9c41f3f37 0xfbffff3f9c41f3f3

def z193 : W := mkw 0x0084800001a24462 0x40084800001a2446 0x31cc800007e3c7fd 0xb31cc800007e3c7f

def z194 : W := mkw 0x0dafe12880000000 0x00dafe1288000000 0x0ffff3f980000003 0xf0ffff3f98000000

def z195 : W := mkw 0x5f7b6ffcee80f607 0x05f7b6ffcee80f60 0xdff37ff07f80fe0e 0xfdff37ff07f80fe0

def z196 : W := mkw 0x4fefefef8804a984 0x84fefefef8804a98 0x5fffffff8000f9c3 0xf5fffffff8000f9c

def z197 : W := mkw 0x0dbec00066000000 0x00dbec0006600000 0x8ffff0007f80000d 0xf8ffff0007f80000

def z198 : W := mkw 0x000000001854a984 0x8000000001854a98 0xf00c0c0e787cf9cf 0x3f00c0c0e787cf9c

def z199 : W := mkw 0x040a000010500000 0x0040a00001050000 0x200f0000007c0001 0x0200f0000007c000

def z200 : W := mkw 0x29f4d48367ab446a 0x429f4d48367ab446 0x71fcfc8f87e3c7ff 0xb71fcfc8f87e3c7f

def z201 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb03003f0441f3f36 0xdb03003f0441f3f3

def z202 : W := mkw 0x193000106e80f607 0x0193000106e80f60 0x9ff000007f80fe0c 0xf9ff000007f80fe0

def z203 : W := mkw 0x1b600ec02a80e406 0x01b600ec02a80e40 0xdfc00f007b80f80e 0x7dfc00f007b80f80

def z204 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0xa1f3f000479f0005 0xda1f3f000479f000

def z205 : W := mkw 0x0040048000804402 0x0004004800080440 0x71c08c898783c73f 0xb71c08c898783c73

def z206 : W := mkw 0x2d3b7138f65d1b19 0xa2d3b7138f65d1b1 0x8e337370781c3800 0x48e337370781c380

def z207 : W := mkw 0x0001212880040900 0x8000121288004090 0xb033f3f9c01c3907 0xdb033f3f9c01c390

def z208 : W := mkw 0x448fe12f90540980 0x8448fe12f9054098 0x200ff00f807c01c1 0x0200ff00f807c01c

def z209 : W := mkw 0x0fafcb0c1854a984 0x80fafcb0c1854a98 0xffffff0e787cf9cf 0xfffffff0e787cf9c

def z210 : W := mkw 0x3dfed4d077fb560b 0x03dfed4d077fb560 0xaffff0f07fff060d 0xfaffff0f07fff060

def z211 : W := mkw 0x0b300a006e00a004 0x00b300a006e00a00 0xdff00f007f80f80e 0xfdff00f007f80f80

def z212 : W := mkw 0x101000106e80f607 0x0101000106e80f60 0x900000007f80fe0c 0x0900000007f80fe0

def z213 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x51cc0c8f83e0c7fa 0x251cc0c8f83e0c7f

def z214 : W := mkw 0x6fbffb6cf77b0008 0x06fbffb6cf77b000 0xaffff3707fff000d 0xfaffff3707fff000

def z215 : W := mkw 0x4001212f80000000 0x04001212f8000000 0x0000000f80000000 0x00000000f8000000

def z216 : W := mkw 0x0000001000041b11 0xa0000001000041b1 0x1000000000003f30 0x01000000000003f3

def z217 : W := mkw 0x09f4848367a24462 0x409f4848367a2446 0xfffc8c8fffe3c7ff 0xffffc8c8fffe3c7f

def z218 : W := mkw 0x004125bb80845f73 0xe004125bb80845f7 0x50000fff8000fff2 0x050000fff8000fff

def z219 : W := mkw 0x0010100044090000 0x0001010004409000 0xa033f000441f0005 0xda033f000441f000

def z220 : W := mkw 0x1b600ed02a80f607 0x01b600ed02a80f60 0x5fc00ff03b80fe0a 0x25fc00ff03b80fe0

def z221 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb0337378401c3907 0x5b0337378401c390

def z222 : W := mkw 0x0084800300000000 0x0008480030000000 0x000c800f80000001 0x0000c800f8000000

def z223 : W := mkw 0x02113b38cc0dbb15 0xa02113b38cc0dbb1 0xfe33fff9fc1fff3f 0xffe33fff9fc1fff3

def z224 : W := mkw 0x040b010c10540980 0x8040b010c1054098 0x200f000e007c01c1 0x0200f000e007c01c

def z225 : W := mkw 0x4be4eee380000000 0x04be4eee38000000 0x4ff0fff180000002 0xf4ff0fff18000000

def z226 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000008980000732 0x0100000898000073

def z227 : W := mkw 0x0000000001a24462 0x40000000001a2446 0x0000000007830630 0x0000000000783063

def z228 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xae0f030e787c39c1 0x4ae0f030e787c39c

def z229 : W := mkw 0x0930001066001201 0x0093000106600120 0x9ff003f07f803e0e 0xf9ff003f07f803e0

def z230 : W := mkw 0x248ff128917f0918 0xa248ff128917f091 0x200ff009807f0131 0x0200ff009807f013

def z231 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xa033f379c01f3931 0x4a033f379c01f393

def z232 : W := mkw 0x064b0f8c18d4ed86 0x8064b0f8c18d4ed8 0xffcf0f8e7ffcffcf 0xfffcf0f8e7ffcffc

def z233 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x5fffffff8780c60f 0xf5fffffff8780c60

def z234 : W := mkw 0x0930000066000000 0x0093000006600000 0x8e30000078000000 0x48e3000007800000

def z235 : W := mkw 0x00d5b5bbc40d1b11 0xa00d5b5bbc40d1b1 0xf1ffffffc41f3f37 0xff1ffffffc41f3f3

def z236 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x61cc8c0607e3c0cd 0xb61cc8c0607e3c0c

def z237 : W := mkw 0x0084800001220000 0x0008480000122000 0x200c800000630001 0x0200c80000063000

def z238 : W := mkw 0x1f3b0b5c7e54bb85 0x81f3b0b5c7e54bb8 0x8e330370781c3800 0x48e330370781c380

def z239 : W := mkw 0x29b4d000777b0008 0x029b4d000777b000 0xa1f0f0007fff000c 0x8a1f0f0007fff000

def z240 : W := mkw 0x02c58f8f09a6ede6 0xc02c58f8f09a6ede 0x71cc8f8f87e3ffff 0xb71cc8f8f87e3fff

def z241 : W := mkw 0x4fffffffc40d1b11 0xa4fffffffc40d1b1 0xcfffffffc01c3803 0xfcfffffffc01c380

def z242 : W := mkw 0x0001010800040900 0x8000101080004090 0xb0030308401c3907 0x5b0030308401c390

def z243 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x8033f3f1c41f3e30 0xc8033f3f1c41f3e3

def z244 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x8ff003f07f803e00 0xc8ff003f07f803e0

def z245 : W := mkw 0x12400ed00880f607 0x012400ed00880f60 0x51c00ff00780fe0e 0xb51c00ff00780fe0

def z246 : W := mkw 0x464b2fef80000000 0x0464b2fef8000000 0x4e0f0fff80000003 0x74e0f0fff8000000

def z247 : W := mkw 0x49e4e4e381a24462 0x449e4e4e381a2446 0x71fcfcff87e3c7ff 0xb71fcfcff87e3c7f

def z248 : W := mkw 0x00013128800d0910 0xa00013128800d091 0x2003f009801f0131 0x02003f009801f013

def z249 : W := mkw 0x1b700ed07ed4ff87 0x81b700ed07ed4ff8 0xfff00ff07ffcffce 0xffff00ff07ffcffc

def z250 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x4fffffff83e0c0cb 0xf4fffffff83e0c0c

def z251 : W := mkw 0x061b1b0c5c5da984 0x8061b1b0c5c5da98 0xfe3fff0e7c7ff9cf 0xffe3fff0e7c7ff9c

def z252 : W := mkw 0x2f3b5b0c7e5da98c 0x82f3b5b0c7e5da98 0x8e337300781c3800 0x48e337300781c380

def z253 : W := mkw 0x648ff12f917b0008 0x0648ff12f917b000 0x200ff00f807f0001 0x0200ff00f807f000

def z254 : W := mkw 0x4fffefffc4001201 0x04fffefffc400120 0xdfffffffc4003e07 0xfdfffffffc4003e0

def z255 : W := mkw 0x1b712ff8ee80f607 0x01b712ff8ee80f60 0xdff3fff9ff80fe0f 0xfdff3fff9ff80fe0

def z256 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x6fffffff87e3000f 0xf6fffffff87e3000

def z257 : W := mkw 0x4fefffef800d0910 0xa4fefffef800d091 0x6fffffff801f0133 0xf6fffffff801f013

def z258 : W := mkw 0x1f7b0fdc7ed4ff87 0x81f7b0fdc7ed4ff8 0xdff30ff07f9cfe0e 0xfdff30ff07f9cfe0

def z259 : W := mkw 0x00c4848300804462 0x400c484830080446 0x51cc8c8f8000c7f3 0xb51cc8c8f8000c7f

def z260 : W := mkw 0x5ffeced76e80f607 0x05ffeced76e80f60 0xdffc0ff67f80fe0e 0xfdffc0ff67f80fe0

def z261 : W := mkw 0x104004d000805603 0x0104004d00080560 0x000000f000000600 0x0000000f00000060

def z262 : W := mkw 0x20101000672b0008 0x020101000672b000 0x0000000007830000 0x0000000000783000

def z263 : W := mkw 0x00c5a5bb81a65f73 0xe00c5a5bb81a65f7 0x71cc8fff87e3ffff 0xb71cc8fff87e3fff

def z264 : W := mkw 0x19f484d367a25663 0x419f484d367a2566 0x01f080f187830630 0x801f080f18783063

def z265 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x7fffffff84030737 0xf7fffffff8403073

def z266 : W := mkw 0x4be5efef80000000 0x04be5efef8000000 0x41f0ffff80000002 0x841f0ffff8000000

def z267 : W := mkw 0x048ec00000000000 0x0048ec0000000000 0x000ff00000000001 0x0000ff0000000000

def z268 : W := mkw 0x5b712fffee80f607 0x05b712fffee80f60 0xdff00fffff80fe0e 0xfdff00fffff80fe0

def z269 : W := mkw 0x00001000000d0910 0xa00001000000d091 0x20000000001f0130 0x020000000001f013

def z270 : W := mkw 0x0040048000804402 0x0004004800080440 0x01c0008007800600 0x801c000800780060

def z271 : W := mkw 0x0011011844041b01 0x80011011844041b0 0xb03303f8441c3f07 0xdb03303f8441c3f0

def z272 : W := mkw 0x061b3b3cdc5dbb95 0xa061b3b3cdc5dbb9 0xfe3ffffffc7fffff 0xffe3ffffffc7ffff

def z273 : W := mkw 0x248ed003117b0068 0x4248ed003117b006 0x200ff00f807f01f1 0x0200ff00f807f01f

def z274 : W := mkw 0x040a000000000000 0x0040a00000000000 0x0e0f000000000001 0x70e0f00000000000

def z275 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xfffffc0e7fffc1cf 0xffffffc0e7fffc1c

def z276 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0xae3f7000787c000d 0x7ae3f7000787c000

def z277 : W := mkw 0x4920606080000000 0x0492060608000000 0x0030707000000000 0x0003070700000000

def z278 : W := mkw 0x040a000010500000 0x0040a00001050000 0x0e0c000038600008 0x20e0c00003860000

def z279 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x1030f3f984033f32 0x81030f3f984033f3

def z280 : W := mkw 0x12412ff88884ff17 0xa12412ff88884ff1 0x50000ff98000ff32 0x050000ff98000ff3

def z281 : W := mkw 0x2dfed483777b0008 0x02dfed483777b000 0xeffffc8fffff000f 0xfeffffc8fffff000

def z282 : W := mkw 0x29b5f138e72f1b19 0xa29b5f138e72f1b1 0xb1f3f3f9c79f3f37 0xdb1f3f3f9c79f3f3

def z283 : W := mkw 0x0000000000040900 0x8000000000004090 0xb0000000401c3904 0x0b0000000401c390

def z284 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0x6e0f0c0e387cc1c9 0x26e0f0c0e387cc1c

def z285 : W := mkw 0x24ced48311fb446a 0x424ced48311fb446 0x71cffc8f87ffc7ff 0xb71cffc8f87ffc7f

def z286 : W := mkw 0x02010b0c0804a984 0x802010b0c0804a98 0xde000f0e7800f9ce 0x7de000f0e7800f9c

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000008004000606 0x9100000800400060

def z288 : W := mkw 0x0000203080001211 0x2000020308000121 0x000000f180000630 0x0000000f18000063

def z289 : W := mkw 0x06ce8e8719f2e4e6 0x406ce8e8719f2e4e 0x7fcc8c8fbfe3c7ff 0xb7fcc8c8fbfe3c7f

def z290 : W := mkw 0x42412fff80041b11 0xa42412fff80041b1 0x50000fff80003f32 0x050000fff80003f3

def z291 : W := mkw 0x040b010c00000000 0x0040b010c0000000 0x000f000e00000001 0x0000f000e0000000

def z292 : W := mkw 0x4feecec700000000 0x04feecec70000000 0x4ffc0ff600000002 0xf4ffc0ff60000000

def z293 : W := mkw 0x0040048000804402 0x0004004800080440 0x50000c800000c602 0x050000c800000c60

def z294 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xa033f370441f3805 0xda033f370441f380

def z295 : W := mkw 0x2010100076590008 0x0201010007659000 0x80000000781c0000 0x080000000781c000

def z296 : W := mkw 0x0f3b0b0c7e54a984 0x80f3b0b0c7e54a98 0xffff0f0e7ffcf9cf 0xfffff0f0e7ffcf9c

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000808184030630 0x8000080818403063

def z298 : W := mkw 0x2fbffb3cff7fbb9d 0xa2fbffb3cff7fbb9 0xffffffffffffffff 0xffffffffffffffff

def z299 : W := mkw 0x0001010800000000 0x0000101080000000 0x0003030800000003 0x5000303080000000

def z300 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc0c0607e3c7fc 0x271cc0c0607e3c7f

def z301 : W := mkw 0x0000000001a24462 0x40000000001a2446 0x3000808987e3c7ff 0x93000808987e3c7f

def z302 : W := mkw 0x064b0f8f18d4ede6 0xc064b0f8f18d4ede 0xfe0f0f8ff87cffff 0x7fe0f0f8ff87cfff

def z303 : W := mkw 0x249ed000557b0008 0x0249ed000557b000 0xa03ff000447f0005 0xda03ff000447f000

def z304 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fff7f7600000000 0x64fff7f760000000

def z305 : W := mkw 0x448fe12f80000000 0x0448fe12f8000000 0x003ff3ff80000003 0xd003ff3ff8000000

def z306 : W := mkw 0x42400ec700000000 0x042400ec70000000 0x40000c0600000000 0x040000c060000000

def z307 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0xfe3ffffff87cf9cf 0xffe3ffffff87cf9c

def z308 : W := mkw 0x048e800011720000 0x0048e80001172000 0xafcf80007fff000d 0xfafcf80007fff000

def z309 : W := mkw 0x19f484d367a25663 0x419f484d367a2566 0x71fc8cff87e3c7ff 0xb71fc8cff87e3c7f

def z310 : W := mkw 0x468feb2f9854a984 0x8468feb2f9854a98 0xfe0fff0ff87cf9cf 0x7fe0fff0ff87cf9c

def z311 : W := mkw 0x49f4f4f3c4091211 0x249f4f4f3c409121 0x01f0f0f184030630 0x801f0f0f18403063

def z312 : W := mkw 0x040a000010500000 0x0040a00001050000 0xfe0f0c0e787cc1cf 0x7fe0f0c0e787cc1c

def z313 : W := mkw 0x2dbec00077720008 0x02dbec0007772000 0x8ffc00007fe0000c 0xf8ffc00007fe0000

def z314 : W := mkw 0x4fefefef99f6ede6 0xc4fefefef99f6ede 0xffffffffffffffff 0xffffffffffffffff

def z315 : W := mkw 0x20101000777b0008 0x020101000777b000 0xa033f0007fff000d 0xda033f0007fff000

def z316 : W := mkw 0x1930005066001201 0x0193000506600120 0x0030007000000000 0x0003000700000000

def z317 : W := mkw 0x2084d000012b0008 0x02084d000012b000 0x0000f00000030000 0x00000f0000003000

def z318 : W := mkw 0x00013138800d1b11 0xa00013138800d1b1 0x3003f3f9801f3f33 0x03003f3f9801f3f3

def z319 : W := mkw 0x4dafe12f80000000 0x04dafe12f8000000 0x0ffff00f80000001 0xf0ffff00f8000000

def z320 : W := mkw 0x6fefffef917b0008 0x06fefffef917b000 0x6fffffff807f0003 0xf6fffffff807f000

def z321 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb00003f9c41f3f36 0x0b00003f9c41f3f3

def z322 : W := mkw 0x00c4848300000000 0x000c484830000000 0x41cc0c0600000000 0x241cc0c060000000

def z323 : W := mkw 0x02000a040800a084 0x002000a040800a08 0x40000c060000c0c0 0x040000c060000c0c

def z324 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xce0f0f06787cf8c8 0x6ce0f0f06787cf8c

def z325 : W := mkw 0x00013128800d0910 0xa00013128800d091 0x00037000001c0000 0x000037000001c000

def z326 : W := mkw 0x3fbeda507f7bb20d 0x03fbeda507f7bb20 0xaffff3707fff380d 0xfaffff3707fff380

def z327 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0x8ff0f0007f83000c 0xf8ff0f0007f83000

def z328 : W := mkw 0x0000000010540980 0x8000000001054098 0x20000000007c01c0 0x020000000007c01c

def z329 : W := mkw 0x0010001044001201 0x0001000104400120 0x9000000044003e04 0x09000000044003e0

def z330 : W := mkw 0x201010007f7fa98c 0x8201010007f7fa98 0xb00000007ffff9cc 0x0b00000007ffff9c

def z331 : W := mkw 0x0b600ec00800a004 0x00b600ec00800a00 0xdff00ff07800f80e 0xfdff00ff07800f80

def z332 : W := mkw 0x0000000001a24462 0x40000000001a2446 0x700c0c0e07e3c7ff 0x3700c0c0e07e3c7f

def z333 : W := mkw 0x6dbff12ff77b0008 0x06dbff12ff77b000 0xaffff00fffff000d 0xfaffff00fffff000

def z334 : W := mkw 0x06dfbfbfddfffff7 0xe06dfbfbfddfffff 0xffffffffffffffff 0xffffffffffffffff

def z335 : W := mkw 0x0010100044090000 0x0001010004409000 0x0030f00004030000 0x80030f0000403000

def z336 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xafcc00007fff000c 0x2afcc00007fff000

def z337 : W := mkw 0x2fafcb0c3b76a98c 0x82fafcb0c3b76a98 0xffcf0f0e7bfcf9cf 0x7ffcf0f0e7bfcf9c

def z338 : W := mkw 0x06cf8f8f00000000 0x006cf8f8f0000000 0x4fcf8f8f80000003 0xf4fcf8f8f8000000

def z339 : W := mkw 0x041b3138d45d1b11 0xa041b3138d45d1b1 0xbe3ff3f9fc7f3f3f 0xfbe3ff3f9fc7f3f3

def z340 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x51cc0c8607e0c6ce 0xb51cc0c8607e0c6c

def z341 : W := mkw 0x2f3b5b0c7e5da98c 0x82f3b5b0c7e5da98 0xfe3f7f0e787cf9cf 0x7fe3f7f0e787cf9c

def z342 : W := mkw 0x101000106e00b205 0x0101000106e00b20 0x8000000078003800 0x0800000007800380

def z343 : W := mkw 0x061b3b3cdc5dbb95 0xa061b3b3cdc5dbb9 0x8e337370781c3800 0x48e337370781c380

def z344 : W := mkw 0x49e5e5eb80000000 0x049e5e5eb8000000 0x01f3f3f980000003 0xd01f3f3f98000000

def z345 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fcc0fff80000002 0x24fcc0fff8000000

def z346 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xce0f0f0e781c3803 0x7ce0f0f0e781c380

def z347 : W := mkw 0x1b712ff8ee84ff17 0xa1b712ff8ee84ff1 0xdff00ff9ff80ff3e 0xfdff00ff9ff80ff3

def z348 : W := mkw 0x101000106fa2f667 0x4101000106fa2f66 0xb00000007fe3fffc 0x0b00000007fe3fff

def z349 : W := mkw 0x060b0b0c19f6ede6 0xc060b0b0c19f6ede 0xfe0f0f0e7fffffff 0x7fe0f0f0e7ffffff

def z350 : W := mkw 0x5fefefefaa80e406 0x05fefefefaa80e40 0x4fffffffbb80c00b 0xf4fffffffbb80c00

def z351 : W := mkw 0x4f3b7b7cc40d1b11 0xa4f3b7b7cc40d1b1 0x8e337370401c3800 0x48e337370401c380

def z352 : W := mkw 0x0084800001220000 0x0008480000122000 0x21cc800007e3000d 0xb21cc800007e3000

def z353 : W := mkw 0x060a0a001850a004 0x0060a0a001850a00 0xfe0f0f00787cf80f 0x7fe0f0f00787cf80

def z354 : W := mkw 0x464b2fef9854a984 0x8464b2fef9854a98 0xfe0f0ffff87cf9cf 0x7fe0f0ffff87cf9c

def z355 : W := mkw 0x00113138c5af5f73 0xe00113138c5af5f7 0xb033f3f9c7ffffff 0xdb033f3f9c7fffff

def z356 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x51c08c8f8783c7f2 0x851c08c8f8783c7f

def z357 : W := mkw 0x2fbfdb0c777b0008 0x02fbfdb0c777b000 0xefffff0e7fff000f 0xfefffff0e7fff000

def z358 : W := mkw 0x00113128c40d0910 0xa00113128c40d091 0xa033f009c41f0135 0xda033f009c41f013

def z359 : W := mkw 0x1b600ec02a80e406 0x01b600ec02a80e40 0x5fc00c803f80c60e 0xb5fc00c803f80c60

def z360 : W := mkw 0x2dbed010777b1209 0x02dbed010777b120 0xbffff3f07fff3e0f 0xfbffff3f07fff3e0

def z361 : W := mkw 0x2dbed010777f1b19 0xa2dbed010777f1b1 0xbffff0007fff3f3d 0xfbffff0007fff3f3

def z362 : W := mkw 0x12400ed30880f667 0x412400ed30880f66 0x50000fff8000fff2 0x050000fff8000fff

def z363 : W := mkw 0x44cfe5af80000000 0x044cfe5af8000000 0x41cffc8f80000003 0xb41cffc8f8000000

def z364 : W := mkw 0x2daec00033720008 0x02daec0003372000 0x2fcc80003fe3000d 0xb2fcc80003fe3000

def z365 : W := mkw 0x0084800301220060 0x4008480030122006 0x300c808f846307f7 0x9300c808f846307f

def z366 : W := mkw 0x249ff138d57f1b19 0xa249ff138d57f1b1 0xb03ff3f9c47f3f37 0xdb03ff3f9c47f3f3

def z367 : W := mkw 0x001010105c5dbb95 0xa001010105c5dbb9 0xb00000007c7ffffc 0x0b00000007c7ffff

def z368 : W := mkw 0x4fffffefc4090000 0x04fffffefc409000 0xefffffffc41f0007 0xfefffffffc41f000

def z369 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x0ff3f3f180000000 0xc0ff3f3f18000000

def z370 : W := mkw 0x2d3b7138f65d1b19 0xa2d3b7138f65d1b1 0xbe33f3f9fc1f3f37 0xdbe33f3f9fc1f3f3

def z371 : W := mkw 0x5fffefffefa2f667 0x45fffefffefa2f66 0xffffffffffe3ffff 0xfffffffffffe3fff

def z372 : W := mkw 0x0b200a4000000000 0x00b200a400000000 0x0e30037000000000 0x40e3003700000000

def z373 : W := mkw 0x0be48ec301a24462 0x40be48ec301a2446 0x7ffc8fff87e3c7ff 0xf7ffc8fff87e3c7f

def z374 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb033f000441f3f35 0xdb033f000441f3f3

def z375 : W := mkw 0x2daec00033720008 0x02daec0003372000 0x0ffff0003be00009 0xf0ffff0003be0000

def z376 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xae3ff000787f0001 0x4ae3ff000787f000

def z377 : W := mkw 0x6fffffefe72b0008 0x06fffffefe72b000 0x4fffffff87830003 0xf4fffffff8783000

def z378 : W := mkw 0x69f4f4e3e72b0008 0x069f4f4e3e72b000 0x01f0f0f187830000 0x801f0f0f18783000

def z379 : W := mkw 0x0000000000000000 0x0000000000000000 0x9000030040003806 0x5900003004000380

def z380 : W := mkw 0x2daec00033720008 0x02daec0003372000 0xafcf00007bfc000d 0x7afcf00007bfc000

def z381 : W := mkw 0x040b010810540900 0x8040b01081054090 0xbe0f0308787c390f 0x7be0f0308787c390

def z382 : W := mkw 0x0d2a400000000000 0x00d2a40000000000 0x0e33700000000000 0x40e3370000000000

def z383 : W := mkw 0x4fefefef90500000 0x04fefefef9050000 0xeffffffff87c000f 0xfeffffffff87c000

def z384 : W := mkw 0x0001213880041b11 0xa0001213880041b1 0x0000037000003800 0x0000003700000380

def z385 : W := mkw 0x6fefefefb3720008 0x06fefefefb372000 0x4fffffffbbe0000b 0xf4fffffffbbe0000

def z386 : W := mkw 0x6dfef4e3f77b0008 0x06dfef4e3f77b000 0xaffff0f1ffff000d 0xfaffff0f1ffff000

def z387 : W := mkw 0x3dbed0107ffbf60f 0x03dbed0107ffbf60 0xbffff0007ffffe0d 0xfbffff0007ffffe0

def z388 : W := mkw 0x1b600ed00880f607 0x01b600ed00880f60 0x5ff00ff00000fe02 0xf5ff00ff00000fe0

def z389 : W := mkw 0x2dbfd108777f0908 0x82dbfd108777f090 0xbffff3087fff390f 0xfbffff3087fff390

def z390 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xbe030300787cf9cc 0x4be030300787cf9c

def z391 : W := mkw 0x060b0b0c10500000 0x0060b0b0c1050000 0xee0f0f0e787c000f 0x7ee0f0f0e787c000

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x700c8c8f8463c7ff 0xb700c8c8f8463c7f

def z393 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x31c0808987830737 0x931c080898783073

def z394 : W := mkw 0x1b701ed06e8dff17 0xa1b701ed06e8dff1 0xfff00ff07f9fff3e 0xffff00ff07f9fff3

def z395 : W := mkw 0x448ff12f800d0910 0xa448ff12f800d091 0x200ff00f801f0131 0x0200ff00f801f013

def z396 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x4e3f7f7e00000003 0x74e3f7f7e0000000

def z397 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x0e3ff37f80000001 0x40e3ff37f8000000

def z398 : W := mkw 0x2dbed00077fb446a 0x42dbed00077fb446 0xbffff0007fffc7fd 0xfbffff0007fffc7f

def z399 : W := mkw 0x0930100066090000 0x0093010006609000 0xaff3f0007f9f000d 0xfaff3f0007f9f000

def z400 : W := mkw 0x1f6b0fcc3ad4ed86 0x81f6b0fcc3ad4ed8 0xffcf0f0e7bfcf9cf 0x7ffcf0f0e7bfcf9c

def z401 : W := mkw 0x4feecec700000000 0x04feecec70000000 0x4ffffc0600000001 0xf4ffffc060000000

def z402 : W := mkw 0x2fffdf8f7fffedee 0xc2fffdf8f7fffede 0xffffff8fffffffff 0xfffffff8ffffffff

def z403 : W := mkw 0x42412fef80804462 0x442412fef8080446 0x50000fff8000c7f2 0x050000fff8000c7f

def z404 : W := mkw 0x4084e02380000000 0x04084e0238000000 0x0000f00180000000 0x00000f0018000000

def z405 : W := mkw 0x0f6b0fcc1854a984 0x80f6b0fcc1854a98 0xffff0ffe787cf9cf 0xfffff0ffe787cf9c

def z406 : W := mkw 0x0084800301a24462 0x40084800301a2446 0x300c800f87e3c7fd 0x0300c800f87e3c7f

def z407 : W := mkw 0x04cf858f11f64de2 0xc04cf858f11f64de 0x71cf8c8f87ffc7ff 0xb71cf8c8f87ffc7f

def z408 : W := mkw 0x0001010c00040980 0x80001010c0004098 0x0000000e000001c0 0x00000000e000001c

def z409 : W := mkw 0x241a1000777b0008 0x0241a1000777b000 0xae0f00007fff000d 0x7ae0f00007fff000

def z410 : W := mkw 0x02000a001854a984 0x802000a001854a98 0xfe000f00787cf9ce 0x7fe000f00787cf9c

def z411 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x41fcfcff80000003 0xb41fcfcff8000000

def z412 : W := mkw 0x02012b3c8804bb95 0xa02012b3c8804bb9 0x50000fff8000fff2 0x050000fff8000fff

def z413 : W := mkw 0x0920000000000000 0x0092000000000000 0x0ff0000000000000 0xf0ff000000000000

def z414 : W := mkw 0x0050049044805603 0x0005004904480560 0xd1f00ff04780fe0e 0xfd1f00ff04780fe0

def z415 : W := mkw 0x02010b0c0804a984 0x802010b0c0804a98 0xf0030f0e401cf9c7 0x5f0030f0e401cf9c

def z416 : W := mkw 0x197004d066805603 0x0197004d06680560 0x8ff000f07f80060c 0xf8ff000f07f80060

def z417 : W := mkw 0x4b612fef80000000 0x04b612fef8000000 0x4ff00fff80000002 0xf4ff00fff8000000

def z418 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c000000780000c 0xb01c000000780000

def z419 : W := mkw 0x3f3a5a507e59b20d 0x03f3a5a507e59b20 0x8e337370781c3800 0x48e337370781c380

def z420 : W := mkw 0x060b0b0c0800a004 0x0060b0b0c0800a00 0xde0f0f0e7800f80f 0x7de0f0f0e7800f80

def z421 : W := mkw 0x20101010777f1b19 0xa20101010777f1b1 0xb00000007fff3f3c 0x0b00000007fff3f3

def z422 : W := mkw 0x0b700ec066000000 0x00b700ec06600000 0xcff00ff07f80000e 0xfcff00ff07f80000

def z423 : W := mkw 0x0040048300804462 0x4004004830080446 0x40000c060000c0c0 0x040000c060000c0c

def z424 : W := mkw 0x02010b0c1854a984 0x802010b0c1854a98 0xf0000f0e787cf9ce 0x0f0000f0e787cf9c

def z425 : W := mkw 0x1f7b3ffcfeddff97 0xa1f7b3ffcfeddff9 0xffffffffffffffff 0xffffffffffffffff

def z426 : W := mkw 0x101010106e8dff17 0xa101010106e8dff1 0xb00000007f9fff3c 0x0b00000007f9fff3

def z427 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x21cc808f87e307f1 0x821cc808f87e307f

def z428 : W := mkw 0x041a100054590000 0x0041a10005459000 0xae3ff0007c7f000d 0xfae3ff0007c7f000

def z429 : W := mkw 0x2dbff138f77f1b19 0xa2dbff138f77f1b1 0xaffff3707fff380d 0xfaffff3707fff380

def z430 : W := mkw 0x00d4b4b3c5ab5673 0x600d4b4b3c5ab567 0x71fcfcff87e3c7ff 0xb71fcfcff87e3c7f

def z431 : W := mkw 0x00013128800d0910 0xa00013128800d091 0x3003f089841f0737 0x93003f089841f073

def z432 : W := mkw 0x2dbed00076590008 0x02dbed0007659000 0x8ffff000781c0001 0xf8ffff000781c000

def z433 : W := mkw 0x0dbed00044090000 0x00dbed0004409000 0xaffff000441f0005 0xfaffff000441f000

def z434 : W := mkw 0x404024e380000000 0x0404024e38000000 0x000000f180000000 0x0000000f18000000

def z435 : W := mkw 0x00949000452b0000 0x000949000452b000 0xa1fff00047ff000d 0xfa1fff00047ff000

def z436 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fcffc0f80000001 0x24fcffc0f8000000

def z437 : W := mkw 0x0001212880040910 0xa000121288004091 0x0000000980000130 0x0000000098000013

def z438 : W := mkw 0x060b0b0c1850a084 0x0060b0b0c1850a08 0x4e0f0f0e3860c0cb 0x74e0f0f0e3860c0c

def z439 : W := mkw 0x4f2b6b6c9854a984 0x84f2b6b6c9854a98 0xfe3f7f7e787cf9cf 0x7fe3f7f7e787cf9c

def z440 : W := mkw 0x0001010800040900 0x8000101080004090 0x80030300401c3800 0x480030300401c380

def z441 : W := mkw 0x5fffffffee8dff17 0xa5fffffffee8dff1 0xffffffffff9fff3f 0xfffffffffff9fff3

def z442 : W := mkw 0x161b0b1c7ed4ff87 0x8161b0b1c7ed4ff8 0xfe0f0f0e7ffcffcf 0x7fe0f0f0e7ffcffc

def z443 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f8f8ffc7fffff 0xffe0f8f8ffc7ffff

def z444 : W := mkw 0x0084800001220000 0x0008480000122000 0x31cc808987e3073f 0xb31cc808987e3073

def z445 : W := mkw 0x0000202080000000 0x0000020208000000 0x0030f0f180000000 0x80030f0f18000000

def z446 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x700c8c8f8063c7f3 0x0700c8c8f8063c7f

def z447 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0x0e00000038000000 0x00e0000003800000

def z448 : W := mkw 0x1bf5bffbefafff77 0xe1bf5bffbefafff7 0xffffffffffffffff 0xffffffffffffffff

def z449 : W := mkw 0x061b3b3cdc5dbb95 0xa061b3b3cdc5dbb9 0xbe33f3f9fc1f3f37 0xdbe33f3f9fc1f3f3

def z450 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x8033f3f9c01c3803 0xd8033f3f9c01c380

def z451 : W := mkw 0x005135bbc48d5f73 0xe005135bbc48d5f7 0xf033ffffc41ffff7 0xdf033ffffc41ffff

def z452 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb003f009c41f3f35 0x0b003f009c41f3f3

def z453 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xcff00f707b80f808 0x6cff00f707b80f80

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000800000107 0x1300000080000010

def z455 : W := mkw 0x0040048000000000 0x0004004800000000 0x41c00c8000000002 0xb41c00c800000000

def z456 : W := mkw 0x1b700ed066805603 0x01b700ed06680560 0x4ff00ff007800602 0xf4ff00ff00780060

def z457 : W := mkw 0x02400ec000000000 0x002400ec00000000 0x40000ff000000002 0x040000ff00000000

def z458 : W := mkw 0x6ffffffff77f1b19 0xa6ffffffff77f1b1 0xffffffffffff3f3f 0xfffffffffffff3f3

def z459 : W := mkw 0x12500ed04c80f607 0x012500ed04c80f60 0xd0300ff04400fe06 0xdd0300ff04400fe0

def z460 : W := mkw 0x00c4848301220000 0x000c484830122000 0x61cc8c8f87e3000f 0xb61cc8c8f87e3000

def z461 : W := mkw 0x3b701ed07ffbf60f 0x03b701ed07ffbf60 0xfff00ff07ffffe0e 0xffff00ff07ffffe0

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000800980030131 0x0200080098003013

def z463 : W := mkw 0x249ed000777b0008 0x0249ed000777b000 0xa00ff0007fff000d 0x0a00ff0007fff000

def z464 : W := mkw 0x2dfff5bbf7ff5f7b 0xe2dfff5bbf7ff5f7 0xffffffffffffffff 0xffffffffffffffff

def z465 : W := mkw 0x2dbff128f77b0008 0x02dbff128f77b000 0xaffff3f9ffff000f 0xfaffff3f9ffff000

def z466 : W := mkw 0x3fffdfdc7fffff8f 0x83fffdfdc7fffff8 0xfffffffe7fffffcf 0xffffffffe7fffffc

def z467 : W := mkw 0x6f3b7b6cf6590008 0x06f3b7b6cf659000 0x8e337370781c0000 0x48e337370781c000

def z468 : W := mkw 0x10d484936fa2f667 0x410d484936fa2f66 0xf1cc8c8fffe3ffff 0xbf1cc8c8fffe3fff

def z469 : W := mkw 0x3ffffff8ffffff1f 0xa3ffffff8ffffff1 0xfffffff9ffffff3f 0xffffffff9ffffff3

def z470 : W := mkw 0x0001213880041b11 0xa0001213880041b1 0x300083f984033f37 0x9300083f984033f3

def z471 : W := mkw 0x0daec00001220000 0x00daec0000122000 0x2ffff00007e3000d 0xf2ffff00007e3000

def z472 : W := mkw 0x4f3b7b7cc40d1b11 0xa4f3b7b7cc40d1b1 0xbe33f3f9c41f3f37 0xdbe33f3f9c41f3f3

def z473 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8fff70007bfc0008 0x68fff70007bfc000

def z474 : W := mkw 0x6fffffeff6590008 0x06fffffeff659000 0xcffffffff81c0003 0xfcffffffff81c000

def z475 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0xae33f0007c1f0005 0xdae33f0007c1f000

def z476 : W := mkw 0x060b0b0c00000000 0x0060b0b0c0000000 0x0e03030000000000 0x40e0303000000000

def z477 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x21fff00007ff0001 0x821fff00007ff000

def z478 : W := mkw 0x2dfed48377fb446a 0x42dfed48377fb446 0xeffffc067fffc0cd 0xfeffffc067fffc0c

def z479 : W := mkw 0x42012b6c80000000 0x042012b6c8000000 0x0000037000000000 0x0000003700000000

def z480 : W := mkw 0x4fefcfcf00000000 0x04fefcfcf0000000 0x4fcf0f0e00000003 0x74fcf0f0e0000000

def z481 : W := mkw 0x2fbeda047f7ba08c 0x02fbeda047f7ba08 0xeffffc067fffc0cd 0xfeffffc067fffc0c

def z482 : W := mkw 0x1b700ed06fa2f667 0x41b700ed06fa2f66 0xfff00ff07fe3fffe 0xffff00ff07fe3fff

def z483 : W := mkw 0x0010000066000000 0x0001000006600000 0x800000007f80000c 0x0800000007f80000

def z484 : W := mkw 0x3ffedec07ffbe40e 0x03ffedec07ffbe40 0xeffffc007fffc00d 0xfeffffc007fffc00

def z485 : W := mkw 0x101000106e80f607 0x0101000106e80f60 0x903003f07f80fe0e 0xd903003f07f80fe0

def z486 : W := mkw 0x09b4800067220000 0x009b480006722000 0xaffc80007fe3000d 0xfaffc80007fe3000

def z487 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x51c08c818783c63e 0xb51c08c818783c63

def z488 : W := mkw 0x7ffffffffffbf60f 0x07ffffffffffbf60 0xfffffffffffffe0f 0xffffffffffffffe0

def z489 : W := mkw 0x12400ec00880e406 0x012400ec00880e40 0x40000c000000c000 0x040000c000000c00

def z490 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000c0e0000c1c2 0x050000c0e0000c1c

def z491 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x8ff003707f80380c 0xf8ff003707f80380

def z492 : W := mkw 0x061b3b3cc40d1b11 0xa061b3b3cc40d1b1 0xfe3fffffc41f3f37 0xffe3fffffc41f3f3

def z493 : W := mkw 0x0040048000804402 0x0004004800080440 0x41c00c000380c008 0x241c00c000380c00

def z494 : W := mkw 0x02000a000800a004 0x002000a000800a00 0x50000f000000f802 0x050000f000000f80

def z495 : W := mkw 0x00103030c4091211 0x200103030c409121 0x0030707000000000 0x0003070700000000

def z496 : W := mkw 0x197004d066805603 0x0197004d06680560 0x91f003f047803e06 0xd91f003f047803e0

def z497 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdfc00c007f80fe0c 0x2dfc00c007f80fe0

def z498 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x51f00ff00780fe02 0x851f00ff00780fe0

def z499 : W := mkw 0x1b710fd86e84ff07 0x81b710fd86e84ff0 0xfff30ff87f9cff0f 0xffff30ff87f9cff0

def z500 : W := mkw 0x060a0a0400000000 0x0060a0a040000000 0x4e0c0c0600000000 0x24e0c0c060000000

def z501 : W := mkw 0x2dbed003777b0068 0x42dbed003777b006 0xaffff00fffff01fd 0xfaffff00fffff01f

def z502 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e0000007800000c 0x78e0000007800000

def z503 : W := mkw 0x00013128800d0910 0xa00013128800d091 0xb003f309c01f3937 0x5b003f309c01f393

def z504 : W := mkw 0x0be48ec300000000 0x00be48ec30000000 0x4ffc8fff80000003 0xf4ffc8fff8000000

def z505 : W := mkw 0x02c48e8309a2e466 0x402c48e8309a2e46 0xffcc8f8fffe3ffff 0xfffcc8f8fffe3fff

def z506 : W := mkw 0x00103030c4091211 0x200103030c409121 0x9030f3f1c4033e36 0xd9030f3f1c4033e3

def z507 : W := mkw 0x1fff8fdf7ff6ffe7 0xc1fff8fdf7ff6ffe 0xffff8fffffffffff 0xfffff8ffffffffff

def z508 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x9e3003f07c003e06 0xd9e3003f07c003e0

def z509 : W := mkw 0x42412fef80000000 0x042412fef8000000 0x4033ffff80000003 0xd4033ffff8000000

def z510 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x903373f9c01c3f32 0x4903373f9c01c3f3

def z511 : W := mkw 0x02000a0000000000 0x002000a000000000 0x4e000f0000000002 0x74e000f000000000

def z512 : W := mkw 0x02100a104c00b205 0x002100a104c00b20 0xde300ff07c00fe0e 0xfde300ff07c00fe0

def z513 : W := mkw 0x2dbed0007f7fa98c 0x82dbed0007f7fa98 0xbffff0007ffff9cd 0xfbffff0007ffff9c

def z514 : W := mkw 0x0001010800040900 0x8000101080004090 0xf00f0f0e407cf9cf 0x7f00f0f0e407cf9c

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000800004030005 0x9200080000403000

def z516 : W := mkw 0x196004c022804402 0x0196004c02280440 0x01c0000003800000 0x001c000000380000

def z517 : W := mkw 0x6ffedec7777b0008 0x06ffedec7777b000 0xeffffc067fff000d 0xfeffffc067fff000

def z518 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x41cc8c8787e3c6f8 0xa41cc8c8787e3c6f

def z519 : W := mkw 0x040b010c10540980 0x8040b010c1054098 0x00030000001c0000 0x000030000001c000

def z520 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb0337370441f3f34 0x4b0337370441f3f3

def z521 : W := mkw 0x02010b0c00000000 0x002010b0c0000000 0x40000f0e00000002 0x040000f0e0000000

def z522 : W := mkw 0x164b0fdc18d4ff87 0x8164b0fdc18d4ff8 0xfe0f0ffe787cffcf 0x7fe0f0ffe787cffc

def z523 : W := mkw 0x449ff13fc40d1b11 0xa449ff13fc40d1b1 0xb03ff3ffc41f3f37 0xdb03ff3ffc41f3f3

def z524 : W := mkw 0x0010001044001201 0x0001000104400120 0x003000f004000600 0x8003000f00400060

def z525 : W := mkw 0x1be48ec32ba2e466 0x41be48ec32ba2e46 0x7fcc8c8fbfe3c7ff 0xb7fcc8c8fbfe3c7f

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000000060c1cc 0x0300000000060c1c

def z527 : W := mkw 0x005135b8c48d5f13 0xa005135b8c48d5f1 0xf1f3fff9c79fff3f 0xff1f3fff9c79fff3

def z528 : W := mkw 0x0b600ec000804402 0x00b600ec00080440 0x5ff00ff00780c60e 0xf5ff00ff00780c60

def z529 : W := mkw 0x101000107ed4ff87 0x8101000107ed4ff8 0xb00000007ffcffcc 0x0b00000007ffcffc

def z530 : W := mkw 0x0fafcb0c00000000 0x00fafcb0c0000000 0x4fffff0e00000003 0xf4fffff0e0000000

def z531 : W := mkw 0x1b200a402a00a004 0x01b200a402a00a00 0x0e00000038000000 0x00e0000003800000

def z532 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xbe030308781c3907 0x5be030308781c390

def z533 : W := mkw 0x000000000800a004 0x0000000000800a00 0x900000007800f80c 0x0900000007800f80

def z534 : W := mkw 0x00113138c4091211 0x200113138c409121 0x0033f3f984030633 0xd0033f3f98403063

def z535 : W := mkw 0x1f7a0ed07ed0f607 0x01f7a0ed07ed0f60 0xffff0ff07ffcfe0f 0xfffff0ff07ffcfe0

def z536 : W := mkw 0x02113b3ccc0dbb95 0xa02113b3ccc0dbb9 0xf033ffffc41ffff7 0xdf033ffffc41ffff

def z537 : W := mkw 0x3ffeded37ffbf66f 0x43ffeded37ffbf66 0xffffffffffffffff 0xffffffffffffffff

def z538 : W := mkw 0x1bf48ed36e80f607 0x01bf48ed36e80f60 0xdffc8fffff80fe0f 0xfdffc8fffff80fe0

def z539 : W := mkw 0x00c4848319f6ede6 0xc00c4848319f6ede 0xf1cc8c8fffffffff 0xbf1cc8c8ffffffff

def z540 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0030308441f3f37 0x5b0030308441f3f3

def z541 : W := mkw 0x12100a106e80f607 0x012100a106e80f60 0xde000f007f80fe0e 0x7de000f007f80fe0

def z542 : W := mkw 0x2ffedec0777b0008 0x02ffedec0777b000 0xeffffff07fff000f 0xfeffffff07fff000

def z543 : W := mkw 0x4fffffffc4091211 0x24fffffffc409121 0x4fffffff84030633 0xf4fffffff8403063

def z544 : W := mkw 0x00c4848300000000 0x000c484830000000 0x71cc8c8f84030737 0xb71cc8c8f8403073

def z545 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000000004030734 0x0300000000403073

def z546 : W := mkw 0x6fffffefff7fa98c 0x86fffffefff7fa98 0xfffffffffffff9cf 0xffffffffffffff9c

def z547 : W := mkw 0x0deec48301a24462 0x40deec48301a2446 0x7ffffc8f87e3c7ff 0xf7ffffc8f87e3c7f

def z548 : W := mkw 0x00113138dc5dbb95 0xa00113138dc5dbb9 0xb033f3f9fc7fffff 0xdb033f3f9fc7ffff

def z549 : W := mkw 0x061b3b3cdc5dbb95 0xa061b3b3cdc5dbb9 0xfe3f7f7e787cf9cf 0x7fe3f7f7e787cf9c

def z550 : W := mkw 0x00112138c4001201 0x000112138c400120 0x9033f3f9c4003e07 0xd9033f3f9c4003e0

def z551 : W := mkw 0x0010100044090000 0x0001010004409000 0x80337000401c0000 0x480337000401c000

def z552 : W := mkw 0x0970048066804402 0x0097004806680440 0xdff00c807f80c60e 0xfdff00c807f80c60

def z553 : W := mkw 0x4f2a4a4400000000 0x04f2a4a440000000 0x0e00000000000000 0x00e0000000000000

def z554 : W := mkw 0x261b1b0c7f7fa98c 0x8261b1b0c7f7fa98 0xfe0f0f0e7ffff9cf 0x7fe0f0f0e7ffff9c

def z555 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x21cc808187e3063d 0xb21cc808187e3063

def z556 : W := mkw 0x1b701ed06e89f607 0x01b701ed06e89f60 0xfff3fff07f9ffe0f 0xffff3fff07f9ffe0

def z557 : W := mkw 0x068f8b0c1976a984 0x8068f8b0c1976a98 0xffcf8f0e7ffff9cf 0xfffcf8f0e7ffff9c

def z558 : W := mkw 0x2faeca043b72a08c 0x02faeca043b72a08 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z559 : W := mkw 0x0084800301220060 0x4008480030122006 0x21cc800f87e301fd 0xb21cc800f87e301f

def z560 : W := mkw 0x5fffefffe6805603 0x05fffefffe680560 0x4fffffff87800603 0xf4fffffff8780060

def z561 : W := mkw 0x3feecec03bf2e40e 0x03feecec03bf2e40 0x4fcc0c003be0c008 0x24fcc0c003be0c00

def z562 : W := mkw 0x59f4e4f3e6805603 0x059f4e4f3e680560 0x01f0f0f187800600 0x801f0f0f18780060

def z563 : W := mkw 0x1b703ef0ee89f617 0x21b703ef0ee89f61 0xdff0fff1ff83fe3e 0xfdff0fff1ff83fe3

def z564 : W := mkw 0x00d4948345ab4462 0x400d4948345ab446 0xf1fffc8fc7ffc7ff 0xff1fffc8fc7ffc7f

def z565 : W := mkw 0x4fefefef90540980 0x84fefefef9054098 0x6fffffff807c01c3 0xf6fffffff807c01c

def z566 : W := mkw 0x12410fdc0884ff87 0x812410fdc0884ff8 0x50000ffe0000ffc2 0x050000ffe0000ffc

def z567 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x0ffcf0003fe30008 0xa0ffcf0003fe3000

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x003003f000000002 0xd003003f00000000

def z569 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000808980000003 0x9000080898000000

def z570 : W := mkw 0x02010b0c0804a984 0x802010b0c0804a98 0x700c0f0e0060f9cf 0x3700c0f0e0060f9c

def z571 : W := mkw 0x4fefcfcf1854a984 0x84fefcfcf1854a98 0xffcf0f0e787cf9cf 0x7ffcf0f0e787cf9c

def z572 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x4ff00cf03f80c608 0xa4ff00cf03f80c60

def z573 : W := mkw 0x0084800301220060 0x4008480030122006 0x700c8c0f8063c1ff 0x3700c8c0f8063c1f

def z574 : W := mkw 0x00c5858b01a64d62 0xc00c5858b01a64d6 0xf1cf8f8fc7ffffff 0xff1cf8f8fc7fffff

def z575 : W := mkw 0x040a000410500080 0x0040a00041050008 0x000c0006006000c0 0x0000c0006006000c

def z576 : W := mkw 0x060b0b0c00040900 0x8060b0b0c0004090 0xfe0f0f0e401c3907 0x7fe0f0f0e401c390

def z577 : W := mkw 0x4feecec701a24462 0x44feecec701a2446 0x4fcc0c0603e0c0c8 0x24fcc0c0603e0c0c

def z578 : W := mkw 0x0daec00010500000 0x00daec0001050000 0xaffff000787c000d 0xfaffff000787c000

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c000e006001c1 0x0200c000e006001c

def z580 : W := mkw 0x1b710fdc6e84ff87 0x81b710fdc6e84ff8 0xdff00ffe7f80ffce 0xfdff00ffe7f80ffc

def z581 : W := mkw 0x2dfed48077fb440a 0x02dfed48077fb440 0xfffffc807fffc60f 0xffffffc807fffc60

def z582 : W := mkw 0x4fffefefe6000000 0x04fffefefe600000 0xcfffffffff80000f 0xfcfffffffff80000

def z583 : W := mkw 0x060b3b2c985da994 0xa060b3b2c985da99 0xfe0fff0ff87ff9ff 0x7fe0fff0ff87ff9f

def z584 : W := mkw 0x000101081854a984 0x8000101081854a98 0xb0030308787cf9cf 0x5b0030308787cf9c

def z585 : W := mkw 0x00103030c4091211 0x200103030c409121 0x3030f0f984030737 0x93030f0f98403073

def z586 : W := mkw 0x4fffffffc5af5f73 0xe4fffffffc5af5f7 0xffffffffc7ffffff 0xfffffffffc7fffff

def z587 : W := mkw 0x0010101044091201 0x0001010104409120 0xb033f3f0441f3e07 0xdb033f3f0441f3e0

def z588 : W := mkw 0x12c48ed309a2f667 0x412c48ed309a2f66 0x71cc8fff87e3ffff 0xb71cc8fff87e3fff

def z589 : W := mkw 0x0010001044001201 0x0001000104400120 0x8030037040003800 0x4803003704000380

def z590 : W := mkw 0x12000a500800b205 0x012000a500800b20 0x0000037000003800 0x0000003700000380

def z591 : W := mkw 0x0040048300804462 0x4004004830080446 0x51c00c8f8780c7fe 0xb51c00c8f8780c7f

def z592 : W := mkw 0x268fdb0c197fa98c 0x8268fdb0c197fa98 0xfe0fff0e787ff9cf 0x7fe0fff0e787ff9c

def z593 : W := mkw 0x00c4848300804402 0x000c484830080440 0x51cc8c8f8780c60f 0xb51cc8c8f8780c60

def z594 : W := mkw 0x0000000019f6ede6 0xc0000000019f6ede 0xb00000007ffffffc 0x0b00000007ffffff

def z595 : W := mkw 0x197004d06e80f607 0x0197004d06e80f60 0x91f000f07f80fe0c 0x891f000f07f80fe0

def z596 : W := mkw 0x0040048001a24462 0x40040048001a2446 0x71c00c8007e3c7fe 0xb71c00c8007e3c7f

def z597 : W := mkw 0x00c4848001a24402 0x000c4848001a2440 0x71cc8c8007e3c60f 0xb71cc8c8007e3c60

def z598 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc0c0e03e0c1cf 0x371cc0c0e03e0c1c

def z599 : W := mkw 0x42c5afef81a24462 0x442c5afef81a2446 0x71cc8fff87e3c7ff 0xb71cc8fff87e3c7f

def z600 : W := mkw 0x0084800301220060 0x4008480030122006 0x000c0006006000c0 0x0000c0006006000c

def z601 : W := mkw 0x248ed000117b0008 0x0248ed000117b000 0xae0ff000787f000d 0x7ae0ff000787f000

def z602 : W := mkw 0x2930500066090008 0x0293050006609000 0x0030700000000000 0x0003070000000000

def z603 : W := mkw 0x041b313cd45d1b91 0xa041b313cd45d1b9 0xb03ff3ffc47f3ff7 0xdb03ff3ffc47f3ff

def z604 : W := mkw 0x09a4c00000000000 0x009a4c0000000000 0x01f0f00000000000 0x801f0f0000000000

def z605 : W := mkw 0x02000a000800a004 0x002000a000800a00 0x8e00030078003800 0x48e0003007800380

def z606 : W := mkw 0x0000000300000060 0x4000000030000006 0x0000000f800001f0 0x00000000f800001f

def z607 : W := mkw 0x0040048300000000 0x0004004830000000 0x40000c8f80000002 0x040000c8f8000000

def z608 : W := mkw 0x12400ed00880f607 0x012400ed00880f60 0xde000ff07800fe0e 0x7de000ff07800fe0

def z609 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0x7e0c0c0e3860c1cf 0x37e0c0c0e3860c1c

def z610 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x7fffffff8060c1cf 0xf7fffffff8060c1c

def z611 : W := mkw 0x12513ff8cc8dff17 0xa12513ff8cc8dff1 0xf033fff9c41fff37 0xdf033fff9c41fff3

def z612 : W := mkw 0x2daed000117b0008 0x02daed000117b000 0x2ffff000007f0001 0xf2ffff000007f000

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000c000000c00e 0x350000c000000c00

def z614 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xde030f00781cf80e 0x7de030f00781cf80

def z615 : W := mkw 0x2d3a5000777b0008 0x02d3a5000777b000 0xae3370007fff000c 0x4ae3370007fff000

def z616 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x01c0000003800000 0x001c000000380000

def z617 : W := mkw 0x0b700ed044001201 0x00b700ed04400120 0xdff00ff044003e06 0xfdff00ff044003e0

def z618 : W := mkw 0x1bf48ed36fa2f667 0x41bf48ed36fa2f66 0xdff08ff1ff83fe3e 0xfdff08ff1ff83fe3

def z619 : W := mkw 0x04ce848311f24462 0x404ce848311f2446 0xffcf8c8fffffc7ff 0xfffcf8c8fffffc7f

def z620 : W := mkw 0x0010100044090000 0x0001010004409000 0xb033f089c41f0737 0xdb033f089c41f073

def z621 : W := mkw 0x2010100077fb446a 0x42010100077fb446 0xb00000007fffc7fc 0x0b00000007fffc7f

def z622 : W := mkw 0x0d3a000076500000 0x00d3a00007650000 0xafff00007ffc000d 0xfafff00007ffc000

def z623 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xde030f0e781cf9c2 0x4de030f0e781cf9c

def z624 : W := mkw 0x20949000777b0008 0x020949000777b000 0xa1cc80007fff000d 0xba1cc80007fff000

def z625 : W := mkw 0x20001000117b0008 0x020001000117b000 0x20000000007f0000 0x020000000007f000

def z626 : W := mkw 0x0095b13bc52f1b71 0xe0095b13bc52f1b7 0xb03ff3ffc47f3ff7 0xdb03ff3ffc47f3ff

def z627 : W := mkw 0x0001213880041b11 0xa0001213880041b1 0x1033f3f980003f33 0xd1033f3f980003f3

def z628 : W := mkw 0x040b010c10540980 0x8040b010c1054098 0xb00f030e407c39c7 0x5b00f030e407c39c

def z629 : W := mkw 0x0b600ec000000000 0x00b600ec00000000 0x4fc00c0000000000 0x24fc00c000000000

def z630 : W := mkw 0x197135f8e68d5f13 0xa197135f8e68d5f1 0xb1f3f3f9c79f3f37 0xdb1f3f3f9c79f3f3

def z631 : W := mkw 0x5f3b6b7cee00b205 0x05f3b6b7cee00b20 0x8e33737078003800 0x48e3373707800380

def z632 : W := mkw 0x0000001000001201 0x0000000100000120 0x100003f000003e02 0x0100003f000003e0

def z633 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0x21fcf00007e3000d 0xb21fcf00007e3000

def z634 : W := mkw 0x06cf8f8f01a24462 0x406cf8f8f01a2446 0x7fcf8f8f87e3c7ff 0xf7fcf8f8f87e3c7f

def z635 : W := mkw 0x02000a000800a004 0x002000a000800a00 0x4e000c003800c008 0x24e000c003800c00

def z636 : W := mkw 0x5fffefffee00b205 0x05fffefffee00b20 0xcffffffff8003803 0xfcffffffff800380

def z637 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xf03fffffc47fffff 0xff03fffffc47ffff

def z638 : W := mkw 0x0deec48300000000 0x00deec4830000000 0x4ffffc8f80000003 0xf4ffffc8f8000000

def z639 : W := mkw 0x2fbeda007f7ba00c 0x02fbeda007f7ba00 0xffffff007ffff80f 0xfffffff007ffff80

def z640 : W := mkw 0x1ffeced06e80f607 0x01ffeced06e80f60 0xdffffff07f80fe0f 0xfdffffff07f80fe0

def z641 : W := mkw 0x100000002a80e406 0x0100000002a80e40 0x000000003b80c008 0x0000000003b80c00

def z642 : W := mkw 0x2deec48333f2446a 0x42deec48333f2446 0x7fcc8c8fbfe3c7ff 0xb7fcc8c8fbfe3c7f

def z643 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0xde300f707800f80e 0x7de300f707800f80

def z644 : W := mkw 0x000000000804a984 0x8000000000804a98 0x100000000000f9c0 0x0100000000000f9c

def z645 : W := mkw 0x040b010c10540980 0x8040b010c1054098 0xae0f000e787c01cd 0x7ae0f000e787c01c

def z646 : W := mkw 0x06cf8f8f1854a984 0x806cf8f8f1854a98 0xffcf8f8ff87cf9cf 0xfffcf8f8ff87cf9c

def z647 : W := mkw 0x4feecec701a24462 0x44feecec701a2446 0x7fcc8c8f87e3c7ff 0xb7fcc8c8f87e3c7f

def z648 : W := mkw 0x0f6b0fcc00000000 0x00f6b0fcc0000000 0x4fff0ffe00000003 0xf4fff0ffe0000000

def z649 : W := mkw 0x0920000022000000 0x0092000002200000 0x0fc000003b800008 0x20fc000003b80000

def z650 : W := mkw 0x240a500010590008 0x0240a50001059000 0x00037000001c0000 0x000037000001c000

def z651 : W := mkw 0x0001010800040900 0x8000101080004090 0x20030008001c0101 0x020030008001c010

def z652 : W := mkw 0x0930000066000000 0x0093000006600000 0x01f0000007800000 0x801f000000780000

def z653 : W := mkw 0x0040048300804462 0x4004004830080446 0x700c0c8f8060c7ff 0x3700c0c8f8060c7f

def z654 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0xde0c0f067860f8ce 0x7de0c0f067860f8c

def z655 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c0c0e00000003 0x3400c0c0e0000000

def z656 : W := mkw 0x0001213880041b11 0xa0001213880041b1 0xb00303f9c01c3f37 0x5b00303f9c01c3f3

def z657 : W := mkw 0x0084800001220000 0x0008480000122000 0x01cc000003e00008 0x201cc000003e0000

def z658 : W := mkw 0x061b0b1c5c54bb85 0x8061b0b1c5c54bb8 0xfe3f0ffe7c7cffcf 0xffe3f0ffe7c7cffc

def z659 : W := mkw 0x3ffeced07ff2f60f 0x03ffeced07ff2f60 0xdffc0ff07fe0fe0e 0xfdffc0ff07fe0fe0

def z660 : W := mkw 0x0001010800040900 0x8000101080004090 0xb0038389c41f3f37 0xdb0038389c41f3f3

def z661 : W := mkw 0x440b612c80000000 0x0440b612c8000000 0x0003700000000000 0x0000370000000000

def z662 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033f00000000001 0xd0033f0000000000

def z663 : W := mkw 0x42513fffc40d1b11 0xa42513fffc40d1b1 0xf033ffffc41f3f37 0xdf033ffffc41f3f3

def z664 : W := mkw 0x00d4b4b3c5ab5673 0x600d4b4b3c5ab567 0x01f0f0f187830630 0x801f0f0f18783063

def z665 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xae0f0300787c380d 0x7ae0f0300787c380

def z666 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x41cc8c8f87830633 0xb41cc8c8f8783063

def z667 : W := mkw 0x02410f8f0884ede6 0xc02410f8f0884ede 0x50000f8f8000fff2 0x050000f8f8000fff

def z668 : W := mkw 0x040b010c10540980 0x8040b010c1054098 0x700f0c0e007cc1cf 0x3700f0c0e007cc1c

def z669 : W := mkw 0x29a4c00023220008 0x029a4c0002322000 0x01c0000003800000 0x001c000000380000

def z670 : W := mkw 0x2dbef030f77b1219 0x22dbef030f77b121 0xaffff0f1ffff063d 0xfaffff0f1ffff063

def z671 : W := mkw 0x0040048300804462 0x4004004830080446 0x0000008180000630 0x0000000818000063

def z672 : W := mkw 0x39f4d4d067ab560b 0x039f4d4d067ab560 0x01f0f0f007830600 0x801f0f0f00783060

def z673 : W := mkw 0x2deec48333f2446a 0x42deec48333f2446 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z674 : W := mkw 0x2dbed000672b0008 0x02dbed000672b000 0x0ffff00007830001 0xf0ffff0000783000

def z675 : W := mkw 0x0084800000000000 0x0008480000000000 0x01cc800000000001 0xb01cc80000000000

def z676 : W := mkw 0x0daec00000000000 0x00daec0000000000 0x0fcc000000000000 0x20fcc00000000000

def z677 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x903373f0441c3e06 0xd903373f0441c3e0

def z678 : W := mkw 0x00111108440d0900 0x800111108440d090 0xb033f308441f3907 0xdb033f308441f390

def z679 : W := mkw 0x0040048000804402 0x0004004800080440 0x71cc0c8e07e0c7cf 0xb71cc0c8e07e0c7c

def z680 : W := mkw 0x1b313b78ee0dbb15 0xa1b313b78ee0dbb1 0x8e337370781c3800 0x48e337370781c380

def z681 : W := mkw 0x197034f0e6895613 0x2197034f0e689561 0x01f0f0f187830630 0x801f0f0f18783063

def z682 : W := mkw 0x0000000000000000 0x0000000000000000 0x200c00000060000d 0x3200c00000060000

def z683 : W := mkw 0x248ed000117b0008 0x0248ed000117b000 0x21cff00007ff000d 0xb21cff00007ff000

def z684 : W := mkw 0x0095b138c52f1b11 0xa0095b138c52f1b1 0xb1fff3f9c7ff3f3f 0xfb1fff3f9c7ff3f3

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0030000401c0005 0x5a0030000401c000

def z686 : W := mkw 0x49f5f5fbc40d1b11 0xa49f5f5fbc40d1b1 0xb1f3f3f9c41f3f37 0xdb1f3f3f9c41f3f3

def z687 : W := mkw 0x100000100880f607 0x0100000100880f60 0x100000000000fe00 0x0100000000000fe0

def z688 : W := mkw 0x5feecec72a80e406 0x05feecec72a80e40 0x4fcc0c063b80c008 0x24fcc0c063b80c00

def z689 : W := mkw 0x0085b12b812f0970 0xe0085b12b812f097 0x200ff00f807f01f1 0x0200ff00f807f01f

def z690 : W := mkw 0x29b4f030e72b1219 0x229b4f030e72b121 0x01f0f0f187830630 0x801f0f0f18783063

def z691 : W := mkw 0x0000302080090010 0x2000030208009001 0x0000f00180030030 0x00000f0018003003

def z692 : W := mkw 0x29f4d48367ab446a 0x429f4d48367ab446 0x01f0f08187830630 0x801f0f0818783063

def z693 : W := mkw 0x12500ed06e80f607 0x012500ed06e80f60 0xd0000ff07f80fe0e 0x0d0000ff07f80fe0

def z694 : W := mkw 0x00113128c4090000 0x000113128c409000 0xa033f3f9c41f0007 0xda033f3f9c41f000

def z695 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0x700f0f0e007cf9c3 0x0700f0f0e007cf9c

def z696 : W := mkw 0x0000000000804402 0x0000000000080440 0x100000000780c60c 0x0100000000780c60

def z697 : W := mkw 0x0000000000000000 0x0000000000000000 0x400c0c060060c0c8 0x2400c0c060060c0c

def z698 : W := mkw 0x06cf8f8f19f6ede6 0xc06cf8f8f19f6ede 0xffcf0f0e7bfcf9cf 0x7ffcf0f0e7bfcf9c

def z699 : W := mkw 0x02010b080804a904 0x802010b080804a90 0xfe030f08781cf90f 0x7fe030f08781cf90

def z700 : W := mkw 0x1b700ed06e00b205 0x01b700ed06e00b20 0xcff00ff078003802 0xfcff00ff07800380

def z701 : W := mkw 0x46cfefef80000000 0x046cfefef8000000 0x400fffff80000003 0x0400fffff8000000

def z702 : W := mkw 0x6feecec733720008 0x06feecec73372000 0x4fcc0c063be00008 0x24fcc0c063be0000

def z703 : W := mkw 0x0084800301220060 0x4008480030122006 0x0000800180030030 0x0000080018003003

def z704 : W := mkw 0x040a000010500000 0x0040a00001050000 0x8e030000781c0000 0x48e030000781c000

def z705 : W := mkw 0x00c4848301220060 0x400c484830122006 0x61cc8c8f806301f3 0xb61cc8c8f806301f

def z706 : W := mkw 0x060b0b0c10540980 0x8060b0b0c1054098 0x6e0f0f0e007c01c3 0x76e0f0f0e007c01c

def z707 : W := mkw 0x44cfe5af80000000 0x044cfe5af8000000 0x41ffffff80000003 0xf41ffffff8000000

def z708 : W := mkw 0x12412ffc8884ff97 0xa12412ffc8884ff9 0x50000fff8000fff2 0x050000fff8000fff

def z709 : W := mkw 0x000121289854a984 0x8000121289854a98 0xb033f3f9f87cf9cf 0xdb033f3f9f87cf9c

def z710 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f0707000000000 0x001f070700000000

def z711 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x3e33f3f984030737 0xd3e33f3f98403073

def z712 : W := mkw 0x12412ff88884ff17 0xa12412ff88884ff1 0x50000ff00000fe02 0x050000ff00000fe0

def z713 : W := mkw 0x448fe12f81220060 0x4448fe12f8122006 0x303ff3ff846307f7 0xd303ff3ff846307f

def z714 : W := mkw 0x2daed000337b0008 0x02daed000337b000 0x2ffff0003bff0009 0xf2ffff0003bff000

def z715 : W := mkw 0x1b600ed02a80f607 0x01b600ed02a80f60 0x5ff00ff03b80fe0a 0xf5ff00ff03b80fe0

def z716 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x0ff3f37000000000 0xc0ff3f3700000000

def z717 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x6fffffff806001c3 0xf6fffffff806001c

def z718 : W := mkw 0x460b6b2c9854a984 0x8460b6b2c9854a98 0xfe0f7f0e787cf9cf 0x7fe0f7f0e787cf9c

def z719 : W := mkw 0x46cfefef80000000 0x046cfefef8000000 0x403fffff80000003 0xd403fffff8000000

def z720 : W := mkw 0x0feecec001a24402 0x00feecec001a2440 0x7ffffff007e3c60f 0xf7ffffff007e3c60

def z721 : W := mkw 0x060a0a041854a984 0x8060a0a041854a98 0xfe0c0f06787cf9ce 0x7fe0c0f06787cf9c

def z722 : W := mkw 0x248ed000117b0008 0x0248ed000117b000 0xafcff0007fff000d 0xfafcff0007fff000

def z723 : W := mkw 0x0001212880040900 0x8000121288004090 0xb033f3f9c41f3f37 0xdb033f3f9c41f3f3

def z724 : W := mkw 0x2dbed010777b1209 0x02dbed010777b120 0xbffff3f9ffff3f3f 0xfbffff3f9ffff3f3

def z725 : W := mkw 0x00101010448d5f73 0xe00101010448d5f7 0xb0000000441ffff4 0x0b0000000441ffff

def z726 : W := mkw 0x0d2b612880000000 0x00d2b61288000000 0x0e33f3f980000003 0xd0e33f3f98000000

def z727 : W := mkw 0x6fefefefb3f2446a 0x46fefefefb3f2446 0x4fffffffbbe0c0cb 0xf4fffffffbbe0c0c

def z728 : W := mkw 0x42012b6c80000000 0x042012b6c8000000 0x0033f3f980000003 0xd0033f3f98000000

def z729 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xcff00ff07f80fe08 0xecff00ff07f80fe0

def z730 : W := mkw 0x2dbed010777b1209 0x02dbed010777b120 0xaffff0f07fff060d 0xfaffff0f07fff060

def z731 : W := mkw 0x49e4e4e39854a984 0x849e4e4e39854a98 0xb1f0f0f1f87cf9cc 0x8b1f0f0f1f87cf9c

def z732 : W := mkw 0x00c4a4a381a24462 0x400c4a4a381a2446 0x01f0f0f187830630 0x801f0f0f18783063

def z733 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xbe33f3f9fc1f3f3f 0xfbe33f3f9fc1f3f3

def z734 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x4fffffff8000c0c3 0xf4fffffff8000c0c

def z735 : W := mkw 0x00101010452f1b71 0xe00101010452f1b7 0xb0000000447f3ff4 0x0b0000000447f3ff

def z736 : W := mkw 0x4fefefef80000060 0x44fefefef8000006 0x4fffffff800001f3 0xf4fffffff800001f

def z737 : W := mkw 0x1b701ed06e89f617 0x21b701ed06e89f61 0xdff00ff07f83fe3e 0xfdff00ff07f83fe3

def z738 : W := mkw 0x2bb5db0c6f2fa98c 0x82bb5db0c6f2fa98 0x51f0ff0e0783f9c2 0x851f0ff0e0783f9c

def z739 : W := mkw 0x20101010777b1219 0x220101010777b121 0xa00000007fff063c 0x0a00000007fff063

def z740 : W := mkw 0x004125a880000000 0x0004125a88000000 0x41f3fff980000003 0xf41f3fff98000000

def z741 : W := mkw 0x0b600ec00880e406 0x00b600ec00880e40 0xdff00ff07f80fe0e 0xfdff00ff07f80fe0

def z742 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0xfe3f7f7e787cf9cf 0x7fe3f7f7e787cf9c

def z743 : W := mkw 0x301010106fabf60f 0x0301010106fabf60 0x900000007f83fe0c 0x0900000007f83fe0

def z744 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe3fff0e787cf9cf 0xffe3fff0e787cf9c

def z745 : W := mkw 0x0daec00011720000 0x00daec0001172000 0xaffff0007fff000d 0xfaffff0007fff000

def z746 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x0e3373f180000000 0x40e3373f18000000

def z747 : W := mkw 0x4b616fef80000000 0x04b616fef8000000 0x40307fff80000002 0x040307fff8000000

def z748 : W := mkw 0x4be5efef8804a984 0x84be5efef8804a98 0x51f0ffff8000f9c2 0x851f0ffff8000f9c

def z749 : W := mkw 0x00c5a5ab80000000 0x000c5a5ab8000000 0x01f3f3f980000003 0xd01f3f3f98000000

def z750 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0x8e337370781c3800 0x48e337370781c380

def z751 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x9033f3f1c41f3e36 0xd9033f3f1c41f3e3

def z752 : W := mkw 0x549fe13fee80f607 0x0549fe13fee80f60 0x900ff00fff80fe0d 0x0900ff00fff80fe0

def z753 : W := mkw 0x0be4cec000000000 0x00be4cec00000000 0x4ff0fff000000002 0xf4ff0fff00000000

def z754 : W := mkw 0x49e5e5eb80040900 0x849e5e5eb8004090 0xb1f3f3f9c01c3907 0xdb1f3f3f9c01c390

def z755 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033737800000003 0x5003373780000000

def z756 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x6fffffff87e301ff 0xf6fffffff87e301f

def z757 : W := mkw 0x06cfafaf80000000 0x006cfafaf8000000 0x4fffffff80000003 0xf4fffffff8000000

def z758 : W := mkw 0x5fefefefaa80e406 0x05fefefefaa80e40 0xdffffffffb80f80f 0xfdffffffffb80f80

def z759 : W := mkw 0x59e4e4e3a2804402 0x059e4e4e3a280440 0x01f0f0f183800000 0x801f0f0f18380000

def z760 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x8ff003707b803808 0x68ff003707b80380

def z761 : W := mkw 0x2d7a548376d9446a 0x42d7a548376d9446 0xde337c8ff81cc7f2 0x4de337c8ff81cc7f

def z762 : W := mkw 0x1b613fe8aa8ded16 0xa1b613fe8aa8ded1 0x6fc3fc09bb9fc139 0x26fc3fc09bb9fc13

def z763 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffffff8060c0cb 0xf4fffffff8060c0c

def z764 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x9ff003f07f80fe0c 0xc9ff003f07f80fe0

def z765 : W := mkw 0x248ff12c917f0998 0xa248ff12c917f099 0x200ff00f807f01f1 0x0200ff00f807f01f

def z766 : W := mkw 0x201010107f7fbb9d 0xa201010107f7fbb9 0xb00000007ffffffc 0x0b00000007ffffff

def z767 : W := mkw 0x06cf8f8f19f6ede6 0xc06cf8f8f19f6ede 0x8fc38381ff9f3e30 0xc8fc38381ff9f3e3

def z768 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x6fffffff8060000f 0xf6fffffff8060000

def z769 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x6fffffff87e307f3 0xf6fffffff87e307f

def z770 : W := mkw 0x4deee4e380000000 0x04deee4e38000000 0x01fff0f180000001 0x801fff0f18000000

def z771 : W := mkw 0x0daec00000000000 0x00daec0000000000 0x0ffff3f000000003 0xf0ffff3f00000000

def z772 : W := mkw 0x02000a001854a984 0x802000a001854a98 0xfe0c0f0e787cf9cf 0x7fe0c0f0e787cf9c

def z773 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x6fffffff84030007 0xf6fffffff8403000

def z774 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe3f0ffe787cf9cf 0xffe3f0ffe787cf9c

def z775 : W := mkw 0x301010107e59b20d 0x0301010107e59b20 0x80000000781c3800 0x080000000781c380

def z776 : W := mkw 0x0000202080000000 0x0000020208000000 0x0030f0f980000003 0x90030f0f98000000

def z777 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x4e3fff7f80000003 0x74e3fff7f8000000

def z778 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0xfe0f0ffff87cf9cf 0x7fe0f0ffff87cf9c

def z779 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x4fffffff87800603 0xf4fffffff8780060

def z780 : W := mkw 0x0f6a4ec000000000 0x00f6a4ec00000000 0x4ff37ff000000002 0xf4ff37ff00000000

def z781 : W := mkw 0x30d494907ffbf60f 0x030d494907ffbf60 0xf1cc8c807ffffe0f 0xbf1cc8c807ffffe0

def z782 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x0ff373f000000000 0xc0ff373f00000000

def z783 : W := mkw 0x0b700ec06e00a004 0x00b700ec06e00a00 0xdff00ff07f80f80e 0xfdff00ff07f80f80

def z784 : W := mkw 0x193000106e80f607 0x0193000106e80f60 0x9ff003f07f80fe0e 0xf9ff003f07f80fe0

def z785 : W := mkw 0x2daec00033720008 0x02daec0003372000 0xaffff0007bfc000d 0xfaffff0007bfc000

def z786 : W := mkw 0x060b2b2c80000000 0x0060b2b2c8000000 0x7e3fffff8463c7ff 0xf7e3fffff8463c7f

def z787 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xffcf0f0e7ffcf9cf 0xfffcf0f0e7ffcf9c

def z788 : W := mkw 0x36ceded019fbf60f 0x036ceded019fbf60 0x700ffff0007ffe03 0x0700ffff0007ffe0

def z789 : W := mkw 0x4fefefef99f6ede6 0xc4fefefef99f6ede 0xfffffffffbfcf9cf 0xffffffffffbfcf9c

def z790 : W := mkw 0x4fefefef90540980 0x84fefefef9054098 0xffffffffc07c39c7 0xfffffffffc07c39c

def z791 : W := mkw 0x4be4eee780000000 0x04be4eee78000000 0x41f0fcf780000000 0x841f0fcf78000000

def z792 : W := mkw 0x4d2b616c80000000 0x04d2b616c8000000 0x0033707000000000 0x0003370700000000

def z793 : W := mkw 0x001010105c5dbb95 0xa001010105c5dbb9 0xb0000000787cf9cc 0x0b0000000787cf9c

def z794 : W := mkw 0x00c5a5ab81a24462 0x400c5a5ab81a2446 0x41ffffff83e0c0cb 0xf41ffffff83e0c0c

def z795 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x71fcfcff8060c1cf 0xb71fcfcff8060c1c

def z796 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0xffffffffc41f3f37 0xfffffffffc41f3f3

def z797 : W := mkw 0x4084e02380000000 0x04084e0238000000 0x0030f0f180000000 0x80030f0f18000000

def z798 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x4fffffff80000633 0xf4fffffff8000063

def z799 : W := mkw 0x4defe5ef80000000 0x04defe5ef8000000 0x01f3f0f180000000 0x801f3f0f18000000

def z800 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb03ff3f9c47f3f3f 0xfb03ff3f9c47f3f3

def z801 : W := mkw 0x3feecec33bf2e46e 0x43feecec33bf2e46 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z802 : W := mkw 0x10d494936fafff77 0xe10d494936fafff7 0xf1cc8c8fffffffff 0xbf1cc8c8ffffffff

def z803 : W := mkw 0x1b700ed36e80f607 0x01b700ed36e80f60 0xdff00fffff80fe0e 0xfdff00fffff80fe0

def z804 : W := mkw 0x4deee4e380000000 0x04deee4e38000000 0x0ff3f0f180000000 0xc0ff3f0f18000000

def z805 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0x80030300401c3800 0x480030300401c380

def z806 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x41f0fcff80000002 0x841f0fcff8000000

def z807 : W := mkw 0x361a1a107ffbf60f 0x0361a1a107ffbf60 0xfe0f0f007ffffe0f 0x7fe0f0f007ffffe0

def z808 : W := mkw 0x6deee4e3b3720008 0x06deee4e3b372000 0x0ffcf0f1bbe00008 0xa0ffcf0f1bbe0000

def z809 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71fc8fff87e3c7ff 0xf71fc8fff87e3c7f

def z810 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x3033f3f9841f3f33 0x83033f3f9841f3f3

def z811 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000000447ffffc 0x0b0000000447ffff

def z812 : W := mkw 0x0defe5ab81a24462 0x40defe5ab81a2446 0x7fffffff87e3c7ff 0xf7fffffff87e3c7f

def z813 : W := mkw 0x4ffeded7440d1b11 0xa4ffeded7440d1b1 0xffcc0c06441f3f34 0x2ffcc0c06441f3f3

def z814 : W := mkw 0x2dbed003777b0068 0x42dbed003777b006 0xaffff001ffff003d 0xfaffff001ffff003

def z815 : W := mkw 0x4f2b6b6c81a24462 0x44f2b6b6c81a2446 0x3e33737007e3c7fc 0x43e33737007e3c7f

def z816 : W := mkw 0x4fefefef91720000 0x04fefefef9172000 0xefffffffffff000f 0xfefffffffffff000

def z817 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff3007fff380f 0xfbffff3007fff380

def z818 : W := mkw 0x0b212b6880000000 0x00b212b688000000 0x0e33737000000000 0x40e3373700000000

def z819 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x4fffff7e00000003 0xf4fffff7e0000000

def z820 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x4fffffff87e3c6fb 0xf4fffffff87e3c6f

def z821 : W := mkw 0x1b600ed02a80f607 0x01b600ed02a80f60 0xdfc00ff07b80fe0e 0x7dfc00ff07b80fe0

def z822 : W := mkw 0x1b700ed36e80f667 0x41b700ed36e80f66 0xfff08fffff83ffff 0xffff08fffff83fff

def z823 : W := mkw 0x4deee4e380000000 0x04deee4e38000000 0x0ffcf0f180000000 0xa0ffcf0f18000000

def z824 : W := mkw 0x101010104c8dff17 0xa101010104c8dff1 0xb0000000441fff34 0x0b0000000441fff3

def z825 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x4fffffff83e0000b 0xf4fffffff83e0000

def z826 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x6fffffff80630003 0xf6fffffff8063000

def z827 : W := mkw 0x1f7b2ffcfed4ff87 0x81f7b2ffcfed4ff8 0xfffffffffffcffcf 0xffffffffffffcffc

def z828 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000008441f3f37 0x1b0000008441f3f3

def z829 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc8c8f87e3c7f3 0x871cc8c8f87e3c7f

def z830 : W := mkw 0x0f6b2fec80000000 0x00f6b2fec8000000 0x4fffffff80000003 0xf4fffffff8000000

def z831 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0xaff3f0007f9f000d 0xfaff3f0007f9f000

def z832 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x6fffffff87e3063f 0xf6fffffff87e3063

def z833 : W := mkw 0x061a3a34dc59b295 0x2061a3a34dc59b29 0x4e3cfcf7bc63c6f8 0xa4e3cfcf7bc63c6f

def z834 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x4fffffff87830003 0xf4fffffff8783000

def z835 : W := mkw 0x040b212c80000000 0x0040b212c8000000 0x003ff3ff80000003 0xd003ff3ff8000000

def z836 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff08ff1ff83fe3e 0xfdff08ff1ff83fe3

def z837 : W := mkw 0x5f2b6b6caa00a004 0x05f2b6b6caa00a00 0x0e33737038000000 0x40e3373703800000

def z838 : W := mkw 0x42412fef80804462 0x442412fef8080446 0x7033ffff8403c7f7 0xd7033ffff8403c7f

def z839 : W := mkw 0x040a00001854a984 0x8040a00001854a98 0xfe0f0c0e787cf9cf 0x7fe0f0c0e787cf9c

def z840 : W := mkw 0x0930100066090000 0x0093010006609000 0x8ff370007f9c000c 0xf8ff370007f9c000

def z841 : W := mkw 0x5fefefefaa00a004 0x05fefefefaa00a00 0x4fffffffb8000003 0xf4fffffffb800000

def z842 : W := mkw 0x3b705ed06e89f60f 0x03b705ed06e89f60 0xdff07ff07f80fe0e 0xfdff07ff07f80fe0

def z843 : W := mkw 0x09a5e12880000000 0x009a5e1288000000 0x01f3f3f980000003 0xd01f3f3f98000000

def z844 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f37980000001 0x40033f3798000000

def z845 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff00ff07fe0ffce 0xffff00ff07fe0ffc

def z846 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0xdff00f707f80f80e 0xfdff00f707f80f80

def z847 : W := mkw 0x4f2b6b6c9854a984 0x84f2b6b6c9854a98 0xbe337370787cf9cc 0x4be337370787cf9c

def z848 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0xfe3ffffffc7fffff 0xffe3ffffffc7ffff

def z849 : W := mkw 0x448fe12f90540980 0x8448fe12f9054098 0xb03ff3ffc07c39c7 0xdb03ff3ffc07c39c

def z850 : W := mkw 0x6f2b6b6cb2500008 0x06f2b6b6cb250000 0x0e33737038000000 0x40e3373703800000

def z851 : W := mkw 0x00501490448d5f13 0xa00501490448d5f1 0xf1c00c80479fff3e 0xbf1c00c80479fff3

def z852 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x4fffffff80030033 0xf4fffffff8003003

def z853 : W := mkw 0x4fefefef89a6ede6 0xc4fefefef89a6ede 0x7fffffff87e3ffff 0xf7fffffff87e3fff

def z854 : W := mkw 0x52412fff8884ff87 0x852412fff8884ff8 0x50000fff8000ffc2 0x050000fff8000ffc

def z855 : W := mkw 0x6fefefefb2500008 0x06fefefefb250000 0x4fffffffb8000003 0xf4fffffffb800000

def z856 : W := mkw 0x040b212880000000 0x0040b21288000000 0x0e3ff3f980000003 0xf0e3ff3f98000000

def z857 : W := mkw 0x0001212880000000 0x0000121288000000 0x0030f3f980000002 0x80030f3f98000000

def z858 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff0807fff060f 0xfbffff0807fff060

def z859 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x7fffffff8783c73f 0xf7fffffff8783c73

def z860 : W := mkw 0x4fefefef8804a904 0x84fefefef8804a90 0xfffffffff81cf90f 0xffffffffff81cf90

def z861 : W := mkw 0x00949010452f1b11 0xa00949010452f1b1 0xb1cc800047ff3f3d 0xbb1cc800047ff3f3

def z862 : W := mkw 0x0faeca4000000000 0x00faeca400000000 0x0ffff37000000001 0xf0ffff3700000000

def z863 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff009ffff013d 0xfaffff009ffff013

def z864 : W := mkw 0x00d5b5bbc5af5f73 0xe00d5b5bbc5af5f7 0xc1ff7f7643fcf8c8 0x6c1ff7f7643fcf8c

def z865 : W := mkw 0x00d4949345ab5673 0x600d4949345ab567 0x71cc8c8f87e3c7ff 0xb71cc8c8f87e3c7f

def z866 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f3f180000000 0xc0033f3f18000000

def z867 : W := mkw 0x00c4a4a380000000 0x000c4a4a38000000 0x01f0f0f180000000 0x801f0f0f18000000

def z868 : W := mkw 0x249ed010557b1209 0x0249ed010557b120 0xb03ff3f0447f3e07 0xdb03ff3f0447f3e0

def z869 : W := mkw 0x12400ed00880f607 0x012400ed00880f60 0xdfc00ff07f80fe0e 0xfdfc00ff07f80fe0

def z870 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x4e3f7fff80000003 0x74e3f7fff8000000

def z871 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000089c41f3f36 0x0b0000089c41f3f3

def z872 : W := mkw 0x0deec4c000000000 0x00deec4c00000000 0x0ffff0f000000001 0xf0ffff0f00000000

def z873 : W := mkw 0x4f2b6b6c8800a004 0x04f2b6b6c8800a00 0x8e33737078003800 0x48e3373707800380

def z874 : W := mkw 0x4be4eee380000000 0x04be4eee38000000 0x41f0fff180000002 0x841f0fff18000000

def z875 : W := mkw 0x00d4949345af5f73 0xe00d4949345af5f7 0xf1cc0c0647fffffc 0x2f1cc0c0647fffff

def z876 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdfc00ff07f80fe0e 0x2dfc00ff07f80fe0

def z877 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fff7ff600000002 0xf4fff7ff60000000

def z878 : W := mkw 0x0010101044091211 0x2001010104409121 0x0000000000000000 0x0000000000000000

def z879 : W := mkw 0x4deee4e780000000 0x04deee4e78000000 0x01fcf0f780000000 0x801fcf0f78000000

def z880 : W := mkw 0x4feecec719f2e4e6 0x44feecec719f2e4e 0x4fcc0c063be0c0c8 0x24fcc0c063be0c0c

def z881 : W := mkw 0x4fefefef8800a004 0x04fefefef8800a00 0xcffffffff8003803 0xfcffffffff800380

def z882 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4ffffcff80000001 0xa4ffffcff8000000

def z883 : W := mkw 0x0001212880000000 0x0000121288000000 0x1033f3f984000607 0xd1033f3f98400060

def z884 : W := mkw 0x42412fef80000000 0x042412fef8000000 0x40337fff80000002 0x440337fff8000000

def z885 : W := mkw 0x1b600ed02a80f607 0x01b600ed02a80f60 0x4fc00f703b80f808 0x24fc00f703b80f80

def z886 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0x8ff370007f9c0000 0xc8ff370007f9c000

def z887 : W := mkw 0x0010101044091211 0x2001010104409121 0x3000000004030734 0x0300000000403073

def z888 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01fcf0f180000001 0xb01fcf0f18000000

def z889 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb033f3f9c01f3f33 0x4b033f3f9c01f3f3

def z890 : W := mkw 0x0001212881a24462 0x40001212881a2446 0x3033f3f987e3c7ff 0xd3033f3f987e3c7f

def z891 : W := mkw 0x6fefefefb3720008 0x06fefefefb372000 0x6fffffffbfe3000f 0xf6fffffffbfe3000

def z892 : W := mkw 0x2dafe138b3761b19 0xa2dafe138b3761b1 0x1fcc03f9bbe03f3a 0x21fcc03f9bbe03f3

def z893 : W := mkw 0x4fefefef91f64de2 0xc4fefefef91f64de 0x7fffffff87ffc7ff 0xf7fffffff87ffc7f

def z894 : W := mkw 0x00c5a5ab81a64d62 0xc00c5a5ab81a64d6 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z895 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x20000000041f0730 0x020000000041f073

def z896 : W := mkw 0x1d7b05dc76d45f83 0x81d7b05dc76d45f8 0x21ff00fe07fc07c1 0x821ff00fe07fc07c

def z897 : W := mkw 0x00d4949345af5f73 0xe00d4949345af5f7 0xb1c08081c79f3f34 0x8b1c08081c79f3f3

def z898 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0xf1cf8c8fc7ffc7ff 0xff1cf8c8fc7ffc7f

def z899 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xa0000000441f3804 0x0a0000000441f380

def z900 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff08ff9ff80fe0f 0xfdff08ff9ff80fe0

def z901 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc0c8f87e3c7fe 0x271cc0c8f87e3c7f

def z902 : W := mkw 0x2dbed003777b0008 0x02dbed003777b000 0xaffff00fffff000d 0xfaffff00fffff000

def z903 : W := mkw 0x42412fef80000000 0x042412fef8000000 0x4030ffff80000002 0x84030ffff8000000

def z904 : W := mkw 0x4fefefef8800a004 0x04fefefef8800a00 0x4fffffffb800c00b 0xf4fffffffb800c00

def z905 : W := mkw 0x42412fef8804a984 0x842412fef8804a98 0xf033ffffc01cf9c7 0xdf033ffffc01cf9c

def z906 : W := mkw 0x4fafeb6f9854a984 0x84fafeb6f9854a98 0xfe3fff7ff87cf9cf 0x7fe3fff7ff87cf9c

def z907 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff3fff07f80fe0f 0xfdff3fff07f80fe0

def z908 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x4fff7ffe00000003 0xf4fff7ffe0000000

def z909 : W := mkw 0x4fefefef8804a984 0x84fefefef8804a98 0x7fffffff8060f9cf 0xf7fffffff8060f9c

def z910 : W := mkw 0x0001212880040900 0x8000121288004090 0xb0337378401c3907 0x5b0337378401c390

def z911 : W := mkw 0x4f2b6b6c90500000 0x04f2b6b6c9050000 0x8e337370781c0000 0x48e337370781c000

def z912 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff30ff07f9cfe0f 0xffff30ff07f9cfe0

def z913 : W := mkw 0x1b700ed36e80f667 0x41b700ed36e80f66 0xfffc0fffffe0ffff 0xffffc0fffffe0fff

def z914 : W := mkw 0x49e4e4e381220000 0x049e4e4e38122000 0x21fcf0f187e3000d 0xb21fcf0f187e3000

def z915 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x4ffffcf780000001 0xf4ffffcf78000000

def z916 : W := mkw 0x4fefefef90500000 0x04fefefef9050000 0xcffffffff81c0003 0xfcffffffff81c000

def z917 : W := mkw 0x4fefefef98d4ed86 0x84fefefef98d4ed8 0xfffffffffffcffcf 0xffffffffffffcffc

def z918 : W := mkw 0x0fefcfcc1854a984 0x80fefcfcc1854a98 0xfffffffe787cf9cf 0xffffffffe787cf9c

def z919 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x1000000004033f30 0x01000000004033f3

def z920 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f8f0ff87ff9ff 0x7fe0f8f0ff87ff9f

def z921 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00ff07b80fe0a 0x6dff00ff07b80fe0

def z922 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x0ff0f0f180000000 0x80ff0f0f18000000

def z923 : W := mkw 0x4dafe12f80000000 0x04dafe12f8000000 0x0ffff3ff80000003 0xf0ffff3ff8000000

def z924 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0008009c41f3f35 0x0b0008009c41f3f3

def z925 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x61cc8c8f87e3c7f9 0xa61cc8c8f87e3c7f

def z926 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f8f8ff87cf9cf 0xffe0f8f8ff87cf9c

def z927 : W := mkw 0x4defe5ef80000000 0x04defe5ef8000000 0x41fffcff80000003 0xb41fffcff8000000

def z928 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4ffffff780000000 0xe4ffffff78000000

def z929 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f8e7c7cffcf 0xffe0f0f8e7c7cffc

def z930 : W := mkw 0x29f4f4b3e7ab567b 0x629f4f4b3e7ab567 0x01f0f0f187830630 0x801f0f0f18783063

def z931 : W := mkw 0x0fafeb2c9854a984 0x80fafeb2c9854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z932 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x0e3ff3ff80000003 0xd0e3ff3ff8000000

def z933 : W := mkw 0x4d2a606080000000 0x04d2a60608000000 0x0e33707000000000 0x40e3370700000000

def z934 : W := mkw 0x2dbed010777f1b19 0xa2dbed010777f1b1 0xbfcc00007fff3f3c 0x2bfcc00007fff3f3

def z935 : W := mkw 0x06df9f9f5dfffff7 0xe06df9f9f5dfffff 0xffcf8f8fffffffff 0xfffcf8f8ffffffff

def z936 : W := mkw 0x4fefefef98d4ede6 0xc4fefefef98d4ede 0xfffffffff87cffff 0xffffffffff87cfff

def z937 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff00ff07f83ff3e 0xffff00ff07f83ff3

def z938 : W := mkw 0x1bb48a536f22b265 0x41bb48a536f22b26 0xae3c837ff86339f1 0x4ae3c837ff86339f

def z939 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xdffffffff81cf9c3 0xfdffffffff81cf9c

def z940 : W := mkw 0x448fe12f80000000 0x0448fe12f8000000 0x003ff0ff80000001 0x8003ff0ff8000000

def z941 : W := mkw 0x4deee4e380000000 0x04deee4e38000000 0x4ffffcff80000003 0xf4ffffcff8000000

def z942 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xfffffffff81c3907 0xffffffffff81c390

def z943 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x4e337ff000000002 0x44e337ff00000000

def z944 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xafcff0007fff000d 0x2afcff0007fff000

def z945 : W := mkw 0x4fefefef8884ede6 0xc4fefefef8884ede 0x5fffffff8000fff3 0xf5fffffff8000fff

def z946 : W := mkw 0x0930001066001201 0x0093000106600120 0x8ff003707f80380c 0xf8ff003707f80380

def z947 : W := mkw 0x02012b2c8804a984 0x802012b2c8804a98 0x5033ffff8000f9c3 0xd5033ffff8000f9c

def z948 : W := mkw 0x4fefefef90540980 0x84fefefef9054098 0x7fffffff807cc1cf 0xf7fffffff807cc1c

def z949 : W := mkw 0x39f4d4d367ab566b 0x439f4d4d367ab566 0x01f0f0f187830630 0x801f0f0f18783063

def z950 : W := mkw 0x4fafeb6c9854a984 0x84fafeb6c9854a98 0xffffff7e787cf9cf 0xfffffff7e787cf9c

def z951 : W := mkw 0x49e5e5eb80000000 0x049e5e5eb8000000 0x01f3f0f980000001 0x801f3f0f98000000

def z952 : W := mkw 0x62513feff77b0008 0x062513feff77b000 0xe0000fffffff000e 0x0e0000fffffff000

def z953 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ffff0007bfc0009 0xf8ffff0007bfc000

def z954 : W := mkw 0x2dbed010777b1219 0x22dbed010777b121 0xaffff0007fff063d 0xfaffff0007fff063

def z955 : W := mkw 0x42412fef8884ede6 0xc42412fef8884ede 0x50000fff8000fff2 0x050000fff8000fff

def z956 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb033f3f9c47fffff 0xdb033f3f9c47ffff

def z957 : W := mkw 0x4fefefef9976a984 0x84fefefef9976a98 0xfffffffffffff9cf 0xffffffffffffff9c

def z958 : W := mkw 0x02012b2c80000000 0x002012b2c8000000 0x4033ffff80000003 0xd4033ffff8000000

def z959 : W := mkw 0x4fefefef90500080 0x04fefefef9050008 0x4fffffff806000c3 0xf4fffffff806000c

def z960 : W := mkw 0x4fefefef99f2e4e6 0x44fefefef99f2e4e 0x4fffffffbbe0c0cb 0xf4fffffffbbe0c0c

def z961 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdffc0ff67fe0fece 0xfdffc0ff67fe0fec

def z962 : W := mkw 0x105014906e8dff17 0xa105014906e8dff1 0xf1c08c89ff9fff3f 0xbf1c08c89ff9fff3

def z963 : W := mkw 0x0011313cc40d1b91 0xa0011313cc40d1b9 0xb033f3ffc41f3ff7 0xdb033f3ffc41f3ff

def z964 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffffff84030633 0xf4fffffff8403063

def z965 : W := mkw 0x1b701ed06e89f607 0x01b701ed06e89f60 0xdff37ff07f9cfe0e 0xfdff37ff07f9cfe0

def z966 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x7fffffff83e0c1cf 0xf7fffffff83e0c1c

def z967 : W := mkw 0x00c4a4a380000000 0x000c4a4a38000000 0x41fcfcff80000003 0xb41fcfcff8000000

def z968 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0xfe0fff0ff87cf9cf 0x7fe0fff0ff87cf9c

def z969 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff0007fff0001 0xcaffff0007fff000

def z970 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0038389c41f3f37 0xdb0038389c41f3f3

def z971 : W := mkw 0x0001212880000000 0x0000121288000000 0x703fffff8060c1cf 0xf703fffff8060c1c

def z972 : W := mkw 0x4fefefef9976a9e4 0xc4fefefef9976a9e 0xfffffffff87ff9ff 0xffffffffff87ff9f

def z973 : W := mkw 0x060b2b2c9850a084 0x0060b2b2c9850a08 0x4e3fffffb860c0cb 0xf4e3fffffb860c0c

def z974 : W := mkw 0x040b212c90540980 0x8040b212c9054098 0x200ff00f807c01c1 0x0200ff00f807c01c

def z975 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xcff00ff07b80f80a 0xfcff00ff07b80f80

def z976 : W := mkw 0x248ff12b917f0978 0xe248ff12b917f097 0x200ff00f807f01f1 0x0200ff00f807f01f

def z977 : W := mkw 0x0010101045ab5673 0x60010101045ab567 0x3000000007e3c7fc 0x03000000007e3c7f

def z978 : W := mkw 0x0be5afeb80000000 0x00be5afeb8000000 0x4fffffff80000003 0xf4fffffff8000000

def z979 : W := mkw 0x02012b2880000000 0x002012b288000000 0x4e33fff980000003 0xf4e33fff98000000

def z980 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0ff3737000000000 0xf0ff373700000000

def z981 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x0ffff3f980000003 0xf0ffff3f98000000

def z982 : W := mkw 0x0001212880000000 0x0000121288000000 0x2033f3f984030007 0xd2033f3f98403000

def z983 : W := mkw 0x4920606080000000 0x0492060608000000 0x0030f0f180000000 0x80030f0f18000000

def z984 : W := mkw 0x4feeeee380000000 0x04feeeee38000000 0x4ffffff180000003 0xf4ffffff18000000

def z985 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f3f0f180000001 0xd01f3f0f18000000

def z986 : W := mkw 0x261b1b1c7f7fbb9d 0xa261b1b1c7f7fbb9 0xfe0f0f0e7fffffff 0x7fe0f0f0e7ffffff

def z987 : W := mkw 0x361b1b1c7fffff8f 0x8361b1b1c7fffff8 0xfe0f0f0e7fffffcf 0x7fe0f0f0e7fffffc

def z988 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x9ff003f07f803e0e 0xf9ff003f07f803e0

def z989 : W := mkw 0x4fefefefa2000000 0x04fefefefa200000 0x4fffffffbb80000b 0xf4fffffffbb80000

def z990 : W := mkw 0x12111b186e8dff17 0xa12111b186e8dff1 0xfe030f087f9fff3f 0x7fe030f087f9fff3

def z991 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xdffffffff81cf80f 0xfdffffffff81cf80

def z992 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x4e33ffff80000003 0xd4e33ffff8000000

def z993 : W := mkw 0x0daee02080000000 0x00daee0208000000 0x0ffff0f180000001 0xf0ffff0f18000000

def z994 : W := mkw 0x20101010777b1209 0x020101010777b120 0xb00000007fff3e0c 0x0b00000007fff3e0

def z995 : W := mkw 0x060a0a041854a984 0x8060a0a041854a98 0xfe0c0c0e787cf9cf 0x3fe0c0c0e787cf9c

def z996 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x41ffffff80000003 0x841ffffff8000000

def z997 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ffff0007f9f0001 0xf8ffff0007f9f000

def z998 : W := mkw 0x49e4e4e381220060 0x449e4e4e38122006 0x21fcf0ff806301f1 0x821fcf0ff806301f

def z999 : W := mkw 0x004125a880804402 0x0004125a88080440 0x51f3fff98780c60f 0xf51f3fff98780c60

def z1000 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xa033f3f1c41f3e35 0xda033f3f1c41f3e3

def z1001 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4ff3fff180000002 0xf4ff3fff18000000

def z1002 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xf033fff9c41fff3f 0xff033fff9c41fff3

def z1003 : W := mkw 0x301010107ffbf66f 0x4301010107ffbf66 0xb00000007ffffffc 0x0b00000007ffffff

def z1004 : W := mkw 0x20101010557f1b19 0xa20101010557f1b1 0xb0000000447f3f34 0x0b0000000447f3f3

def z1005 : W := mkw 0x0000202080000000 0x0000020208000000 0x0030f0f184030630 0x80030f0f18403063

def z1006 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaff3f0007fff000c 0xcaff3f0007fff000

def z1007 : W := mkw 0x060b2b2c80000000 0x0060b2b2c8000000 0x4e3f7f7e00000003 0x74e3f7f7e0000000

def z1008 : W := mkw 0x0b300a106e00b205 0x00b300a106e00b20 0xdff00ff07f80fe0e 0xfdff00ff07f80fe0

def z1009 : W := mkw 0x464b2fef80000000 0x0464b2fef8000000 0x4e3fffff80000003 0xf4e3fffff8000000

def z1010 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01fcf0ff80000001 0x801fcf0ff8000000

def z1011 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000000401c3904 0x0b0000000401c390

def z1012 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fff7fff80000002 0x64fff7fff8000000

def z1013 : W := mkw 0x0dafe12890540900 0x80dafe1289054090 0xbffff3f9f87c390f 0xfbffff3f9f87c390

def z1014 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff081ffff063d 0xfaffff081ffff063

def z1015 : W := mkw 0x2dbed004777b0088 0x02dbed004777b008 0xaffff0067fff00cd 0xfaffff0067fff00c

def z1016 : W := mkw 0x060a0a041850a084 0x0060a0a041850a08 0xfe0f0f06787cf8cf 0x7fe0f0f06787cf8c

def z1017 : W := mkw 0x00c5a5ab80040900 0x800c5a5ab8004090 0xf1ffffffc07cf9cf 0xff1ffffffc07cf9c

def z1018 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f0f980000001 0x80033f0f98000000

def z1019 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0000308441f3f36 0x0b0000308441f3f3

def z1020 : W := mkw 0x4f6b6fec9854a984 0x84f6b6fec9854a98 0xffff7ffe787cf9cf 0xfffff7ffe787cf9c

def z1021 : W := mkw 0x4f2a6a6480000000 0x04f2a6a648000000 0x0e30707000000000 0x00e3070700000000

def z1022 : W := mkw 0x197004d066805603 0x0197004d06680560 0x01c0000007800600 0x001c000000780060

def z1023 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x9033f3f9c41f3f32 0xc9033f3f9c41f3f3

def z1024 : W := mkw 0x12412ffb8884ff77 0xe12412ffb8884ff7 0x50000fff8000fff2 0x050000fff8000fff

def z1025 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0xefffffffc01c0007 0xfefffffffc01c000

def z1026 : W := mkw 0x101010106e89f607 0x0101010106e89f60 0xb00000007f9ffe0c 0x0b00000007f9ffe0

def z1027 : W := mkw 0x004125ab80804462 0x4004125ab8080446 0x5033ffff8000c7f3 0xd5033ffff8000c7f

def z1028 : W := mkw 0x2dbed00076590008 0x02dbed0007659000 0x8ffff0007f9c000d 0xf8ffff0007f9c000

def z1029 : W := mkw 0x301010107ed9f60f 0x0301010107ed9f60 0x900000007f9cfe0c 0x0900000007f9cfe0

def z1030 : W := mkw 0x6fefefefa3220008 0x06fefefefa322000 0x4fffffff83800003 0xf4fffffff8380000

def z1031 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x4e3f7f7600000000 0x64e3f7f760000000

def z1032 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f8ff87cffff 0x7fe0f0f8ff87cfff

def z1033 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x4ffcfcff80000003 0xb4ffcfcff8000000

def z1034 : W := mkw 0x0feecec301a24462 0x40feecec301a2446 0x7fffffff87e3c7ff 0xf7fffffff87e3c7f

def z1035 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x0ff0f0f180000000 0xf0ff0f0f18000000

def z1036 : W := mkw 0x4be5efef81a24462 0x44be5efef81a2446 0x51f0ffff8783c7f2 0x851f0ffff8783c7f

def z1037 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x0ff3737000000000 0x40ff373700000000

def z1038 : W := mkw 0x0085a12881220000 0x00085a1288122000 0x21fff3f987e3000f 0xf21fff3f987e3000

def z1039 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ff3f0007f9f000c 0xf8ff3f0007f9f000

def z1040 : W := mkw 0x101010106e8dff17 0xa101010106e8dff1 0x900000007f9cfe0c 0x0900000007f9cfe0

def z1041 : W := mkw 0x49e4e4e380804402 0x049e4e4e38080440 0x51f0fcf18780c60e 0xb51f0fcf18780c60

def z1042 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x4ff3fff980000003 0xf4ff3fff98000000

def z1043 : W := mkw 0x4fefefef8804a984 0x84fefefef8804a98 0xffffffffc01cf9c7 0xfffffffffc01cf9c

def z1044 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb1f3f3f9c79f3f3f 0xfb1f3f3f9c79f3f3

def z1045 : W := mkw 0x0085a12880000000 0x00085a1288000000 0x01fff3f980000003 0xf01fff3f98000000

def z1046 : W := mkw 0x09e4c4c000000000 0x009e4c4c00000000 0x01f0f0f000000000 0x801f0f0f00000000

def z1047 : W := mkw 0x49e5e5ef80000000 0x049e5e5ef8000000 0x01f0f0ff80000000 0x801f0f0ff8000000

def z1048 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xafff70007bfc000d 0x7afff70007bfc000

def z1049 : W := mkw 0x0b612fe88804a904 0x80b612fe88804a90 0xfff3fff9f81cf90f 0xffff3fff9f81cf90

def z1050 : W := mkw 0x060a0a041854a984 0x8060a0a041854a98 0xce0c0c06787cf8c8 0x2ce0c0c06787cf8c

def z1051 : W := mkw 0x004125ab80000000 0x0004125ab8000000 0x4033ffff80000003 0xd4033ffff8000000

def z1052 : W := mkw 0x4be4eee38800a004 0x04be4eee38800a00 0xdff0fff1f800f80e 0xfdff0fff1f800f80

def z1053 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff00ff87f80ff0f 0xffff00ff87f80ff0

def z1054 : W := mkw 0x44cfe5af81a24462 0x444cfe5af81a2446 0x71ffffff87e3c7ff 0xf71ffffff87e3c7f

def z1055 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x0e3ff37000000001 0x40e3ff3700000000

def z1056 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffff7600000001 0xf4fffff760000000

def z1057 : W := mkw 0x648ff12f917f0988 0x8648ff12f917f098 0x200ff00f807f01c1 0x0200ff00f807f01c

def z1058 : W := mkw 0x301010107fffff1f 0xa301010107fffff1 0xb00000007fffff3c 0x0b00000007fffff3

def z1059 : W := mkw 0x00d494935dfffff7 0xe00d494935dfffff 0xf1cc8c8fffffffff 0xbf1cc8c8ffffffff

def z1060 : W := mkw 0x2fbffb2cff7fa98c 0x82fbffb2cff7fa98 0xfffffffffffff9cf 0xffffffffffffff9c

def z1061 : W := mkw 0x2010101077ff5f7b 0xe2010101077ff5f7 0xb00000007ffffffc 0x0b00000007ffffff

def z1062 : W := mkw 0x4fafeb6c9854a984 0x84fafeb6c9854a98 0xaffff370787c380d 0xfaffff370787c380

def z1063 : W := mkw 0x12501ed04c89f607 0x012501ed04c89f60 0xf033fff0441ffe07 0xdf033fff0441ffe0

def z1064 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xce0f0f0e787cf8cb 0x7ce0f0f0e787cf8c

def z1065 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x4fffffff806000c3 0xf4fffffff806000c

def z1066 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xafff70007fff000c 0x6afff70007fff000

def z1067 : W := mkw 0x0085a12b81220060 0x40085a12b8122006 0x203ff3ff806301f3 0xd203ff3ff806301f

def z1068 : W := mkw 0x2dbed010777b1209 0x02dbed010777b120 0xbffff0007fff3e0d 0xfbffff0007fff3e0

def z1069 : W := mkw 0x4f2b6b6f80000000 0x04f2b6b6f8000000 0x0e33737f80000000 0x40e33737f8000000

def z1070 : W := mkw 0x0000000000000000 0x0000000000000000 0x0033f3f000000003 0xd0033f3f00000000

def z1071 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x7fffffff87e0c7cf 0xf7fffffff87e0c7c

def z1072 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x4ffcfff780000002 0xf4ffcfff78000000

def z1073 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0c0e787cf9cd 0x2fe0f0c0e787cf9c

def z1074 : W := mkw 0x0000202080000000 0x0000020208000000 0x0030f3f180000002 0xd0030f3f18000000

def z1075 : W := mkw 0x101010106e0dbb15 0xa101010106e0dbb1 0x80000000781c3800 0x080000000781c380

def z1076 : W := mkw 0x0fefcfcc00000000 0x00fefcfcc0000000 0x4ffffffe00000003 0xf4ffffffe0000000

def z1077 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xfffffffffc7fffff 0xffffffffffc7ffff

def z1078 : W := mkw 0x1b700ed46e80f687 0x01b700ed46e80f68 0xdff00ff67f80fece 0xfdff00ff67f80fec

def z1079 : W := mkw 0x404125eb80000000 0x0404125eb8000000 0x0033f3f980000003 0xd0033f3f98000000

def z1080 : W := mkw 0x4f2b6b6c9850a084 0x04f2b6b6c9850a08 0x0e33737038000000 0x40e3373703800000

def z1081 : W := mkw 0x1b700ed06e80f667 0x41b700ed06e80f66 0xdff00ff07f80fffe 0xfdff00ff07f80fff

def z1082 : W := mkw 0x5fefefefaa80e406 0x05fefefefaa80e40 0x5fffffffbf80c60f 0xf5fffffffbf80c60

def z1083 : W := mkw 0x4be4eee381a24462 0x44be4eee381a2446 0x5ff0fff18783c63e 0xf5ff0fff18783c63

def z1084 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x7fffffff8060c7ff 0xf7fffffff8060c7f

def z1085 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x8ff003707b803800 0x48ff003707b80380

def z1086 : W := mkw 0x0d2b612880000000 0x00d2b61288000000 0x0e33737000000000 0x40e3373700000000

def z1087 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x5fffffff8000c1c3 0xf5fffffff8000c1c

def z1088 : W := mkw 0x4fefefef9850a084 0x04fefefef9850a08 0x4fffffffb8000003 0xf4fffffffb800000

def z1089 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x7fffffff8403c7f7 0xf7fffffff8403c7f

def z1090 : W := mkw 0x0001212880000000 0x0000121288000000 0x3033f3f980000107 0xd3033f3f98000010

def z1091 : W := mkw 0x4fefefef80804462 0x44fefefef8080446 0x5fffffff8780c7ff 0xf5fffffff8780c7f

def z1092 : W := mkw 0x4fafeb6f9854a984 0x84fafeb6f9854a98 0xae3ff37ff87c39c1 0x4ae3ff37ff87c39c

def z1093 : W := mkw 0x440b612c80000000 0x0440b612c8000000 0x0033f3f980000003 0xd0033f3f98000000

def z1094 : W := mkw 0x4be5efef80000000 0x04be5efef8000000 0x01f0f3f180000000 0x801f0f3f18000000

def z1095 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x7fffffff80000107 0xf7fffffff8000010

def z1096 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xcfff7f76787cf8c8 0x6cfff7f76787cf8c

def z1097 : W := mkw 0x4f6b6fef9854a984 0x84f6b6fef9854a98 0xfe3f7ffff87cf9cf 0x7fe3f7ffff87cf9c

def z1098 : W := mkw 0x4921616880000000 0x0492161688000000 0x0033737000000000 0x4003373700000000

def z1099 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f0f0f980000003 0x901f0f0f98000000

def z1100 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0c0f0e787cf9ce 0x2fe0c0f0e787cf9c

def z1101 : W := mkw 0x2dafe128b3720008 0x02dafe128b372000 0x0ffff3f9bbe0000b 0xf0ffff3f9bbe0000

def z1102 : W := mkw 0x1b300a506e80f607 0x01b300a506e80f60 0x9ff003707f80fe0c 0xf9ff003707f80fe0

def z1103 : W := mkw 0x0010101044091201 0x0001010104409120 0xb0000000441f3e04 0x0b0000000441f3e0

def z1104 : W := mkw 0x49e5e5eb80000000 0x049e5e5eb8000000 0x01f3f3f180000000 0xc01f3f3f18000000

def z1105 : W := mkw 0x02000a000800a004 0x002000a000800a00 0xde300ff07800f80e 0xfde300ff07800f80

def z1106 : W := mkw 0x4fefefef90500000 0x04fefefef9050000 0x6fffffff807c0003 0xf6fffffff807c000

def z1107 : W := mkw 0x4fefefef8880e406 0x04fefefef8880e40 0xdfffffffff80fe0f 0xfdfffffffff80fe0

def z1108 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x4e337f7000000002 0x74e337f700000000

def z1109 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x7fffffff87e3c1cf 0xf7fffffff87e3c1c

def z1110 : W := mkw 0x49e4e4e381a24462 0x449e4e4e381a2446 0x01f0f0f183800000 0x801f0f0f18380000

def z1111 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0xdfffffffc0003807 0xfdfffffffc000380

def z1112 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x01c0000007830630 0x001c000000783063

def z1113 : W := mkw 0x5fefefef8880e406 0x05fefefef8880e40 0x4fffffff8000c003 0xf4fffffff8000c00

def z1114 : W := mkw 0x040b212c90540980 0x8040b212c9054098 0x203ff3ff807c01c3 0xd203ff3ff807c01c

def z1115 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x7e3f7f7e0060c1cf 0x77e3f7f7e0060c1c

def z1116 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff0007fff073d 0xfbffff0007fff073

def z1117 : W := mkw 0x060b2b2c80000000 0x0060b2b2c8000000 0x0e33f3f980000003 0xd0e33f3f98000000

def z1118 : W := mkw 0x4f2b6b6c90540980 0x84f2b6b6c9054098 0x2e3f737e007c01c1 0x42e3f737e007c01c

def z1119 : W := mkw 0x0001212880040900 0x8000121288004090 0x1033f3f980003903 0xd1033f3f98000390

def z1120 : W := mkw 0x00013138800d1b11 0xa00013138800d1b1 0x3033f3f9801f3f33 0xd3033f3f9801f3f3

def z1121 : W := mkw 0x49e4e4e380804462 0x449e4e4e38080446 0x51f0fcff8000c7f2 0x851f0fcff8000c7f

def z1122 : W := mkw 0x09313128e60d0910 0xa09313128e60d091 0xaff3f009ff9f013d 0xfaff3f009ff9f013

def z1123 : W := mkw 0x30d494937ffbf66f 0x430d494937ffbf66 0xf1cc8c8fffffffff 0xbf1cc8c8ffffffff

def z1124 : W := mkw 0x6fefefefb3720008 0x06fefefefb372000 0xeffffffffbfc000f 0xfeffffffffbfc000

def z1125 : W := mkw 0x464b2fef9854a984 0x8464b2fef9854a98 0xfe3ffffff87cf9cf 0xffe3ffffff87cf9c

def z1126 : W := mkw 0x0010101044091211 0x2001010104409121 0xa0000000441f0634 0x0a0000000441f063

def z1127 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x7fffffff8063c1ff 0xf7fffffff8063c1f

def z1128 : W := mkw 0x4fefefef90540980 0x84fefefef9054098 0xeffffffff87c01cf 0xfeffffffff87c01c

def z1129 : W := mkw 0x0010101044091211 0x2001010104409121 0x3000808984030737 0x9300080898403073

def z1130 : W := mkw 0x4fefefef91f24462 0x44fefefef91f2446 0xffffffffffffc7ff 0xfffffffffffffc7f

def z1131 : W := mkw 0x049e9000557b0000 0x0049e9000557b000 0xaffff0007fff000d 0xfaffff0007fff000

def z1132 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4ff3ffff80000002 0xc4ff3ffff8000000

def z1133 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x5fffffff83e0c7fb 0xf5fffffff83e0c7f

def z1134 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f0f3f180000002 0xd01f0f3f18000000

def z1135 : W := mkw 0x4defe5ef81a24462 0x44defe5ef81a2446 0x71fffcff87e3c7ff 0xb71fffcff87e3c7f

def z1136 : W := mkw 0x4fefefef80040980 0x84fefefef8004098 0x4fffffff800001c3 0xf4fffffff800001c

def z1137 : W := mkw 0x6fefefefbb76a98c 0x86fefefefbb76a98 0xfffffffffbfcf9cf 0xffffffffffbfcf9c

def z1138 : W := mkw 0x4be5efeb80000000 0x04be5efeb8000000 0x4ff3fff980000003 0xf4ff3fff98000000

def z1139 : W := mkw 0x20101010672b1219 0x220101010672b121 0x0000000007830630 0x0000000000783063

def z1140 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x5fffffff8000c00f 0xf5fffffff8000c00

def z1141 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x5fffffff8783c7f3 0xf5fffffff8783c7f

def z1142 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fff7f7e00000003 0x74fff7f7e0000000

def z1143 : W := mkw 0x4fefefef8800a004 0x04fefefef8800a00 0xfffffffff860f9cf 0xffffffffff860f9c

def z1144 : W := mkw 0x4defe5ef80000000 0x04defe5ef8000000 0x0ffff0ff80000001 0xf0ffff0ff8000000

def z1145 : W := mkw 0x0001212880040910 0xa000121288004091 0x0033f3f980000133 0xd0033f3f98000013

def z1146 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4ffcffff80000002 0xa4ffcffff8000000

def z1147 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x7fffffff87830737 0xf7fffffff8783073

def z1148 : W := mkw 0x0010101044091211 0x2001010104409121 0x9000000044033e34 0x09000000044033e3

def z1149 : W := mkw 0x060b2b2c9854a994 0xa060b2b2c9854a99 0xfe0f0f0ff87cf9ff 0x7fe0f0f0ff87cf9f

def z1150 : W := mkw 0x00d4949345ab5673 0x600d4949345ab567 0x01c0808187830630 0x801c080818783063

def z1151 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x5fffffff8000c603 0xf5fffffff8000c60

def z1152 : W := mkw 0x5be4eee3aa80e406 0x05be4eee3aa80e40 0x4ff0fcf1bb80c008 0xa4ff0fcf1bb80c00

def z1153 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdffc0ffe7f80fe0f 0xfdffc0ffe7f80fe0

def z1154 : W := mkw 0x061b1b1c5c5dbb95 0xa061b1b1c5c5dbb9 0xfe0f0f0e787cf9cf 0x7fe0f0f0e787cf9c

def z1155 : W := mkw 0x09a4e02080000000 0x009a4e0208000000 0x01f0f0f180000000 0x801f0f0f18000000

def z1156 : W := mkw 0x061b1b1c5dfffff7 0xe061b1b1c5dfffff 0xfe0f0f0e7fffffff 0x7fe0f0f0e7ffffff

def z1157 : W := mkw 0x20101010765d1b19 0xa20101010765d1b1 0x80000000781c3800 0x080000000781c380

def z1158 : W := mkw 0x197004d066805603 0x0197004d06680560 0x9ff003f07f803e0e 0xf9ff003f07f803e0

def z1159 : W := mkw 0x5f6b6fecaa80e406 0x05f6b6fecaa80e40 0x4ff37f703b80c008 0x64ff37f703b80c00

def z1160 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0xaff3f0007f9f000d 0xfaff3f0007f9f000

def z1161 : W := mkw 0x1b701ed06e89f607 0x01b701ed06e89f60 0xfff00ff07f9ffe0e 0xffff00ff07f9ffe0

def z1162 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0030008441f3f35 0x0b0030008441f3f3

def z1163 : W := mkw 0x5fefefefaba2e466 0x45fefefefaba2e46 0x7fffffffbfe3c7ff 0xf7fffffffbfe3c7f

def z1164 : W := mkw 0x2dbed000777b0068 0x42dbed000777b006 0xaffff0007fff01fd 0xfaffff0007fff01f

def z1165 : W := mkw 0x4fefefef81a24402 0x04fefefef81a2440 0x7fffffff87e3c60f 0xf7fffffff87e3c60

def z1166 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8fff70007ffc000c 0xf8fff70007ffc000

def z1167 : W := mkw 0x4fefefef81220000 0x04fefefef8122000 0x7fffffff87e3073f 0xf7fffffff87e3073

def z1168 : W := mkw 0x061b1b1c5c5dbb95 0xa061b1b1c5c5dbb9 0x8e030300781c3800 0x48e030300781c380

def z1169 : W := mkw 0x4fefefef90500000 0x04fefefef9050000 0xfffffffff87cc1cf 0xffffffffff87cc1c

def z1170 : W := mkw 0x3ffeded07ffbf60f 0x03ffeded07ffbf60 0xffcc0c007ffffe0c 0x2ffcc0c007ffffe0

def z1171 : W := mkw 0x4feeeee781a24462 0x44feeeee781a2446 0x4ffcfcf787e3c6f8 0xa4ffcfcf787e3c6f

def z1172 : W := mkw 0x6fefefefb3f2446a 0x46fefefefb3f2446 0x7fffffffbfe3c7ff 0xf7fffffffbfe3c7f

def z1173 : W := mkw 0x0b612fe880000000 0x00b612fe88000000 0x4ff37ff000000002 0xf4ff37ff00000000

def z1174 : W := mkw 0x4fefefef8800a084 0x04fefefef8800a08 0x4fffffff8000c0c3 0xf4fffffff8000c0c

def z1175 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffff7f80000001 0x64fffff7f8000000

def z1176 : W := mkw 0x4f2b6b6c80040900 0x84f2b6b6c8004090 0x8e337370401c3800 0x48e337370401c380

def z1177 : W := mkw 0x0fafeb2c80000000 0x00fafeb2c8000000 0x4fffffff80000003 0xf4fffffff8000000

def z1178 : W := mkw 0x060a0a041854a984 0x8060a0a041854a98 0xfe0f0c06787cf9cd 0x7fe0f0c06787cf9c

def z1179 : W := mkw 0x4b216b6c80000000 0x04b216b6c8000000 0x0030737000000000 0x0003073700000000

def z1180 : W := mkw 0x5fefefefa2804402 0x05fefefefa280440 0x4fffffff83800003 0xf4fffffff8380000

def z1181 : W := mkw 0x4defe5ef90540980 0x84defe5ef9054098 0x21fff0ff807c01c1 0x821fff0ff807c01c

def z1182 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x4fff7f7603e0c0c8 0x64fff7f7603e0c0c

def z1183 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00f707f80fe0c 0x6dff00f707f80fe0

def z1184 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x0ffff3f180000001 0xf0ffff3f18000000

def z1185 : W := mkw 0x0970049066805603 0x0097004906680560 0xdff00ff07f80fe0e 0xfdff00ff07f80fe0

def z1186 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0xcfffffffc01c3803 0xfcfffffffc01c380

def z1187 : W := mkw 0x4be5efef80000000 0x04be5efef8000000 0x41fcffff80000003 0xb41fcffff8000000

def z1188 : W := mkw 0x1b700ed06e00b205 0x01b700ed06e00b20 0xcff00ff07f80380e 0xfcff00ff07f80380

def z1189 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x5fffffff8783c63f 0xf5fffffff8783c63

def z1190 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xcff00f707f80f80c 0xfcff00f707f80f80

def z1191 : W := mkw 0x061b1b1c5c5dbb95 0xa061b1b1c5c5dbb9 0xbe0303007c1f3f34 0x4be0303007c1f3f3

def z1192 : W := mkw 0x4b206a6080000000 0x04b206a608000000 0x0e30737000000000 0x40e3073700000000

def z1193 : W := mkw 0x1b600ed02a80f607 0x01b600ed02a80f60 0x5fc00ff03f80fe0e 0xb5fc00ff03f80fe0

def z1194 : W := mkw 0x2f3b7b3cfe5dbb9d 0xa2f3b7b3cfe5dbb9 0x8e337370781c3800 0x48e337370781c380

def z1195 : W := mkw 0x2daed000337b0008 0x02daed000337b000 0xafcff0007bff000d 0x7afcff0007bff000

def z1196 : W := mkw 0x42012b6c80000000 0x042012b6c8000000 0x0033737000000000 0x4003373700000000

def z1197 : W := mkw 0x101010106e0dbb15 0xa101010106e0dbb1 0xb00000007c1f3f34 0x0b00000007c1f3f3

def z1198 : W := mkw 0x4fafeb6c81220000 0x04fafeb6c8122000 0x2ffff37007e3000d 0xf2ffff37007e3000

def z1199 : W := mkw 0x4fefefef89a2e466 0x44fefefef89a2e46 0xffffffffffe3ffff 0xfffffffffffe3fff

def z1200 : W := mkw 0x42c5afef80000000 0x042c5afef8000000 0x41ffffff80000003 0xf41ffffff8000000

def z1201 : W := mkw 0x4be4eee380000000 0x04be4eee38000000 0x0ff0f3f180000000 0xc0ff0f3f18000000

def z1202 : W := mkw 0x0001212880040900 0x8000121288004090 0x2033f3f9801c0103 0xd2033f3f9801c010

def z1203 : W := mkw 0x49e5e5eb80000000 0x049e5e5eb8000000 0x41ffffff80000003 0xf41ffffff8000000

def z1204 : W := mkw 0x0b212b6880000000 0x00b212b688000000 0x0e33f3f980000003 0xd0e33f3f98000000

def z1205 : W := mkw 0x0000000000000000 0x0000000000000000 0x700c8c8f8060c1cf 0xb700c8c8f8060c1c

def z1206 : W := mkw 0x49a4e06380000000 0x049a4e0638000000 0x0030f07180000000 0x00030f0718000000

def z1207 : W := mkw 0x49e5e5eb81a24462 0x449e5e5eb81a2446 0x31f3f3f987830737 0xd31f3f3f98783073

def z1208 : W := mkw 0x49e5e5eb80000000 0x049e5e5eb8000000 0x01f0f3f980000002 0x801f0f3f98000000

def z1209 : W := mkw 0x00101010660d1b11 0xa00101010660d1b1 0xb00000007f9f3f3c 0x0b00000007f9f3f3

def z1210 : W := mkw 0x7fefefefbbf2e40e 0x07fefefefbbf2e40 0x4fffffffbbe0c00b 0xf4fffffffbbe0c00

def z1211 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0x8ff370007b9c0008 0x68ff370007b9c000

def z1212 : W := mkw 0x0b600ec000000000 0x00b600ec00000000 0x4ff3fff000000003 0xf4ff3fff00000000

def z1213 : W := mkw 0x49e4e4e380804402 0x049e4e4e38080440 0x01f0f0f187800600 0x801f0f0f18780060

def z1214 : W := mkw 0x20101010777f1b19 0xa20101010777f1b1 0xa00000007fff380c 0x0a00000007fff380

def z1215 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xde0f0f06787cf8ce 0x7de0f0f06787cf8c

def z1216 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff3f07fff000f 0xfaffff3f07fff000

def z1217 : W := mkw 0x0defe5ab80000000 0x00defe5ab8000000 0x4fffffff80000003 0xf4fffffff8000000

def z1218 : W := mkw 0x0001212880040900 0x8000121288004090 0x80337370401c3800 0x480337370401c380

def z1219 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000300441f3f36 0x5b0000300441f3f3

def z1220 : W := mkw 0x096125e880000000 0x0096125e88000000 0x01f3f3f980000003 0xd01f3f3f98000000

def z1221 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0x7fffffff807cf9c3 0xf7fffffff807cf9c

def z1222 : W := mkw 0x448fe12f917609e0 0xc448fe12f917609e 0x200ff00f807f01f1 0x0200ff00f807f01f

def z1223 : W := mkw 0x1b700ed36e80f667 0x41b700ed36e80f66 0xdff00ff1ff80fe3e 0xfdff00ff1ff80fe3

def z1224 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x7fffffff8463c7ff 0xf7fffffff8463c7f

def z1225 : W := mkw 0x468feb2f80000000 0x0468feb2f8000000 0x4e3fffff80000003 0xf4e3fffff8000000

def z1226 : W := mkw 0x49e4e4e380804462 0x449e4e4e38080446 0x01f0f0f180000630 0x801f0f0f18000063

def z1227 : W := mkw 0x1b600ec02a80e406 0x01b600ec02a80e40 0xdff00ff07b80f80e 0xfdff00ff07b80f80

def z1228 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x4e337f7e00000002 0x44e337f7e0000000

def z1229 : W := mkw 0x02012b288800a004 0x002012b288800a00 0xde33fff9f800f80f 0xfde33fff9f800f80

def z1230 : W := mkw 0x448fe12f80000000 0x0448fe12f8000000 0x003ff37f80000001 0x4003ff37f8000000

def z1231 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e3373f000000002 0xd0e3373f00000000

def z1232 : W := mkw 0x52412fff8884ff17 0xa52412fff8884ff1 0x50000fff8000ff32 0x050000fff8000ff3

def z1233 : W := mkw 0x20949010777f1b19 0xa20949010777f1b1 0xb1cc8089ffff3f3f 0xbb1cc8089ffff3f3

def z1234 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xee0f0f06787cf8cd 0x7ee0f0f06787cf8c

def z1235 : W := mkw 0x4feeeee781a24462 0x44feeeee781a2446 0x7ffcfcff87e3c7ff 0xb7ffcfcff87e3c7f

def z1236 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x7fffffff8063c7f3 0xf7fffffff8063c7f

def z1237 : W := mkw 0x4fefefef80804402 0x04fefefef8080440 0x4fffffff8380c00b 0xf4fffffff8380c00

def z1238 : W := mkw 0x001010105c5dbb95 0xa001010105c5dbb9 0x80000000781c3800 0x080000000781c380

def z1239 : W := mkw 0x20d4949377ff5f7b 0xe20d4949377ff5f7 0xf1cc8c8fffffffff 0xbf1cc8c8ffffffff

def z1240 : W := mkw 0x02412fbf8884fff7 0xe02412fbf8884fff 0x50000fff8000fff2 0x050000fff8000fff

def z1241 : W := mkw 0x49a4e06080000000 0x049a4e0608000000 0x01f0f07000000000 0x801f0f0700000000

def z1242 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfffc8fffffe3ffff 0xffffc8fffffe3fff

def z1243 : W := mkw 0x060b2b2c9854a984 0x8060b2b2c9854a98 0x8e33f3f9f81c3803 0xd8e33f3f9f81c380

def z1244 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xcff00ff07f803e02 0xfcff00ff07f803e0

def z1245 : W := mkw 0x4deee4e381a24462 0x44deee4e381a2446 0x7ffffcff87e3c7ff 0xf7ffffcff87e3c7f

def z1246 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xffff7f7e787cf9cf 0x7ffff7f7e787cf9c

def z1247 : W := mkw 0x001010105c5dbb95 0xa001010105c5dbb9 0xb00000007c1f3f34 0x0b00000007c1f3f3

def z1248 : W := mkw 0x1b701ed06e89f607 0x01b701ed06e89f60 0xfff3fff9ff9fff3f 0xffff3fff9ff9fff3

def z1249 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xa033f3f9c41f3f31 0xca033f3f9c41f3f3

def z1250 : W := mkw 0x6dbed007777b0008 0x06dbed007777b000 0xaffff0067fff000d 0xfaffff0067fff000

def z1251 : W := mkw 0x49e4e4e381220000 0x049e4e4e38122000 0x01f0f0f187830000 0x801f0f0f18783000

def z1252 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x5fffffff80000733 0xf5fffffff8000073

def z1253 : W := mkw 0x00103030c4091211 0x200103030c409121 0xb033f3f1c41f3e37 0xdb033f3f1c41f3e3

def z1254 : W := mkw 0x0b602ee080000000 0x00b602ee08000000 0x4ff0fff180000002 0xf4ff0fff18000000

def z1255 : W := mkw 0x4fefefef9850a084 0x04fefefef9850a08 0xdffffffff860f8cf 0xfdffffffff860f8c

def z1256 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x80000000441f3e30 0x080000000441f3e3

def z1257 : W := mkw 0x1b701ed06e8dff17 0xa1b701ed06e8dff1 0xffc00c007f9fff3c 0x2ffc00c007f9fff3

def z1258 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x90000000401c3f30 0x090000000401c3f3

def z1259 : W := mkw 0x1b612fe8aa80e406 0x01b612fe8aa80e40 0x4ff3fff9bb80c00b 0xf4ff3fff9bb80c00

def z1260 : W := mkw 0x0dafe12881220000 0x00dafe1288122000 0x3ffff3f987e3073f 0xf3ffff3f987e3073

def z1261 : W := mkw 0x001010105c5dbb95 0xa001010105c5dbb9 0xf00c8c8ffc7fffff 0xbf00c8c8ffc7ffff

def z1262 : W := mkw 0x001010104c0dbb15 0xa001010104c0dbb1 0xb00000007c1fff3c 0x0b00000007c1fff3

def z1263 : W := mkw 0x0040048000804402 0x0004004800080440 0x71cc8c8f87e3c7ff 0xb71cc8c8f87e3c7f

def z1264 : W := mkw 0x49e4e4e381220060 0x449e4e4e38122006 0x01f0f0f180030030 0x801f0f0f18003003

def z1265 : W := mkw 0x3010101077fb560b 0x03010101077fb560 0xa00000007fff060c 0x0a00000007fff060

def z1266 : W := mkw 0x2dbed003777b0068 0x42dbed003777b006 0xfffffc0fffffc1ff 0xffffffc0fffffc1f

def z1267 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0x6fffffff801c0103 0xf6fffffff801c010

def z1268 : W := mkw 0x0f2a4a4000000000 0x00f2a4a400000000 0x0e33737000000000 0x40e3373700000000

def z1269 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x5ff00ff03f80fe0a 0xa5ff00ff03f80fe0

def z1270 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaff3f0007f9f0005 0xdaff3f0007f9f000

def z1271 : W := mkw 0x4f2b6b6c90500000 0x04f2b6b6c9050000 0xae3f7370787c000d 0x7ae3f7370787c000

def z1272 : W := mkw 0x1b300a506e00b205 0x01b300a506e00b20 0x8ff003707f803800 0xc8ff003707f80380

def z1273 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33f3f180000000 0xc0e33f3f18000000

def z1274 : W := mkw 0x4fefefef9850a084 0x04fefefef9850a08 0xeffffffff87cc0cf 0xfeffffffff87cc0c

def z1275 : W := mkw 0x496064e380000000 0x0496064e38000000 0x003070f180000000 0x0003070f18000000

def z1276 : W := mkw 0x3010101067ab560b 0x03010101067ab560 0x0000000007830600 0x0000000000783060

def z1277 : W := mkw 0x4f2b6b6c9850a084 0x04f2b6b6c9850a08 0x4e3f7f763860c0c8 0x64e3f7f763860c0c

def z1278 : W := mkw 0x6fefefefbb72a08c 0x06fefefefbb72a08 0x4fffffffbbe0c0cb 0xf4fffffffbbe0c0c

def z1279 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb0000009c41f3f34 0x0b0000009c41f3f3

def z1280 : W := mkw 0x4be5efef80000000 0x04be5efef8000000 0x41f3ffff80000003 0xd41f3ffff8000000

def z1281 : W := mkw 0x29301000777b0008 0x029301000777b000 0xaff3f0007fff000d 0xfaff3f0007fff000

def z1282 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x5fffffff87e0c6cf 0xf5fffffff87e0c6c

def z1283 : W := mkw 0x00101010545d1b11 0xa00101010545d1b1 0xb00000007c7f3f3c 0x0b00000007c7f3f3

def z1284 : W := mkw 0x0921212880000000 0x0092121288000000 0x0ff3f3f980000003 0xf0ff3f3f98000000

def z1285 : W := mkw 0x00c4a4a381a24462 0x400c4a4a381a2446 0x71fcfcff87e3c7ff 0xb71fcfcff87e3c7f

def z1286 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f0e7c7fffff 0x7fe0f0f0e7c7ffff

def z1287 : W := mkw 0x101010106e89f617 0x2101010106e89f61 0x900000007f83fe3c 0x0900000007f83fe3

def z1288 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71fffc8f87e3c7ff 0xf71fffc8f87e3c7f

def z1289 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e3f737000000001 0x70e3f73700000000

def z1290 : W := mkw 0x4f2b6b6c9854a984 0x84f2b6b6c9854a98 0xbe33f3f9f81c3907 0xdbe33f3f9f81c390

def z1291 : W := mkw 0x0001212880000000 0x0000121288000000 0x403fffff80000003 0xf403fffff8000000

def z1292 : W := mkw 0x4085e12b80000000 0x04085e12b8000000 0x0033f3f980000003 0xd0033f3f98000000

def z1293 : W := mkw 0x00d5959b45af5f73 0xe00d5959b45af5f7 0xf1cf8f8fc7ffffff 0xff1cf8f8fc7fffff

def z1294 : W := mkw 0x4f6b6fec9854a984 0x84f6b6fec9854a98 0xdff37ff0781cf80e 0xfdff37ff0781cf80

def z1295 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff0007bff0009 0x6affff0007bff000

def z1296 : W := mkw 0x0010101045ab5673 0x60010101045ab567 0x0000000007830630 0x0000000000783063

def z1297 : W := mkw 0x5fefefefbad4ed86 0x85fefefefbad4ed8 0xfffffffffbfcf9cf 0xffffffffffbfcf9c

def z1298 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x71cc8c0f87e3c7fd 0x271cc8c0f87e3c7f

def z1299 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb03ff3ffc47f3ff7 0xdb03ff3ffc47f3ff

def z1300 : W := mkw 0x06cfafaf99f6ede6 0xc06cfafaf99f6ede 0xffffffffffffffff 0xffffffffffffffff

def z1301 : W := mkw 0x02111b1c4c0dbb95 0xa02111b1c4c0dbb9 0xf0000f0e441ffff6 0x0f0000f0e441ffff

def z1302 : W := mkw 0x4be4eee380000000 0x04be4eee38000000 0x4ffcffff80000003 0xf4ffcffff8000000

def z1303 : W := mkw 0x1b701ed06e89f607 0x01b701ed06e89f60 0xdff0fff07f83fe0e 0xfdff0fff07f83fe0

def z1304 : W := mkw 0x2d3a500076590008 0x02d3a50007659000 0xafff70007ffc000d 0xfafff70007ffc000

def z1305 : W := mkw 0x4defe5ef81a24462 0x44defe5ef81a2446 0x21fff0ff87e307f1 0x821fff0ff87e307f

def z1306 : W := mkw 0x02010b080804a904 0x802010b080804a90 0xfe0f0f0e787cf9cf 0x7fe0f0f0e787cf9c

def z1307 : W := mkw 0x101010107eddff97 0xa101010107eddff9 0xb00000007ffffffc 0x0b00000007ffffff

def z1308 : W := mkw 0x4defe5eb80000000 0x04defe5eb8000000 0x0ffff3f980000003 0xf0ffff3f98000000

def z1309 : W := mkw 0x20101010672f1b19 0xa20101010672f1b1 0xb0000000479f3f34 0x0b0000000479f3f3

def z1310 : W := mkw 0x2dbed003777b0068 0x42dbed003777b006 0xaffff0067fff00cd 0xfaffff0067fff00c

def z1311 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x0ffff3ff80000001 0xc0ffff3ff8000000

def z1312 : W := mkw 0x0001212880000000 0x0000121288000000 0x003373f000000002 0xd003373f00000000

def z1313 : W := mkw 0x06cfafaf81a24462 0x406cfafaf81a2446 0x7fffffff87e3c7ff 0xf7fffffff87e3c7f

def z1314 : W := mkw 0x2daed000337b0008 0x02daed000337b000 0x2fcff0003fff000d 0xb2fcff0003fff000

def z1315 : W := mkw 0x496064e080000000 0x0496064e08000000 0x01f070f000000000 0x801f070f00000000

def z1316 : W := mkw 0x2d3a5000777b0008 0x02d3a5000777b000 0xaff370007fff000c 0xfaff370007fff000

def z1317 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x8ff003f07f803e0c 0xf8ff003f07f803e0

def z1318 : W := mkw 0x0085a12b80000000 0x00085a12b8000000 0x003ff3ff80000003 0xd003ff3ff8000000

def z1319 : W := mkw 0x20101010765d1b19 0xa20101010765d1b1 0xb00000007c1f3f34 0x0b00000007c1f3f3

def z1320 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xeffffc067fffc0cd 0xfeffffc067fffc0c

def z1321 : W := mkw 0x0000202080000000 0x0000020208000000 0x0033f0f180000001 0xd0033f0f18000000

def z1322 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f3f984030633 0xd0033f3f98403063

def z1323 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x6fffffff83e3c1fb 0xf6fffffff83e3c1f

def z1324 : W := mkw 0x4be5efef80000000 0x04be5efef8000000 0x4ff0ffff80000002 0xf4ff0ffff8000000

def z1325 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0030308401c3907 0x5b0030308401c390

def z1326 : W := mkw 0x00113138e60d1b11 0xa00113138e60d1b1 0xb033f3f9ff9f3f3f 0xdb033f3f9ff9f3f3

def z1327 : W := mkw 0x001010105dfffff7 0xe001010105dfffff 0xb00000007ffffffc 0x0b00000007ffffff

def z1328 : W := mkw 0x468feb2f9854a984 0x8468feb2f9854a98 0xfe3ffffff87cf9cf 0xffe3ffffff87cf9c

def z1329 : W := mkw 0x0001212880000000 0x0000121288000000 0x9033f3f9c0003807 0xd9033f3f9c000380

def z1330 : W := mkw 0x041b111c545d1b91 0xa041b111c545d1b9 0xb00f000e447f3ff5 0x0b00f000e447f3ff

def z1331 : W := mkw 0x061b1b1c5c5dbb95 0xa061b1b1c5c5dbb9 0xfe0f8f8ffc7fffff 0xffe0f8f8ffc7ffff

def z1332 : W := mkw 0x4fefefef9850a084 0x04fefefef9850a08 0x7fffffffb860c1cf 0xf7fffffffb860c1c

def z1333 : W := mkw 0x02500e904c80f607 0x002500e904c80f60 0xdff00ff07f80fe0e 0xfdff00ff07f80fe0

def z1334 : W := mkw 0x161b1b1c7eddff97 0xa161b1b1c7eddff9 0xfe0f0f0e7fffffff 0x7fe0f0f0e7ffffff

def z1335 : W := mkw 0x4fafeb6f81220060 0x44fafeb6f8122006 0x2e3ff37f806301f1 0x42e3ff37f806301f

def z1336 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00ff9ff80ff3e 0xfdff00ff9ff80ff3

def z1337 : W := mkw 0x4f2b6b6c80040900 0x84f2b6b6c8004090 0xbe337378401c3907 0x5be337378401c390

def z1338 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff00e7fff01cd 0xfaffff00e7fff01c

def z1339 : W := mkw 0x4daee06080000000 0x04daee0608000000 0x0ffff07000000001 0xf0ffff0700000000

def z1340 : W := mkw 0x4fefefef90540900 0x84fefefef9054090 0xfffffffff87c390f 0xffffffffff87c390

def z1341 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xde0f0f0e787cf9ca 0x6de0f0f0e787cf9c

def z1342 : W := mkw 0x4f2b6b6c8804a984 0x84f2b6b6c8804a98 0x5e337f7e0000f9c2 0x45e337f7e0000f9c

def z1343 : W := mkw 0x4defe5ef80000000 0x04defe5ef8000000 0x01fff3ff80000003 0xd01fff3ff8000000

def z1344 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xf03fffffc41f3f37 0xff03fffffc41f3f3

def z1345 : W := mkw 0x4f2b6b6c8804a984 0x84f2b6b6c8804a98 0x0e33737000003800 0x40e3373700000380

def z1346 : W := mkw 0x4deee4e381a24462 0x44deee4e381a2446 0x2ffff0f187e3063d 0xf2ffff0f187e3063

def z1347 : W := mkw 0x4deee4e390500000 0x04deee4e39050000 0xaffff0f1f87c000d 0xfaffff0f1f87c000

def z1348 : W := mkw 0x4fefefec80000000 0x04fefefec8000000 0x4ffffff000000003 0xf4ffffff00000000

def z1349 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0x5fffffff80003903 0xf5fffffff8000390

def z1350 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfff08ff07f83fe0f 0xffff08ff07f83fe0

def z1351 : W := mkw 0x2daed000337b0008 0x02daed000337b000 0x0fcf70003bfc0008 0x20fcf70003bfc000

def z1352 : W := mkw 0x02012b2c8804a984 0x802012b2c8804a98 0x50000fff8000f9c2 0x050000fff8000f9c

def z1353 : W := mkw 0x1b700ed36e80f667 0x41b700ed36e80f66 0xdff00ff67f80fece 0xfdff00ff67f80fec

def z1354 : W := mkw 0x0b700ed066001201 0x00b700ed06600120 0xdff00ff07f803e0e 0xfdff00ff07f803e0

def z1355 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e3373f980000002 0x40e3373f98000000

def z1356 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x01f0f0f184030630 0x801f0f0f18403063

def z1357 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xee0f0f0e787cf9c9 0x6ee0f0f0e787cf9c

def z1358 : W := mkw 0x19f4b4f3e7ab5673 0x619f4b4f3e7ab567 0x01f0f0f187830630 0x801f0f0f18783063

def z1359 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f06787cf9cc 0x6fe0f0f06787cf9c

def z1360 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x4ff37fff80000002 0xf4ff37fff8000000

def z1361 : W := mkw 0x0dbec00076500000 0x00dbec0007650000 0xaffff0007ffc000d 0xfaffff0007ffc000

def z1362 : W := mkw 0x0000202080000000 0x0000020208000000 0x0030707000000000 0x0003070700000000

def z1363 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0xf1cc8f8fc7e3ffff 0xff1cc8f8fc7e3fff

def z1364 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0x51cc8c8f87e3c7fa 0xa51cc8c8f87e3c7f

def z1365 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x0e3f737600000000 0x40e3f73760000000

def z1366 : W := mkw 0x061b1b1c440d1b11 0xa061b1b1c440d1b1 0xfe0f0f0e441f3f37 0x7fe0f0f0e441f3f3

def z1367 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0000080441f3f36 0x9b0000080441f3f3

def z1368 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x4e3fffff80000003 0xf4e3fffff8000000

def z1369 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0x8033f3f9c41f3e33 0xd8033f3f9c41f3e3

def z1370 : W := mkw 0x4f2b6b6c90540980 0x84f2b6b6c9054098 0x0e337370001c0000 0x40e337370001c000

def z1371 : W := mkw 0x301010107fffff8f 0x8301010107fffff8 0xb00000007fffffcc 0x0b00000007fffffc

def z1372 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0x9ff003f07f803e06 0xd9ff003f07f803e0

def z1373 : W := mkw 0x4f6b6fec80804402 0x04f6b6fec8080440 0x5ff37ff00780c60e 0xf5ff37ff00780c60

def z1374 : W := mkw 0x0d3a100076590000 0x00d3a10007659000 0xaffff0007fff000d 0xfaffff0007fff000

def z1375 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x0ff3f3f980000003 0xd0ff3f3f98000000

def z1376 : W := mkw 0x0010101044091201 0x0001010104409120 0xb033f3f9c41f3f37 0xdb033f3f9c41f3f3

def z1377 : W := mkw 0x3dbed050777b1209 0x03dbed050777b120 0xaffff0707fff000d 0xfaffff0707fff000

def z1378 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xeffffffff87c39c3 0xfeffffffff87c39c

def z1379 : W := mkw 0x4fefefef99f2e4e6 0x44fefefef99f2e4e 0x7fffffffbfe3c7ff 0xf7fffffffbfe3c7f

def z1380 : W := mkw 0x0f6b2fec9854a984 0x80f6b2fec9854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z1381 : W := mkw 0x0be5afeb81a24462 0x40be5afeb81a2446 0x7fffffff87e3c7ff 0xf7fffffff87e3c7f

def z1382 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33f37000000001 0xd0e33f3700000000

def z1383 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x5fffffff84000607 0xf5fffffff8400060

def z1384 : W := mkw 0x1f3b3b7cfe5dbb95 0xa1f3b3b7cfe5dbb9 0x8e337370781c3800 0x48e337370781c380

def z1385 : W := mkw 0x49e5e5eb81a24462 0x449e5e5eb81a2446 0x71ffffff87e3c7ff 0xf71ffffff87e3c7f

def z1386 : W := mkw 0x0feecec300000000 0x00feecec30000000 0x4fffffff80000003 0xf4fffffff8000000

def z1387 : W := mkw 0x4fefefef8800a004 0x04fefefef8800a00 0x5fffffff8000f803 0xf5fffffff8000f80

def z1388 : W := mkw 0x00c4848301a24462 0x400c4848301a2446 0xffcc8c8fffe3c7ff 0xfffcc8c8fffe3c7f

def z1389 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e3f737e00000001 0x40e3f737e0000000

def z1390 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x2ffff0003fff0009 0xa2ffff0003fff000

def z1391 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0x8ff3f3f1f81c3800 0xc8ff3f3f1f81c380

def z1392 : W := mkw 0x404024e380000000 0x0404024e38000000 0x0030f0f180000000 0x80030f0f18000000

def z1393 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xaffff089ffff000f 0xfaffff089ffff000

def z1394 : W := mkw 0x49e4e4e381a24462 0x449e4e4e381a2446 0x41fcfcf783e0c0c8 0xa41fcfcf783e0c0c

def z1395 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0xcffffffff800000f 0xfcffffffff800000

def z1396 : W := mkw 0x460b2b6c9854a984 0x8460b2b6c9854a98 0xfe0f0f7e787cf9cf 0x7fe0f0f7e787cf9c

def z1397 : W := mkw 0x040b010810540900 0x8040b01081054090 0xfe0f0f0e787cf9cf 0x7fe0f0f0e787cf9c

def z1398 : W := mkw 0x2dbed010777b1209 0x02dbed010777b120 0xaffff3707fff380d 0xfaffff3707fff380

def z1399 : W := mkw 0x0001212880000000 0x0000121288000000 0xa033f3f9c01c0007 0xda033f3f9c01c000

def z1400 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x31f0f0f984030737 0x931f0f0f98403073

def z1401 : W := mkw 0x4dafe16f80000000 0x04dafe16f8000000 0x003ff07f80000001 0x0003ff07f8000000

def z1402 : W := mkw 0x0010101045af5f73 0xe0010101045af5f7 0xb0000000479f3f34 0x0b0000000479f3f3

def z1403 : W := mkw 0x048fb12f917f09f0 0xe048fb12f917f09f 0x200ff00f807f01f1 0x0200ff00f807f01f

def z1404 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff0007fffc1cd 0xfbffff0007fffc1c

def z1405 : W := mkw 0x4f6b6fef9854a984 0x84f6b6fef9854a98 0xde337ffff81cf9c2 0x4de337ffff81cf9c

def z1406 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ff370007b9c0000 0x48ff370007b9c000

def z1407 : W := mkw 0x4fafeb6c80000000 0x04fafeb6c8000000 0x0fff737000000000 0x60fff73700000000

def z1408 : W := mkw 0x0010101044091211 0x2001010104409121 0x0000808184030630 0x8000080818403063

def z1409 : W := mkw 0x69e4e4e3a3220008 0x069e4e4e3a322000 0x01f0f0f183800000 0x801f0f0f18380000

def z1410 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xeffffc0e7fff000f 0xfeffffc0e7fff000

def z1411 : W := mkw 0x4fefefef8804a984 0x84fefefef8804a98 0xdffffffff800f9cf 0xfdffffffff800f9c

def z1412 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xfffc0ff07fe0fe0f 0xffffc0ff07fe0fe0

def z1413 : W := mkw 0x0001212880000000 0x0000121288000000 0x1033f3f980000733 0xd1033f3f98000073

def z1414 : W := mkw 0x06cfafaf9854a984 0x806cfafaf9854a98 0xfffffffff87cf9cf 0xffffffffff87cf9c

def z1415 : W := mkw 0x2dbed003777b0068 0x42dbed003777b006 0xbffff08fffff07ff 0xfbffff08fffff07f

def z1416 : W := mkw 0x00d49493440d1b11 0xa00d49493440d1b1 0xf1cc8c8fc41f3f37 0xbf1cc8c8fc41f3f3

def z1417 : W := mkw 0x4f6b6fef80000000 0x04f6b6fef8000000 0x4e337f7600000000 0x44e337f760000000

def z1418 : W := mkw 0x5fefefefbad0e486 0x05fefefefbad0e48 0x4fffffffbbe0c0cb 0xf4fffffffbbe0c0c

def z1419 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4e3fffff80000003 0x44e3fffff8000000

def z1420 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xcffffffff87cf8cb 0xfcffffffff87cf8c

def z1421 : W := mkw 0x060a0a001850a004 0x0060a0a001850a00 0xfe0f0f0e787cf9cf 0x7fe0f0f0e787cf9c

def z1422 : W := mkw 0x4feecec700000000 0x04feecec70000000 0x4ffffff600000003 0xf4ffffff60000000

def z1423 : W := mkw 0x4921616880000000 0x0492161688000000 0x0033f3f980000003 0xd0033f3f98000000

def z1424 : W := mkw 0x4fefefef80040900 0x84fefefef8004090 0xffffffffc07cf9cf 0xfffffffffc07cf9c

def z1425 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xfffffc8fffffc7ff 0xffffffc8fffffc7f

def z1426 : W := mkw 0x4b612fef80000000 0x04b612fef8000000 0x4ff3ffff80000003 0xf4ff3ffff8000000

def z1427 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0xeffffffff87c380f 0xfeffffffff87c380

def z1428 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xb033f3f1c41f3f34 0xcb033f3f1c41f3f3

def z1429 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x6fffffff80030133 0xf6fffffff8003013

def z1430 : W := mkw 0x4feeeee79850a084 0x04feeeee79850a08 0x4ffcfcf7b860c0c8 0xa4ffcfcf7b860c0c

def z1431 : W := mkw 0x0001212880040900 0x8000121288004090 0x8033f3f9c01c3803 0xd8033f3f9c01c380

def z1432 : W := mkw 0x060b2b2c80000000 0x0060b2b2c8000000 0x0e33737000000000 0x40e3373700000000

def z1433 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xa0000000401f3930 0x0a0000000401f393

def z1434 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0008081c41f3f34 0x8b0008081c41f3f3

def z1435 : W := mkw 0x0fefefe880000000 0x00fefefe88000000 0x4ffffff980000003 0xf4ffffff98000000

def z1436 : W := mkw 0x00c5a5ab81a24462 0x400c5a5ab81a2446 0x01f3f3f987830633 0xd01f3f3f98783063

def z1437 : W := mkw 0x4fefefef8804a984 0x84fefefef8804a98 0x4fffffff80003803 0xf4fffffff8000380

def z1438 : W := mkw 0x1010101066895613 0x2101010106689561 0x0000000007830630 0x0000000000783063

def z1439 : W := mkw 0x0001212880000000 0x0000121288000000 0x0033f37000000001 0xd0033f3700000000

def z1440 : W := mkw 0x02412fe880000000 0x002412fe88000000 0x4033fff980000003 0xd4033fff98000000

def z1441 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00f707b80f80e 0x7dff00f707b80f80

def z1442 : W := mkw 0x49e4e4e381a24462 0x449e4e4e381a2446 0x31f0f0f187e3c7fc 0x831f0f0f187e3c7f

def z1443 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0030000441f3f35 0x5b0030000441f3f3

def z1444 : W := mkw 0x4be4eee380000000 0x04be4eee38000000 0x4ff0fcf180000000 0xa4ff0fcf18000000

def z1445 : W := mkw 0x10101010668d5f13 0xa10101010668d5f1 0xb0000000479f3f34 0x0b0000000479f3f3

def z1446 : W := mkw 0x5b700ed76e80f607 0x05b700ed76e80f60 0xdff00ff67f80fe0e 0xfdff00ff67f80fe0

def z1447 : W := mkw 0x4feeeee780000000 0x04feeeee78000000 0x4ffc7c7600000000 0x24ffc7c760000000

def z1448 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x0ffff37f80000001 0xf0ffff37f8000000

def z1449 : W := mkw 0x0dbed00066090000 0x00dbed0006609000 0xaffff0007f9f000d 0xfaffff0007f9f000

def z1450 : W := mkw 0x4fefefef917609e0 0xc4fefefef917609e 0x6fffffff807f01f3 0xf6fffffff807f01f

def z1451 : W := mkw 0x241b1118777f1b19 0xa241b1118777f1b1 0xbe0f03087fff3f3f 0x7be0f03087fff3f3

def z1452 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x6fffffff87e3c0cf 0xf6fffffff87e3c0c

def z1453 : W := mkw 0x02101a104c0dbb15 0xa02101a104c0dbb1 0xfe000f007c1fff3e 0x7fe000f007c1fff3

def z1454 : W := mkw 0x0dafe12880000000 0x00dafe1288000000 0x0ffff37000000001 0xf0ffff3700000000

def z1455 : W := mkw 0x09312138e6041b11 0xa09312138e6041b1 0x9ff003f9ff803f3e 0xf9ff003f9ff803f3

def z1456 : W := mkw 0x00113138c40d1b11 0xa00113138c40d1b1 0xf033ffffc41ffff7 0xdf033ffffc41ffff

def z1457 : W := mkw 0x4f6b6fec80000000 0x04f6b6fec8000000 0x4ff37f7000000000 0x64ff37f700000000

def z1458 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00ffe7f80ffce 0xfdff00ffe7f80ffc

def z1459 : W := mkw 0x4f2b6b6c9854a984 0x84f2b6b6c9854a98 0xfe3ffffff87cf9cf 0xffe3ffffff87cf9c

def z1460 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33737800000003 0x50e3373780000000

def z1461 : W := mkw 0x248ff128917f0918 0xa248ff128917f091 0x200ff000007f0001 0x0200ff000007f000

def z1462 : W := mkw 0x4fefefef90500000 0x04fefefef9050000 0x4fffffffb860000b 0xf4fffffffb860000

def z1463 : W := mkw 0x4fefefef81220060 0x44fefefef8122006 0x7fffffff846307f7 0xf7fffffff846307f

def z1464 : W := mkw 0x4fefefef90540980 0x84fefefef9054098 0x4fffffff801c0003 0xf4fffffff801c000

def z1465 : W := mkw 0x101010106fafff77 0xe101010106fafff7 0xb00000007ffffffc 0x0b00000007ffffff

def z1466 : W := mkw 0x4001212f80000000 0x04001212f8000000 0x0033f3ff80000003 0xd0033f3ff8000000

def z1467 : W := mkw 0x4fefefef80000000 0x04fefefef8000000 0x4fffffff8780000f 0xf4fffffff8780000

def z1468 : W := mkw 0x001010104c0dbb95 0xa001010104c0dbb9 0xb0000000441ffff4 0x0b0000000441ffff

def z1469 : W := mkw 0x4fefefef80040910 0xa4fefefef8004091 0x4fffffff80000133 0xf4fffffff8000013

def z1470 : W := mkw 0x0feecec01850a004 0x00feecec01850a00 0xfffffff0787cf80f 0xffffffff0787cf80

def z1471 : W := mkw 0x29b4d000672b0008 0x029b4d000672b000 0x01c0000007830000 0x001c000000783000

def z1472 : W := mkw 0x040b212890500000 0x0040b21289050000 0xae3ff3f9f87c000f 0xfae3ff3f9f87c000

def z1473 : W := mkw 0x4b606ee080000000 0x04b606ee08000000 0x4ff07ff000000002 0xf4ff07ff00000000

def z1474 : W := mkw 0x4fefefef81a64d62 0xc4fefefef81a64d6 0xffffffffc7ffffff 0xfffffffffc7fffff

def z1475 : W := mkw 0x00101010448d5f13 0xa00101010448d5f1 0xb0000000479fff3c 0x0b0000000479fff3

def z1476 : W := mkw 0x4be5efef81a24462 0x44be5efef81a2446 0x71fcffff87e3c7ff 0xb71fcffff87e3c7f

def z1477 : W := mkw 0x4fefefef9850a004 0x04fefefef9850a00 0xfffffffff87cf80f 0xffffffffff87cf80

def z1478 : W := mkw 0x4fafeb6f80000000 0x04fafeb6f8000000 0x0e33f37180000000 0x40e33f3718000000

def z1479 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0x5fffffffb860f9cb 0xf5fffffffb860f9c

def z1480 : W := mkw 0x048fe12880000000 0x0048fe1288000000 0x003ff3f980000003 0xd003ff3f98000000

def z1481 : W := mkw 0x3feecec03bf2e40e 0x03feecec03bf2e40 0x4ffffff03be0c00b 0xf4ffffff03be0c00

def z1482 : W := mkw 0x061a1a145c5dbb95 0xa061a1a145c5dbb9 0xfe0c0c067c7ffffc 0x2fe0c0c067c7ffff

def z1483 : W := mkw 0x0001212880000000 0x0000121288000000 0x003373f980000002 0x4003373f98000000

def z1484 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xfffffc007fffc00f 0xffffffc007fffc00

def z1485 : W := mkw 0x4f2b6b6c8800a004 0x04f2b6b6c8800a00 0xde337f707800f80e 0x7de337f707800f80

def z1486 : W := mkw 0x4be4eee381a24462 0x44be4eee381a2446 0x7ffcffff87e3c7ff 0xf7ffcffff87e3c7f

def z1487 : W := mkw 0x0000202080000000 0x0000020208000000 0x3030f0f984030737 0x93030f0f98403073

def z1488 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x4fffffff83800003 0xf4fffffff8380000

def z1489 : W := mkw 0x42c5afef81a24462 0x442c5afef81a2446 0x71ffffff87e3c7ff 0xf71ffffff87e3c7f

def z1490 : W := mkw 0x4fefefef81a24462 0x44fefefef81a2446 0x0ff3f3f187830630 0xc0ff3f3f18783063

def z1491 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f0f0e787cf9c3 0x4fe0f0f0e787cf9c

def z1492 : W := mkw 0x0084800001220000 0x0008480000122000 0x71cc8c8f87e3c7ff 0xb71cc8c8f87e3c7f

def z1493 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x41f0fcf180000002 0xb41f0fcf18000000

def z1494 : W := mkw 0x096024e080000000 0x0096024e08000000 0x01f0f0f180000000 0x801f0f0f18000000

def z1495 : W := mkw 0x040a000010500000 0x0040a00001050000 0xae3ff000787c000d 0xfae3ff000787c000

def z1496 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0x90000000441c3e04 0x090000000441c3e0

def z1497 : W := mkw 0x00101010452f1b11 0xa00101010452f1b1 0xb000000047ff3f3c 0x0b000000047ff3f3

def z1498 : W := mkw 0x041a1010545d1b11 0xa041a1010545d1b1 0xbe0f00007c7f3f3d 0x7be0f00007c7f3f3

def z1499 : W := mkw 0x00101010545d1b91 0xa00101010545d1b9 0xb0000000447f3ff4 0x0b0000000447f3ff

def z1500 : W := mkw 0x09b49000672b0000 0x009b49000672b000 0xaffff0007fff000d 0xfaffff0007fff000

def z1501 : W := mkw 0x1b700ed06e80f607 0x01b700ed06e80f60 0xdff00ff07f80fe02 0xcdff00ff07f80fe0

def z1502 : W := mkw 0x060b0b0c1854a984 0x8060b0b0c1854a98 0xfe0f8f0e7c7ff9cf 0xffe0f8f0e7c7ff9c

def z1503 : W := mkw 0x0011111845af5f73 0xe0011111845af5f7 0xf00f0f0e47ffffff 0x7f00f0f0e47fffff

def z1504 : W := mkw 0x648ff12f917f0918 0xa648ff12f917f091 0x200ff00f807f0131 0x0200ff00f807f013

def z1505 : W := mkw 0x6fafeb6cb3720008 0x06fafeb6cb372000 0x0fff73703be00008 0x60fff73703be0000

def z1506 : W := mkw 0x4fefefef9854a984 0x84fefefef9854a98 0x6fffffffb87cc1cb 0xf6fffffffb87cc1c

def z1507 : W := mkw 0x0001212880000000 0x0000121288000000 0x2033f3f980030133 0xd2033f3f98003013

def z1508 : W := mkw 0x301010107f7bb20d 0x0301010107f7bb20 0xa00000007fff380c 0x0a00000007fff380

def z1509 : W := mkw 0x00501493448d5f73 0xe00501493448d5f7 0xf0000c8fc41ffff6 0x0f0000c8fc41ffff

def z1510 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0xbffff0087fff010f 0xfbffff0087fff010

def z1511 : W := mkw 0x2dbed000777b0008 0x02dbed000777b000 0x8ffff0007fff0008 0xe8ffff0007fff000

def z1512 : W := mkw 0x6fefefef91720008 0x06fefefef9172000 0x4fffffff80600003 0xf4fffffff8060000

def z1513 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xb0008000441f3f35 0x9b0008000441f3f3

def z1514 : W := mkw 0x0b612fe880804402 0x00b612fe88080440 0x7ff3fff98783c73f 0xf7ff3fff98783c73

def z1515 : W := mkw 0x4f2b6b6c80000000 0x04f2b6b6c8000000 0x0e33f37980000001 0x40e33f3798000000

def z1516 : W := mkw 0x440b612c80000000 0x0440b612c8000000 0x0033737000000000 0x4003373700000000

def z1517 : W := mkw 0x4f6b6fef80804462 0x44f6b6fef8080446 0x5e337fff8000c7f2 0x45e337fff8000c7f

def z1518 : W := mkw 0x00949013452f1b71 0xe00949013452f1b7 0xb00c800fc47f3ff5 0x0b00c800fc47f3ff

def z1519 : W := mkw 0x49e4e4e380000000 0x049e4e4e38000000 0x41fcfcf780000000 0xa41fcfcf78000000

def z1520 : W := mkw 0x00101010440d1b11 0xa00101010440d1b1 0xf00c0c0e447fffff 0x3f00c0c0e447ffff

def z1521 : W := mkw 0x00111118440d1b11 0xa00111118440d1b1 0xb0030300441f3f34 0x4b0030300441f3f3

def z1522 : W := mkw 0x5fefefefaba2e466 0x45fefefefaba2e46 0x4fffffffbbe0c0cb 0xf4fffffffbbe0c0c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z6,z7]),(0,[z0,z1,z2,z8,z3,z4,z7]),(1,[z0,z9,z2,z3,z4,z10]),(0,[z0,z1,z11,z2,z12,z4,z7]),(0,[z0,z13,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z3,z15,z7])],[(1,[z16,z0,z1,z17,z3,z4]),(0,[z0,z1,z2,z3,z18,z4,z7]),(0,[z19,z0,z1,z2,z3,z4,z7]),(1,[z0,z20,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z22,z10]),(0,[z0,z1,z2,z23,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z24,z25])],[(0,[z0,z1,z3,z26,z4,z27,z7]),(0,[z0,z1,z2,z28,z3,z4,z29]),(0,[z0,z1,z2,z30,z3,z4,z22]),(0,[z0,z1,z2,z31,z14,z3,z4])],[(0,[z32,z0,z1,z2,z33,z4,z7]),(1,[z0,z34,z2,z35,z4,z7]),(0,[z0,z1,z2,z3,z4,z36,z7]),(0,[z0,z37,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z38,z7])],[(0,[z0,z1,z2,z3,z4,z39,z10]),(0,[z40,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z24,z29]),(0,[z0,z1,z2,z3,z4,z24,z7])],[(0,[z42,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z43,z4,z7]),(0,[z44,z0,z1,z2,z33,z3,z4]),(0,[z0,z1,z2,z45,z33,z4,z7]),(0,[z0,z1,z2,z3,z4,z10,z46]),(0,[z0,z1,z2,z47,z3,z4,z7])],[(0,[z0,z1,z2,z3,z48,z4,z7]),(0,[z0,z1,z49,z2,z3,z4,z7]),(0,[z50,z0,z1,z2,z3,z4,z7]),(0,[z51,z0,z1,z2,z3,z4,z10]),(0,[z16,z0,z52,z1,z2,z3,z4]),(0,[z0,z52,z1,z2,z3,z4,z53]),(0,[z54,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z55,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z56,z4,z7]),(0,[z0,z1,z2,z3,z57,z4,z7]),(0,[z16,z0,z58,z1,z2,z3,z4]),(0,[z16,z0,z20,z1,z2,z3,z4]),(0,[z0,z1,z2,z59,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z60,z7]),(1,[z61,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z62,z7])]],
   [[(1,[z0,z1,z2,z3,z4,z63]),(0,[z64,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z65,z3,z4,z7]),(0,[z0,z1,z66,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z67]),(0,[z0,z1,z2,z3,z4,z68,z7])],[(0,[z0,z1,z2,z3,z4,z69,z41]),(1,[z0,z1,z2,z70,z3,z4]),(0,[z71,z0,z1,z2,z3,z4,z25])],[(0,[z0,z1,z55,z2,z3,z4,z7]),(0,[z0,z1,z55,z2,z3,z4,z29]),(0,[z72,z0,z1,z2,z3,z4,z7]),(0,[z0,z73,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z74,z35,z4,z7]),(0,[z0,z1,z2,z3,z75,z4,z7]),(0,[z0,z1,z2,z35,z76,z4,z7]),(0,[z77,z0,z1,z2,z3,z4,z25])],[(0,[z78,z0,z1,z55,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z79]),(0,[z32,z0,z1,z2,z76,z4,z7]),(0,[z0,z1,z2,z80,z3,z74,z4]),(0,[z0,z81,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z2,z45,z3,z4]),(0,[z0,z1,z2,z3,z4,z82,z7]),(0,[z83,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z35,z4,z41]),(0,[z0,z58,z1,z2,z3,z4,z84]),(0,[z0,z1,z2,z3,z26,z4,z25]),(0,[z0,z1,z85,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z86,z4,z10]),(0,[z44,z0,z1,z2,z87,z3,z4]),(0,[z71,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z88]),(1,[z0,z1,z2,z14,z3,z89])],[(0,[z0,z1,z2,z3,z69,z22,z7]),(0,[z90,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z70,z3,z4,z7]),(0,[z0,z91,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z45,z76,z4,z7])],[(0,[z0,z1,z92,z2,z3,z4,z7]),(0,[z0,z1,z93,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z94]),(0,[z44,z0,z1,z95,z2,z3,z4]),(0,[z96,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z10,z97]),(0,[z0,z1,z2,z3,z26,z4,z7]),(0,[z0,z1,z2,z3,z26,z4,z29]),(0,[z0,z1,z2,z98,z3,z4,z7])],[(0,[z0,z1,z99,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z100,z4,z7]),(1,[z0,z1,z101,z3,z27,z7])]],
   [[(0,[z0,z1,z102,z2,z3,z4,z7]),(1,[z78,z0,z1,z2,z3,z4]),(0,[z0,z1,z103,z2,z3,z4,z25]),(0,[z0,z1,z104,z2,z3,z4,z7]),(0,[z0,z1,z2,z105,z3,z21,z7]),(0,[z61,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z106,z2,z3,z4,z7])],[(0,[z0,z58,z1,z2,z3,z4,z10]),(0,[z107,z0,z1,z95,z3,z4,z7]),(0,[z0,z1,z95,z2,z3,z4,z41]),(1,[z0,z1,z2,z3,z15,z24])],[(0,[z0,z1,z2,z3,z108,z4,z7]),(0,[z0,z1,z2,z3,z4,z109,z7]),(0,[z0,z1,z110,z2,z3,z4,z7]),(0,[z0,z1,z2,z87,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z111,z7]),(0,[z112,z0,z1,z2,z3,z4,z7]),(0,[z113,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z114]),(0,[z0,z1,z2,z3,z4,z109,z29])],[(0,[z0,z20,z1,z2,z3,z4,z115]),(0,[z0,z1,z2,z3,z21,z27,z7]),(0,[z0,z1,z2,z116,z3,z4,z7]),(0,[z0,z1,z2,z3,z117,z4,z7])],[(0,[z118,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z119,z2,z3,z4]),(0,[z0,z20,z1,z2,z120,z4,z7]),(0,[z0,z1,z2,z3,z4,z121,z7]),(0,[z0,z1,z2,z122,z3,z4,z7])],[(0,[z0,z1,z2,z123,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z124,z7]),(0,[z125,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z126,z4,z7])],[(0,[z127,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z101,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z15,z4,z41]),(1,[z0,z1,z2,z128,z22,z7])],[(0,[z0,z1,z2,z3,z4,z129,z7]),(0,[z0,z130,z1,z2,z3,z4,z7]),(0,[z0,z58,z1,z2,z3,z131,z7]),(0,[z0,z1,z2,z132,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z133]),(0,[z0,z1,z134,z2,z3,z4,z7])]],
   [[(1,[z135,z0,z1,z2,z3,z4]),(0,[z42,z64,z0,z1,z2,z3,z4]),(0,[z0,z1,z136,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z74,z4,z41]),(0,[z0,z1,z2,z3,z4,z137,z7])],[(0,[z0,z1,z2,z3,z4,z138,z7]),(0,[z0,z1,z2,z45,z74,z4,z7]),(0,[z139,z0,z1,z2,z3,z4,z7]),(0,[z0,z140,z1,z2,z3,z4,z7]),(0,[z0,z141,z1,z2,z3,z4,z41])],[(0,[z142,z0,z1,z2,z3,z4,z7]),(0,[z143,z0,z1,z87,z3,z4,z7])],[(0,[z0,z1,z144,z2,z3,z4,z7]),(1,[z0,z1,z11,z12,z4,z7]),(0,[z0,z1,z2,z3,z145,z4,z7])],[(0,[z0,z1,z2,z3,z146,z4,z7]),(1,[z0,z1,z2,z147,z3,z4]),(0,[z44,z0,z130,z1,z2,z3,z4]),(1,[z0,z58,z2,z45,z4,z7]),(0,[z0,z1,z2,z148,z3,z4,z7]),(0,[z0,z1,z2,z149,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z150,z10]),(0,[z0,z1,z151,z2,z3,z4,z152])],[(0,[z153,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z154,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z4,z89]),(0,[z143,z0,z1,z103,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z115]),(0,[z0,z1,z2,z14,z3,z4,z25]),(0,[z0,z1,z2,z30,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z155,z7]),(0,[z44,z156,z0,z1,z2,z3,z4]),(0,[z0,z157,z1,z2,z3,z4,z63]),(0,[z0,z1,z2,z158,z3,z4,z41]),(0,[z0,z1,z2,z3,z159,z4,z7])],[(0,[z0,z1,z2,z3,z160,z4,z7]),(1,[z0,z1,z2,z3,z18,z7]),(1,[z0,z1,z2,z3,z4,z161]),(0,[z0,z58,z2,z45,z3,z4,z7]),(0,[z0,z1,z2,z3,z120,z4,z7]),(0,[z162,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z7,z163]),(0,[z0,z1,z2,z3,z4,z7,z164])]],
   [[(0,[z165,z156,z1,z2,z3,z4,z7]),(0,[z0,z1,z166,z2,z3,z4,z167]),(0,[z0,z1,z2,z168,z3,z4,z7]),(0,[z0,z1,z169,z2,z3,z4,z7]),(0,[z0,z1,z170,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z171]),(0,[z0,z1,z2,z3,z4,z172,z41]),(0,[z0,z20,z1,z2,z3,z4,z173]),(0,[z0,z1,z151,z2,z3,z4,z41]),(0,[z0,z1,z2,z14,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z29,z89]),(0,[z0,z1,z2,z14,z3,z4,z7])],[(0,[z0,z0,z1,z2,z3,z4,z7]),(0,[z0,z174,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z175,z4,z7]),(0,[z0,z174,z1,z2,z3,z4,z29])],[(0,[z162,z0,z1,z2,z3,z4,z7]),(0,[z32,z0,z1,z2,z3,z57,z7]),(0,[z50,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z27,z25]),(0,[z0,z1,z2,z3,z176,z4,z7])],[(0,[z44,z0,z1,z101,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z177]),(1,[z0,z1,z2,z178,z4,z7]),(0,[z143,z0,z1,z2,z3,z18,z7]),(0,[z179,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z180,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z7]),(0,[z181,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z182,z3,z4,z7]),(0,[z0,z20,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z10,z183]),(0,[z0,z1,z2,z3,z4,z7,z184]),(0,[z0,z1,z2,z3,z4,z185,z7]),(0,[z0,z1,z2,z3,z4,z186,z7]),(0,[z187,z0,z1,z2,z3,z4,z7])],[(0,[z16,z0,z1,z2,z33,z3,z4]),(0,[z0,z34,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z25,z89]),(0,[z0,z1,z2,z3,z4,z27,z7]),(0,[z0,z1,z2,z3,z4,z27,z29])],[(1,[z64,z1,z166,z3,z4,z7]),(0,[z188,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z2,z3,z76,z4]),(0,[z0,z1,z119,z2,z3,z4,z7]),(0,[z0,z52,z1,z2,z3,z4,z7]),(0,[z0,z52,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z189,z4,z7]),(1,[z0,z1,z2,z3,z4,z25]),(0,[z0,z9,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z190,z41]),(0,[z0,z1,z2,z3,z4,z191,z22]),(0,[z0,z1,z2,z192,z3,z4,z7]),(0,[z0,z193,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z194,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z7,z195]),(0,[z0,z1,z151,z2,z3,z4,z196]),(0,[z0,z1,z2,z197,z3,z4,z7])]],
   [[(0,[z165,z44,z0,z1,z2,z3,z4]),(0,[z32,z0,z1,z2,z128,z4,z7]),(0,[z0,z1,z2,z3,z4,z84,z7]),(0,[z198,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z199,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z200,z4,z7]),(0,[z201,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z3,z4,z24]),(0,[z0,z1,z2,z202,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z203,z3,z4,z7]),(0,[z0,z1,z166,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z204,z4,z7]),(0,[z0,z205,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z206,z4,z7]),(0,[z77,z16,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z184]),(1,[z0,z1,z2,z3,z4,z29]),(0,[z207,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z208,z7]),(0,[z0,z1,z2,z128,z3,z76,z7]),(0,[z0,z1,z2,z209,z3,z4,z7])],[(0,[z44,z0,z1,z2,z128,z3,z4]),(0,[z143,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z210,z7]),(0,[z0,z1,z2,z211,z3,z4,z7]),(0,[z0,z1,z2,z14,z212,z3,z4])],[(0,[z165,z0,z1,z2,z146,z4,z7]),(0,[z156,z0,z55,z2,z3,z4,z7]),(0,[z0,z213,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z25,z214]),(0,[z198,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z215,z7])],[(0,[z0,z1,z2,z33,z3,z4,z25]),(0,[z16,z0,z1,z2,z87,z3,z4]),(0,[z216,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z217,z3,z4,z7])],[(0,[z0,z218,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z5,z7]),(0,[z219,z0,z1,z2,z220,z4,z7]),(0,[z221,z0,z1,z2,z3,z4,z7]),(0,[z0,z222,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z12,z4,z25]),(0,[z0,z1,z223,z2,z3,z4,z7]),(0,[z0,z1,z224,z2,z3,z4,z225]),(0,[z0,z1,z101,z2,z3,z27,z7])],[(0,[z226,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z95,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z26,z4]),(0,[z227,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z228,z2,z3,z4,z7]),(0,[z0,z1,z2,z128,z105,z4,z7])],[(0,[z0,z1,z2,z229,z4,z69,z7]),(0,[z0,z1,z2,z230,z4,z69,z7]),(0,[z231,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z232,z3,z4,z7]),(0,[z0,z34,z1,z2,z3,z4,z233]),(0,[z0,z1,z2,z234,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z173]),(0,[z0,z1,z235,z2,z3,z4,z7])]],
   [[(0,[z0,z236,z1,z2,z3,z4,z7]),(0,[z0,z237,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z26,z21,z7]),(0,[z0,z1,z2,z31,z3,z4,z10]),(0,[z0,z1,z2,z3,z238,z4,z7]),(0,[z0,z1,z2,z3,z12,z4,z7]),(0,[z0,z1,z2,z3,z12,z4,z29]),(0,[z0,z1,z2,z3,z239,z4,z7])],[(0,[z0,z1,z240,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z241]),(0,[z242,z0,z1,z2,z3,z4,z41]),(0,[z219,z0,z1,z2,z3,z4,z29]),(0,[z143,z243,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z244,z4,z7]),(0,[z0,z1,z2,z245,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z246,z7]),(1,[z0,z1,z2,z3,z4,z247]),(0,[z0,z1,z2,z31,z3,z15,z4])],[(0,[z248,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z105,z3,z4,z41]),(0,[z0,z1,z2,z3,z249,z4,z7])],[(0,[z0,z157,z1,z2,z3,z4,z250]),(0,[z32,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z251,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z25,z183]),(0,[z0,z1,z2,z3,z4,z252,z7]),(0,[z0,z1,z2,z3,z4,z7,z253])],[(0,[z0,z1,z2,z3,z4,z7,z254]),(0,[z16,z0,z1,z2,z3,z255,z4]),(0,[z0,z1,z2,z3,z4,z7,z256]),(0,[z0,z1,z11,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z4,z7,z257]),(0,[z143,z0,z1,z2,z244,z4,z7]),(0,[z0,z1,z2,z3,z258,z4,z7]),(0,[z0,z259,z1,z2,z3,z4,z7])],[(1,[z16,z1,z2,z3,z4,z46]),(0,[z0,z1,z2,z3,z4,z7,z260]),(0,[z0,z1,z2,z158,z35,z4,z7]),(0,[z0,z1,z2,z3,z4,z22,z25]),(0,[z0,z1,z2,z3,z4,z25,z41]),(0,[z0,z1,z2,z261,z3,z4,z7]),(0,[z0,z1,z151,z2,z3,z27,z7]),(0,[z0,z1,z2,z3,z262,z4,z41])]],
   [[(0,[z0,z1,z263,z2,z3,z4,z7]),(0,[z44,z44,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z27]),(0,[z0,z1,z2,z264,z3,z4,z7]),(0,[z0,z1,z11,z2,z3,z4,z7]),(0,[z0,z1,z11,z2,z3,z4,z184]),(0,[z0,z1,z11,z2,z3,z4,z29])],[(0,[z0,z1,z2,z3,z4,z7,z265]),(0,[z135,z156,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z266,z7]),(0,[z0,z1,z267,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z268])],[(0,[z51,z0,z1,z2,z3,z69,z7]),(0,[z269,z44,z0,z1,z2,z3,z4]),(0,[z0,z270,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z256]),(0,[z0,z1,z2,z128,z3,z4,z10]),(0,[z271,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z22,z29]),(0,[z0,z1,z2,z3,z4,z22,z7]),(0,[z0,z1,z2,z212,z3,z4,z183])],[(0,[z0,z1,z2,z272,z3,z4,z41]),(0,[z0,z1,z2,z3,z273,z4,z7]),(0,[z0,z1,z2,z3,z21,z4,z10]),(0,[z0,z1,z224,z2,z3,z4,z10]),(0,[z0,z1,z158,z3,z12,z4,z7]),(0,[z0,z1,z274,z2,z3,z4,z7])],[(0,[z0,z1,z2,z80,z3,z4,z7]),(0,[z51,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z244,z3,z4,z7]),(1,[z0,z1,z2,z3,z275,z7]),(0,[z0,z1,z2,z3,z276,z4,z7]),(0,[z0,z20,z1,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z277,z25]),(0,[z0,z1,z224,z2,z12,z4,z7])],[(0,[z0,z1,z2,z3,z4,z39,z7]),(0,[z0,z1,z2,z212,z3,z4,z41])],[(1,[z0,z1,z2,z3,z4,z265]),(0,[z165,z0,z1,z2,z3,z4,z10]),(0,[z44,z0,z1,z55,z2,z3,z4]),(0,[z16,z156,z0,z1,z2,z3,z4]),(0,[z64,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z278,z2,z3,z4,z7]),(0,[z162,z16,z0,z1,z2,z3,z4]),(0,[z279,z0,z1,z2,z3,z4,z7])],[(0,[z156,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z280,z3,z4,z7]),(0,[z51,z0,z1,z2,z3,z4,z7]),(0,[z51,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z277,z7]),(0,[z0,z1,z2,z3,z4,z281,z7]),(0,[z0,z1,z2,z3,z282,z4,z7]),(0,[z0,z1,z2,z3,z4,z277,z29])]],
   [[(0,[z283,z44,z0,z1,z2,z3,z4]),(0,[z143,z0,z1,z2,z3,z275,z7])],[(0,[z0,z1,z284,z2,z3,z4,z7]),(0,[z44,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z191,z7]),(0,[z0,z1,z2,z3,z285,z4,z7]),(0,[z0,z1,z286,z2,z3,z4,z7])],[(0,[z287,z0,z1,z2,z3,z4,z7]),(0,[z288,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z289,z3,z4,z7]),(0,[z16,z51,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z86,z4,z25]),(0,[z0,z1,z2,z3,z4,z290,z7]),(0,[z0,z1,z291,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z292,z7]),(0,[z16,z0,z1,z101,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z4,z177]),(0,[z0,z293,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z105,z3,z172,z7]),(0,[z294,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z295,z4,z10]),(0,[z0,z1,z2,z296,z3,z4,z7])],[(0,[z297,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z298,z7]),(0,[z0,z1,z2,z33,z4,z22,z7]),(0,[z299,z16,z0,z1,z2,z3,z4]),(0,[z0,z300,z1,z2,z3,z4,z7]),(0,[z301,z0,z1,z2,z3,z4,z7]),(0,[z0,z58,z1,z2,z45,z4,z7]),(0,[z0,z1,z2,z302,z3,z4,z7])],[(0,[z0,z1,z2,z105,z33,z4,z7]),(0,[z0,z1,z2,z3,z86,z4,z7]),(0,[z0,z1,z2,z3,z86,z4,z29]),(1,[z16,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z31,z3,z4]),(0,[z0,z1,z2,z128,z4,z22,z7])],[(0,[z0,z1,z166,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z303,z4,z7]),(0,[z16,z0,z1,z2,z3,z76,z4]),(0,[z0,z1,z2,z3,z4,z29,z177])],[(1,[z0,z1,z2,z3,z4,z304]),(1,[z0,z1,z2,z3,z4,z305]),(0,[z0,z1,z2,z3,z4,z306,z7]),(0,[z0,z1,z2,z307,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z46]),(0,[z0,z1,z2,z3,z4,z7,z53]),(0,[z0,z58,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z15,z4,z89])]],
   [[(0,[z0,z1,z2,z3,z4,z69,z10]),(0,[z44,z0,z1,z2,z158,z3,z4]),(0,[z0,z1,z2,z87,z3,z4,z25]),(0,[z0,z1,z308,z2,z3,z4,z7]),(0,[z0,z1,z2,z309,z3,z4,z7]),(0,[z0,z1,z151,z3,z26,z4,z7]),(0,[z0,z1,z2,z3,z4,z38,z41]),(0,[z0,z1,z2,z3,z4,z310,z7])],[(0,[z0,z157,z1,z2,z3,z4,z10]),(0,[z248,z0,z1,z2,z3,z4,z10]),(0,[z143,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z311,z7]),(0,[z0,z1,z312,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z24,z41])],[(1,[z242,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z313,z4,z7]),(0,[z16,z0,z1,z2,z128,z3,z4]),(0,[z0,z58,z1,z2,z3,z4,z7]),(0,[z0,z58,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z10,z314]),(0,[z42,z0,z1,z2,z3,z4,z41])],[(0,[z0,z1,z2,z3,z4,z25,z177]),(0,[z0,z1,z2,z3,z315,z4,z7]),(0,[z0,z1,z2,z87,z3,z4,z7]),(0,[z0,z1,z2,z87,z3,z4,z29]),(0,[z0,z1,z2,z316,z3,z4,z7]),(0,[z0,z34,z2,z3,z35,z4,z7]),(0,[z0,z1,z2,z3,z76,z4,z10]),(0,[z0,z1,z2,z3,z317,z4,z7]),(0,[z318,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z319,z7]),(0,[z0,z1,z2,z3,z4,z7,z320]),(0,[z321,z0,z1,z2,z3,z4,z7])],[(0,[z0,z322,z1,z2,z3,z4,z7]),(0,[z0,z1,z323,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z53]),(1,[z0,z1,z2,z3,z4,z150]),(0,[z0,z1,z2,z31,z212,z4,z7])],[(1,[z0,z1,z324,z3,z4,z7]),(0,[z325,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z224,z2,z3,z4]),(0,[z107,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z326,z7]),(0,[z0,z1,z2,z3,z327,z4,z7]),(0,[z328,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z68,z41]),(0,[z0,z1,z2,z105,z76,z4,z7])],[(0,[z329,z0,z1,z2,z3,z4,z7]),(0,[z219,z0,z1,z2,z3,z86,z7]),(0,[z16,z0,z1,z2,z3,z26,z4]),(0,[z44,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z330,z4,z7]),(0,[z0,z1,z2,z331,z3,z4,z7]),(0,[z332,z0,z1,z2,z3,z4,z29]),(0,[z332,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z333])],[(0,[z157,z1,z55,z2,z3,z4,z7]),(0,[z0,z1,z2,z334,z3,z4,z7]),(0,[z0,z1,z55,z2,z3,z4,z41]),(0,[z335,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z336,z4,z7]),(0,[z44,z0,z1,z2,z3,z21,z4]),(0,[z0,z1,z2,z3,z15,z24,z7])]],
   [[(0,[z77,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z157,z1,z2,z3,z4]),(0,[z1,z2,z3,z86,z4,z69,z7]),(0,[z0,z1,z2,z3,z4,z337,z7]),(0,[z44,z0,z1,z2,z3,z15,z4]),(0,[z0,z1,z2,z338,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z97]),(0,[z0,z1,z339,z2,z3,z4,z7]),(0,[z77,z0,z1,z2,z3,z4,z29])],[(0,[z248,z32,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z280,z3,z7]),(0,[z0,z340,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z341,z7]),(0,[z0,z1,z2,z342,z3,z4,z10])],[(0,[z0,z1,z2,z343,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z344]),(0,[z0,z1,z2,z3,z4,z345,z7]),(1,[z16,z44,z1,z2,z3,z4]),(0,[z0,z1,z2,z128,z3,z21,z7]),(0,[z0,z1,z346,z2,z3,z4,z7]),(0,[z0,z1,z2,z31,z3,z4,z190])],[(1,[z40,z0,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z26,z4,z41]),(0,[z0,z1,z2,z14,z3,z4,z89])],[(0,[z78,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z194,z3,z4,z7]),(0,[z0,z1,z2,z3,z347,z4,z7]),(0,[z0,z1,z2,z348,z3,z4,z7]),(0,[z0,z1,z2,z349,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z350]),(0,[z0,z1,z2,z3,z4,z351,z7]),(0,[z0,z352,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z150,z7]),(0,[z0,z1,z101,z3,z4,z27,z7]),(0,[z0,z1,z353,z2,z3,z4,z7])],[(1,[z0,z1,z2,z80,z3,z4]),(0,[z0,z1,z103,z2,z3,z4,z7]),(0,[z0,z1,z103,z2,z3,z4,z29]),(1,[z207,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z354,z7])],[(0,[z0,z1,z2,z3,z74,z4,z10]),(0,[z0,z34,z58,z2,z3,z4,z7]),(0,[z0,z355,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z324,z2,z3,z4,z7]),(0,[z16,z44,z0,z1,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z4,z27]),(0,[z0,z1,z2,z3,z4,z10,z89]),(0,[z0,z356,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z357,z7]),(0,[z0,z1,z2,z116,z3,z4,z41]),(0,[z358,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z359,z3,z4,z7]),(0,[z32,z0,z1,z2,z3,z360,z7]),(0,[z0,z1,z2,z105,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z121,z41])],[(0,[z32,z0,z1,z2,z74,z4,z7]),(1,[z0,z1,z2,z3,z4,z350]),(0,[z44,z0,z1,z2,z3,z4,z69]),(0,[z44,z0,z1,z2,z59,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z361]),(0,[z0,z1,z2,z362,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z363,z7]),(0,[z0,z20,z1,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z364,z4,z7]),(0,[z156,z157,z1,z2,z3,z4,z7]),(0,[z51,z0,z1,z2,z3,z86,z7]),(0,[z0,z34,z1,z2,z3,z4,z25])],[(0,[z64,z0,z1,z166,z3,z4,z7]),(0,[z0,z365,z1,z2,z3,z4,z7]),(0,[z90,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z177,z10]),(0,[z0,z1,z2,z3,z366,z4,z7])],[(1,[z367,z0,z1,z2,z3,z4]),(0,[z32,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z368]),(0,[z0,z1,z2,z3,z4,z369,z7]),(0,[z0,z1,z2,z3,z4,z7,z161]),(0,[z0,z20,z1,z2,z3,z4,z7]),(0,[z0,z20,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z370,z4,z7]),(0,[z0,z1,z2,z3,z4,z10,z371]),(0,[z0,z1,z2,z372,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z7,z214]),(0,[z0,z1,z2,z373,z3,z4,z7]),(0,[z0,z1,z2,z3,z24,z7,z89]),(0,[z374,z0,z1,z2,z3,z4,z7])],[(0,[z16,z0,z1,z55,z2,z3,z4]),(0,[z32,z1,z2,z3,z74,z4,z7]),(0,[z44,z0,z1,z2,z3,z375,z4]),(0,[z0,z1,z2,z3,z376,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z377]),(0,[z0,z1,z2,z3,z4,z7,z378])],[(0,[z379,z0,z1,z2,z3,z4,z7]),(1,[z248,z1,z2,z33,z4,z7]),(0,[z0,z1,z2,z105,z3,z22,z7])]],
   [[(0,[z165,z1,z55,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z380,z4,z7]),(0,[z0,z1,z381,z2,z3,z4,z7]),(0,[z0,z52,z103,z2,z3,z4,z7]),(0,[z0,z1,z2,z372,z3,z4,z7]),(0,[z0,z1,z2,z382,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z7,z383])],[(0,[z384,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z385]),(0,[z16,z0,z9,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z29,z386]),(0,[z0,z1,z2,z3,z4,z387,z7]),(0,[z0,z1,z2,z388,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z389,z7]),(0,[z0,z1,z2,z3,z178,z4,z7]),(0,[z0,z1,z390,z2,z3,z4,z7]),(0,[z0,z1,z391,z2,z3,z4,z7])],[(1,[z32,z1,z2,z74,z4,z7]),(0,[z44,z0,z1,z2,z3,z4,z172]),(0,[z0,z1,z2,z3,z26,z172,z7]),(0,[z107,z0,z1,z2,z3,z4,z10])],[(0,[z1,z166,z2,z272,z3,z4,z7]),(0,[z392,z0,z1,z2,z3,z4,z7]),(0,[z0,z393,z1,z2,z3,z4,z7]),(0,[z16,z32,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z394,z4,z7])],[(0,[z16,z0,z1,z2,z31,z3,z4]),(0,[z0,z1,z2,z3,z4,z395,z7]),(0,[z0,z52,z1,z2,z3,z4,z396]),(1,[z0,z1,z2,z3,z4,z397]),(0,[z0,z1,z2,z3,z4,z398,z7]),(0,[z0,z1,z151,z101,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z383]),(0,[z0,z1,z2,z14,z3,z4,z41])],[(0,[z0,z1,z2,z399,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z385]),(0,[z0,z1,z17,z2,z3,z4,z7]),(0,[z0,z1,z2,z31,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z7,z183])],[(0,[z0,z1,z2,z3,z400,z4,z7]),(1,[z0,z1,z2,z220,z4,z7]),(0,[z0,z1,z2,z3,z4,z401,z7]),(1,[z0,z1,z17,z3,z4,z7]),(0,[z44,z0,z1,z2,z70,z3,z4]),(0,[z0,z1,z2,z3,z4,z402,z7]),(0,[z0,z1,z2,z3,z4,z403,z10]),(0,[z0,z1,z2,z3,z4,z404,z7]),(0,[z0,z1,z2,z405,z3,z4,z7])]],
   [[(0,[z0,z1,z103,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z3,z4,z7]),(0,[z0,z1,z2,z280,z3,z74,z7]),(1,[z219,z1,z2,z3,z69,z7]),(0,[z16,z0,z1,z2,z158,z3,z4]),(1,[z0,z1,z2,z3,z4,z277]),(1,[z0,z1,z2,z3,z4,z396]),(0,[z0,z1,z2,z3,z4,z171,z7]),(0,[z0,z406,z1,z2,z3,z4,z7])],[(0,[z0,z2,z3,z21,z4,z172,z7]),(0,[z0,z1,z2,z3,z4,z7,z41]),(0,[z0,z1,z2,z31,z3,z4,z29]),(0,[z0,z1,z2,z31,z3,z4,z7])],[(0,[z16,z44,z1,z2,z3,z4,z7]),(0,[z44,z0,z34,z1,z2,z3,z4]),(0,[z143,z0,z1,z2,z178,z4,z7]),(0,[z0,z1,z2,z3,z4,z10,z41]),(0,[z0,z1,z407,z2,z3,z4,z7]),(0,[z408,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z27,z41]),(1,[z0,z1,z2,z3,z4,z152]),(0,[z0,z1,z2,z3,z409,z4,z29]),(0,[z0,z1,z2,z3,z409,z4,z7]),(0,[z0,z1,z410,z2,z3,z4,z7])],[(0,[z299,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z46]),(0,[z0,z52,z1,z2,z3,z4,z41]),(1,[z0,z1,z2,z3,z4,z411])],[(0,[z0,z1,z412,z2,z3,z4,z7]),(0,[z0,z1,z2,z413,z3,z4,z7])],[(0,[z64,z1,z55,z2,z3,z4,z7]),(0,[z0,z414,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z224,z2,z3,z4]),(0,[z0,z1,z2,z128,z45,z4,z7])],[(0,[z219,z0,z1,z2,z105,z3,z7]),(0,[z0,z1,z415,z2,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z416,z3,z4,z7]),(0,[z207,z0,z1,z2,z3,z4,z41]),(1,[z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z208,z41]),(0,[z0,z1,z2,z3,z4,z417,z7])],[(0,[z0,z1,z166,z103,z3,z4,z7]),(0,[z0,z1,z2,z3,z21,z69,z7]),(0,[z16,z0,z1,z2,z3,z21,z4]),(0,[z418,z0,z1,z2,z3,z4,z7]),(0,[z0,z20,z1,z2,z3,z172,z7]),(1,[z71,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z419,z7]),(0,[z0,z1,z420,z2,z3,z4,z7])]],
   [[(0,[z16,z0,z157,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z230,z4,z7]),(0,[z0,z1,z2,z3,z421,z4,z69]),(0,[z16,z0,z1,z2,z3,z15,z4]),(0,[z44,z0,z1,z2,z3,z12,z4]),(0,[z40,z44,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z190]),(0,[z143,z0,z1,z2,z3,z4,z7]),(0,[z143,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z128,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z7,z196]),(0,[z0,z1,z2,z422,z3,z4,z7])],[(0,[z0,z423,z1,z2,z3,z4,z7]),(0,[z242,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z21,z4,z25]),(0,[z0,z1,z2,z3,z4,z29,z10]),(0,[z0,z1,z224,z2,z3,z4,z25]),(0,[z0,z1,z424,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z425,z4,z7]),(0,[z0,z1,z2,z33,z3,z4,z7]),(1,[z0,z1,z2,z426,z3,z4]),(0,[z0,z1,z2,z33,z3,z4,z29]),(0,[z44,z0,z1,z119,z2,z3,z4]),(0,[z0,z427,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z247,z7])],[(0,[z0,z1,z428,z2,z3,z4,z7]),(0,[z32,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z35,z12,z4,z7]),(0,[z227,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z128,z3,z4,z29]),(0,[z0,z1,z2,z128,z3,z4,z7])],[(0,[z165,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z429,z7]),(0,[z0,z1,z430,z2,z3,z4,z7]),(1,[z0,z1,z2,z230,z4,z7]),(0,[z431,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z21,z4,z7]),(0,[z0,z1,z2,z3,z21,z4,z29]),(0,[z0,z1,z2,z3,z432,z4,z7]),(0,[z0,z1,z224,z2,z3,z4,z7]),(0,[z0,z1,z224,z2,z3,z4,z29])],[(0,[z0,z1,z2,z433,z3,z4,z7]),(0,[z44,z0,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z394,z4]),(0,[z0,z103,z2,z87,z3,z4,z7]),(0,[z0,z1,z2,z45,z3,z4,z10]),(0,[z0,z1,z2,z3,z12,z4,z41]),(0,[z0,z1,z2,z3,z4,z434,z7]),(1,[z0,z1,z2,z3,z4,z196]),(0,[z0,z1,z2,z3,z4,z434,z29])],[(0,[z0,z435,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z360,z7]),(0,[z0,z1,z2,z3,z4,z436,z7]),(0,[z437,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z438,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z25,z10]),(0,[z0,z1,z2,z3,z4,z25,z439])],[(0,[z165,z0,z1,z2,z3,z4,z7]),(0,[z165,z0,z1,z2,z3,z4,z29]),(0,[z440,z0,z1,z2,z3,z4,z7]),(0,[z219,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z172,z27,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z7,z441]),(1,[z0,z1,z2,z307,z3,z4]),(0,[z0,z1,z2,z442,z3,z4,z7])],[(1,[z0,z1,z2,z3,z138,z7])],[(1,[z0,z1,z443,z3,z4,z7]),(0,[z0,z1,z2,z272,z3,z4,z10]),(0,[z16,z0,z1,z2,z3,z4,z69]),(0,[z0,z444,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z63,z7]),(1,[z445,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z426,z3,z74,z4]),(0,[z216,z0,z1,z2,z3,z4,z7]),(0,[z51,z0,z1,z2,z105,z3,z7]),(0,[z0,z446,z1,z2,z3,z4,z7])],[(0,[z0,z1,z166,z2,z3,z4,z25]),(2,[z0,z1,z307,z3,z4])],[(0,[z0,z1,z447,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z448,z4,z7]),(0,[z0,z1,z11,z2,z3,z4,z41])],[(0,[z156,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z272,z87,z3,z4,z7]),(0,[z0,z1,z2,z74,z4,z22,z7]),(0,[z0,z1,z2,z3,z4,z69,z25]),(0,[z0,z1,z2,z212,z3,z15,z4])],[(0,[z0,z157,z1,z2,z3,z4,z25]),(0,[z0,z1,z166,z2,z3,z4,z7]),(0,[z0,z1,z166,z2,z3,z4,z29]),(0,[z248,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z76,z69,z7]),(0,[z0,z1,z2,z449,z3,z4,z7]),(0,[z450,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z11,z2,z3,z4,z185]),(0,[z0,z1,z2,z3,z4,z22,z41])]],
   [[(0,[z0,z451,z1,z2,z3,z4,z7]),(0,[z452,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z453,z3,z4,z7]),(0,[z0,z1,z2,z3,z76,z4,z25])],[(0,[z0,z157,z1,z2,z3,z4,z7]),(0,[z0,z157,z1,z2,z3,z4,z29]),(0,[z248,z0,z1,z2,z3,z4,z7]),(0,[z248,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z86,z4,z385]),(1,[z16,z0,z1,z307,z3,z4])],[(0,[z454,z0,z1,z2,z3,z4,z7]),(0,[z51,z219,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z172]),(0,[z0,z455,z1,z2,z3,z4,z7]),(0,[z0,z58,z1,z2,z3,z4,z161]),(0,[z0,z1,z2,z456,z3,z4,z7]),(0,[z0,z1,z457,z2,z3,z4,z7])],[(0,[z64,z0,z1,z2,z3,z4,z7]),(0,[z64,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z7,z458]),(0,[z51,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z459,z3,z4,z7]),(0,[z44,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z76,z4,z29]),(0,[z0,z1,z2,z3,z76,z4,z7]),(0,[z0,z460,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z461,z7])],[(0,[z462,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z300,z1,z2,z3,z4]),(0,[z0,z352,z1,z2,z3,z4,z171]),(0,[z0,z1,z2,z128,z3,z172,z7]),(0,[z0,z1,z2,z3,z463,z4,z7])],[(0,[z0,z1,z2,z3,z4,z464,z7]),(1,[z42,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z465,z7]),(0,[z40,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z466,z7]),(0,[z0,z1,z2,z3,z4,z7,z467])],[(0,[z44,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z468,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z469,z7]),(1,[z44,z1,z2,z3,z4,z177]),(0,[z470,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z471,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z472,z7])],[(1,[z0,z1,z2,z3,z473,z7]),(1,[z0,z1,z166,z3,z4,z41]),(0,[z269,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z103,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z474])],[(0,[z0,z1,z2,z3,z475,z4,z7]),(0,[z0,z1,z166,z3,z4,z7,z41]),(0,[z0,z1,z2,z3,z86,z4,z41]),(0,[z16,z0,z34,z1,z2,z3,z4]),(0,[z0,z1,z2,z87,z3,z4,z277]),(0,[z0,z1,z2,z342,z3,z4,z7]),(0,[z0,z1,z476,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z477,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z183])],[(0,[z0,z1,z2,z3,z4,z478,z7]),(1,[z0,z52,z103,z3,z4,z7]),(0,[z0,z352,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z479,z25])],[(0,[z165,z0,z1,z2,z3,z4,z265]),(0,[z156,z1,z2,z272,z3,z4,z7]),(0,[z445,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z480,z7]),(0,[z0,z1,z2,z3,z4,z481,z7]),(1,[z0,z1,z2,z229,z4,z7]),(0,[z44,z0,z1,z2,z3,z86,z4]),(0,[z44,z0,z1,z2,z3,z35,z4]),(0,[z0,z1,z2,z3,z4,z7,z314]),(0,[z61,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z482,z4,z7]),(0,[z445,z0,z1,z2,z3,z4,z29]),(0,[z483,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z484,z7]),(0,[z0,z1,z2,z485,z3,z4,z7]),(0,[z0,z1,z476,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z35,z4,z10]),(0,[z0,z1,z2,z486,z3,z4,z7]),(0,[z0,z487,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z41]),(0,[z0,z1,z2,z3,z4,z7,z488])],[(0,[z0,z1,z2,z489,z3,z4,z7]),(0,[z490,z0,z1,z2,z3,z4,z7]),(0,[z0,z352,z1,z2,z3,z4,z7]),(0,[z0,z352,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z479,z7]),(1,[z0,z1,z2,z491,z4,z7]),(0,[z0,z1,z2,z492,z3,z4,z7])],[(0,[z0,z493,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z399,z3,z74,z7]),(0,[z0,z1,z2,z3,z4,z305,z7]),(0,[z44,z0,z1,z2,z3,z4,z24]),(0,[z0,z58,z1,z2,z3,z4,z41]),(0,[z0,z1,z11,z2,z158,z4,z7]),(0,[z0,z1,z494,z2,z3,z4,z7]),(0,[z0,z1,z101,z2,z3,z26,z7])]],
   [[(0,[z495,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z496,z3,z4,z7]),(0,[z0,z1,z2,z33,z3,z4,z305]),(0,[z16,z0,z1,z2,z3,z4,z465]),(0,[z16,z0,z1,z2,z3,z12,z4]),(0,[z16,z0,z1,z307,z3,z4,z7]),(0,[z0,z1,z2,z497,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z190]),(0,[z0,z352,z2,z3,z4,z172,z7]),(0,[z0,z1,z2,z498,z3,z4,z7]),(0,[z0,z1,z101,z2,z3,z4,z266])],[(0,[z0,z1,z2,z3,z499,z4,z7]),(0,[z242,z0,z1,z2,z3,z4,z79]),(0,[z0,z1,z500,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z314]),(1,[z0,z1,z2,z3,z501,z7]),(0,[z502,z0,z1,z2,z3,z4,z7]),(0,[z503,z0,z1,z2,z3,z4,z7])],[(0,[z219,z1,z2,z3,z4,z69,z7])],[(0,[z165,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z504,z3,z4,z7]),(0,[z0,z1,z95,z2,z3,z4,z10]),(0,[z0,z1,z505,z2,z3,z4,z7]),(0,[z506,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z331,z3,z4,z41])],[(0,[z165,z0,z1,z2,z3,z473,z7]),(0,[z367,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z255,z4,z7]),(0,[z0,z1,z2,z3,z507,z4,z7]),(0,[z0,z1,z95,z3,z4,z7,z41])],[(0,[z165,z0,z1,z2,z3,z4,z304]),(0,[z0,z1,z2,z508,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z509]),(0,[z16,z0,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z177,z7]),(0,[z510,z0,z1,z2,z3,z4,z7]),(0,[z40,z0,z2,z3,z4,z25,z7]),(0,[z0,z1,z511,z2,z3,z4,z7]),(0,[z77,z0,z1,z2,z3,z4,z41])],[(0,[z165,z0,z157,z2,z3,z4,z7]),(0,[z64,z0,z1,z272,z3,z4,z7]),(0,[z0,z1,z512,z2,z3,z4,z7]),(0,[z1,z2,z33,z3,z74,z4,z7]),(0,[z248,z0,z1,z2,z33,z4,z7]),(0,[z1,z2,z3,z4,z177,z7,z46]),(0,[z135,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z513,z7])],[(0,[z514,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z76,z4,z22,z7])]],
   [[(0,[z0,z1,z103,z2,z3,z4,z411]),(0,[z0,z1,z101,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z15,z4,z10]),(0,[z0,z1,z2,z4,z190,z7,z183])],[(0,[z515,z0,z1,z2,z3,z4,z7]),(0,[z44,z0,z1,z2,z3,z74,z4]),(0,[z0,z1,z2,z3,z4,z275,z7]),(0,[z107,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z151,z2,z3,z26,z7])],[(0,[z0,z1,z2,z516,z3,z4,z7]),(0,[z44,z64,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z86,z172,z7]),(0,[z0,z1,z2,z3,z4,z7,z517]),(1,[z0,z1,z2,z105,z76,z7]),(0,[z0,z1,z2,z3,z4,z7,z89])],[(0,[z165,z0,z1,z324,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z304,z7]),(0,[z0,z518,z1,z2,z3,z4,z7]),(0,[z0,z1,z103,z2,z3,z4,z41]),(0,[z0,z34,z1,z2,z45,z4,z7]),(1,[z0,z1,z2,z30,z3,z4])],[(0,[z0,z1,z272,z3,z4,z7,z41]),(0,[z0,z1,z519,z2,z3,z4,z7]),(0,[z520,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z521,z2,z3,z4,z7]),(0,[z107,z0,z1,z2,z3,z4,z7]),(0,[z107,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z522,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z523,z7])],[(0,[z524,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z525,z4,z7]),(0,[z0,z1,z2,z3,z421,z4,z7])],[(0,[z242,z44,z0,z1,z2,z3,z4]),(0,[z526,z0,z1,z2,z3,z4,z7]),(0,[z0,z527,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z528,z3,z4,z10]),(0,[z0,z1,z2,z529,z3,z4,z7]),(0,[z0,z1,z2,z530,z3,z4,z7])],[(0,[z0,z1,z2,z531,z3,z4,z7]),(0,[z0,z1,z532,z2,z3,z4,z7]),(0,[z445,z64,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z57,z7]),(1,[z0,z1,z154,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z371]),(0,[z0,z352,z1,z2,z3,z4,z256]),(0,[z0,z1,z144,z2,z3,z4,z10]),(0,[z533,z0,z1,z2,z3,z4,z7]),(0,[z534,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z219,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z76,z86,z7]),(0,[z0,z1,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z158,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z403,z7])],[(0,[z0,z1,z2,z2,z3,z4,z7]),(0,[z0,z34,z1,z2,z3,z4,z7]),(0,[z0,z34,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z535,z4,z7]),(0,[z0,z1,z536,z2,z3,z4,z7]),(0,[z0,z1,z2,z2,z3,z4,z29])],[(0,[z0,z1,z2,z3,z4,z537,z7]),(0,[z0,z1,z2,z3,z4,z172,z10]),(0,[z0,z20,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z538,z4,z7]),(0,[z0,z1,z151,z2,z3,z4,z10]),(0,[z0,z1,z539,z2,z3,z4,z7]),(0,[z540,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z541,z3,z4,z29]),(0,[z540,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z541,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z542,z7])],[(0,[z0,z1,z2,z3,z4,z7,z543]),(0,[z0,z1,z2,z33,z3,z4,z350]),(0,[z0,z544,z1,z2,z3,z4,z7]),(0,[z545,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z7,z546]),(0,[z0,z1,z2,z547,z3,z4,z7])],[(0,[z44,z0,z1,z2,z272,z3,z4]),(0,[z16,z0,z1,z2,z3,z4,z25]),(0,[z0,z548,z1,z2,z3,z4,z7]),(1,[z540,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z105,z3,z76,z7])],[(0,[z0,z1,z2,z549,z3,z4,z7]),(1,[z0,z1,z2,z399,z3,z7]),(0,[z107,z0,z1,z3,z4,z29,z7]),(0,[z0,z1,z2,z3,z4,z29,z163]),(0,[z550,z0,z1,z2,z3,z4,z7])],[(0,[z551,z0,z1,z2,z3,z4,z7]),(0,[z51,z1,z2,z3,z86,z4,z7]),(0,[z0,z1,z2,z552,z3,z4,z7]),(0,[z0,z1,z2,z382,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z553,z25]),(0,[z0,z1,z2,z3,z554,z4,z7])],[(0,[z242,z0,z1,z2,z3,z4,z25]),(0,[z16,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z29,z25]),(0,[z0,z555,z1,z2,z3,z4,z7])]],
   [[(0,[z165,z0,z55,z2,z3,z4,z7]),(0,[z0,z1,z166,z2,z3,z4,z344]),(1,[z0,z1,z2,z556,z4,z7]),(0,[z445,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z557,z3,z4,z7]),(0,[z0,z9,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z190,z10]),(0,[z0,z1,z2,z3,z4,z558,z7]),(0,[z0,z559,z1,z2,z3,z4,z7])],[(1,[z0,z1,z2,z453,z4,z7]),(0,[z0,z1,z2,z3,z4,z553,z7]),(0,[z32,z0,z1,z2,z3,z4,z25]),(0,[z16,z0,z1,z103,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z10,z10]),(0,[z0,z1,z11,z224,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z560]),(0,[z0,z1,z2,z3,z4,z561,z7]),(0,[z0,z1,z2,z3,z4,z7,z562])],[(0,[z0,z1,z2,z3,z563,z4,z7]),(0,[z44,z0,z1,z2,z3,z4,z46]),(0,[z44,z0,z1,z151,z2,z3,z4]),(0,[z0,z52,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z29,z7]),(0,[z0,z1,z2,z3,z4,z29,z29]),(0,[z0,z1,z2,z3,z4,z404,z29]),(0,[z0,z1,z2,z31,z4,z7,z183])],[(0,[z0,z1,z564,z2,z3,z4,z7]),(0,[z0,z1,z2,z45,z3,z4,z25]),(0,[z0,z1,z2,z31,z3,z4,z183])],[(0,[z32,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z426,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z86,z4]),(0,[z16,z0,z1,z2,z3,z35,z4]),(0,[z44,z0,z1,z2,z105,z3,z4]),(0,[z135,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z25,z25]),(0,[z0,z1,z2,z3,z4,z7,z565]),(0,[z0,z1,z224,z158,z3,z4,z7])],[(0,[z44,z0,z352,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z439]),(0,[z0,z1,z2,z566,z3,z4,z7])],[(0,[z0,z1,z2,z3,z567,z4,z7]),(0,[z568,z0,z1,z2,z3,z4,z7]),(0,[z569,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z45,z3,z4,z7]),(0,[z0,z1,z2,z45,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z173,z7]),(0,[z0,z1,z570,z2,z3,z4,z7]),(0,[z0,z1,z2,z31,z3,z4,z41])],[(0,[z16,z0,z1,z2,z3,z4,z24]),(0,[z44,z0,z1,z2,z3,z4,z22])]],
   [[(1,[z162,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z272,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z571,z7]),(0,[z0,z352,z1,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z41,z314])],[(0,[z0,z1,z2,z572,z3,z4,z7]),(0,[z367,z0,z1,z2,z272,z3,z4]),(0,[z219,z0,z1,z2,z556,z4,z7]),(0,[z0,z1,z2,z3,z4,z25,z472]),(1,[z0,z1,z2,z3,z4,z565]),(0,[z0,z573,z1,z2,z3,z4,z7])],[(0,[z0,z1,z574,z2,z3,z4,z7]),(0,[z0,z1,z575,z2,z3,z4,z7]),(0,[z0,z58,z1,z2,z3,z501,z7]),(0,[z0,z1,z2,z3,z4,z25,z195])],[(0,[z0,z1,z2,z3,z473,z4,z7]),(0,[z0,z1,z576,z2,z3,z4,z7]),(0,[z0,z1,z2,z87,z3,z4,z314]),(0,[z0,z1,z2,z3,z4,z577,z10]),(1,[z0,z1,z2,z3,z4,z185]),(0,[z0,z1,z2,z578,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z247])],[(0,[z156,z0,z1,z2,z3,z4,z25]),(0,[z44,z0,z1,z166,z2,z3,z4]),(0,[z579,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z411,z7]),(0,[z0,z1,z2,z3,z580,z4,z7]),(0,[z0,z1,z2,z212,z4,z190,z7])],[(0,[z143,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z105,z3,z4,z10])],[(0,[z219,z0,z1,z2,z3,z4,z10]),(0,[z42,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z581,z7]),(0,[z0,z1,z2,z3,z4,z7,z582])],[(0,[z156,z0,z1,z2,z3,z4,z7]),(0,[z107,z0,z1,z166,z3,z4,z7]),(0,[z0,z1,z2,z583,z3,z4,z7]),(0,[z16,z248,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z33,z3,z4,z41]),(0,[z584,z0,z1,z2,z3,z4,z7]),(0,[z585,z0,z1,z2,z3,z4,z7]),(1,[z0,z352,z2,z3,z172,z7]),(0,[z0,z1,z2,z3,z4,z10,z586])]],
   [[(0,[z107,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z128,z3,z4,z41]),(0,[z587,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z588,z3,z4,z7])],[(0,[z162,z156,z0,z1,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z74,z4]),(0,[z0,z1,z2,z3,z4,z396,z7]),(0,[z0,z1,z2,z45,z12,z4,z7]),(0,[z0,z1,z2,z3,z21,z4,z41]),(0,[z0,z1,z224,z2,z3,z4,z565]),(0,[z0,z1,z224,z2,z3,z4,z41])],[(0,[z589,z0,z1,z2,z3,z4,z7]),(0,[z16,z64,z0,z1,z2,z3,z4]),(0,[z0,z1,z438,z2,z3,z4,z7]),(1,[z0,z1,z3,z4,z29,z41])],[(0,[z248,z0,z1,z2,z128,z4,z7]),(0,[z0,z1,z2,z590,z3,z4,z7]),(0,[z0,z591,z1,z2,z3,z4,z7])],[(0,[z165,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z147,z3,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z592,z4,z7]),(0,[z0,z593,z1,z2,z3,z4,z7])],[(0,[z0,z1,z154,z2,z3,z4,z7]),(0,[z594,z0,z1,z2,z3,z4,z7])],[(0,[z16,z0,z1,z2,z3,z336,z4]),(0,[z77,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z595,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z41,z89]),(0,[z0,z596,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z375,z4,z7]),(0,[z0,z1,z2,z3,z295,z4,z7]),(0,[z40,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z212,z3,z4,z10]),(0,[z40,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z28,z3,z4,z7]),(0,[z0,z597,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z31,z4,z183])]],
   [[(0,[z0,z598,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z471,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z599,z7])],[(0,[z0,z600,z1,z2,z3,z4,z7]),(0,[z242,z1,z2,z272,z3,z4,z7]),(0,[z0,z20,z1,z2,z491,z4,z7])],[(1,[z0,z1,z272,z3,z4,z41]),(0,[z16,z16,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z11,z2,z3,z4]),(0,[z0,z1,z2,z3,z35,z4,z25]),(0,[z0,z1,z2,z3,z601,z4,z7])],[(0,[z242,z0,z1,z2,z3,z4,z5]),(0,[z16,z0,z1,z2,z272,z3,z4]),(0,[z0,z1,z166,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z69,z7]),(0,[z0,z1,z2,z3,z4,z69,z29]),(0,[z0,z1,z2,z3,z4,z361,z7]),(0,[z0,z1,z2,z3,z602,z4,z7]),(0,[z0,z1,z603,z2,z3,z4,z7]),(0,[z0,z1,z2,z604,z3,z4,z7]),(0,[z0,z1,z2,z604,z3,z4,z29])],[(0,[z242,z0,z1,z166,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z167]),(0,[z0,z1,z605,z2,z3,z4,z7]),(0,[z606,z0,z1,z2,z3,z4,z7]),(0,[z0,z607,z1,z2,z3,z4,z7])],[(0,[z242,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z35,z4,z7]),(0,[z0,z1,z2,z3,z35,z4,z29]),(1,[z0,z2,z3,z4,z25,z10]),(0,[z0,z1,z2,z608,z3,z4,z7])],[(0,[z165,z0,z1,z2,z3,z138,z7]),(0,[z0,z1,z102,z55,z2,z3,z4]),(0,[z0,z157,z1,z2,z3,z4,z41]),(0,[z248,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z11,z3,z12,z4,z7]),(1,[z0,z1,z2,z3,z4,z38]),(0,[z0,z1,z2,z3,z4,z41,z546])]],
   [[(0,[z165,z0,z1,z443,z3,z4,z7]),(0,[z0,z1,z609,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z610]),(0,[z0,z1,z2,z611,z3,z4,z7]),(0,[z0,z1,z2,z3,z612,z4,z7])],[(0,[z64,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z4,z7]),(1,[z0,z1,z2,z194,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z183]),(0,[z613,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z614,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z615,z4,z7]),(0,[z0,z1,z95,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z76,z4,z41])],[(0,[z0,z616,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z167]),(0,[z568,z16,z0,z1,z2,z3,z4]),(0,[z16,z0,z1,z151,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z4,z46]),(0,[z0,z1,z2,z617,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z67]),(0,[z0,z1,z101,z2,z3,z4,z383]),(1,[z0,z1,z2,z3,z4,z191])],[(0,[z0,z1,z2,z3,z4,z24,z10]),(0,[z0,z1,z224,z2,z158,z4,z7])],[(0,[z16,z0,z1,z2,z105,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z618,z4,z7]),(0,[z0,z1,z619,z2,z3,z4,z7]),(0,[z0,z1,z95,z2,z3,z4,z7]),(0,[z0,z1,z95,z2,z3,z4,z29])],[(1,[z0,z1,z2,z3,z4,z79]),(0,[z16,z0,z352,z1,z2,z3,z4]),(0,[z16,z1,z2,z3,z4,z7,z46]),(0,[z0,z1,z2,z3,z4,z29,z46]),(1,[z0,z1,z2,z3,z4,z610]),(0,[z620,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z621,z4,z7]),(0,[z0,z1,z2,z622,z3,z4,z7]),(1,[z107,z0,z1,z3,z4,z29])],[(0,[z0,z1,z623,z2,z3,z4,z7]),(0,[z0,z1,z101,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z624,z4,z25]),(0,[z0,z1,z2,z3,z15,z4,z25])],[(0,[z242,z64,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z22]),(1,[z0,z1,z307,z3,z4,z7]),(0,[z40,z0,z9,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z74,z4,z25]),(0,[z0,z1,z2,z33,z35,z4,z7]),(0,[z0,z52,z1,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z625,z4,z7])],[(0,[z0,z1,z55,z2,z3,z4,z10]),(0,[z143,z0,z1,z2,z3,z4,z610]),(0,[z0,z1,z2,z128,z35,z4,z7]),(0,[z0,z626,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z624,z4,z7]),(0,[z0,z1,z101,z2,z3,z4,z7]),(0,[z0,z1,z101,z2,z3,z4,z29]),(0,[z0,z1,z2,z3,z15,z4,z29]),(0,[z0,z1,z2,z3,z15,z4,z7])],[(0,[z283,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z220,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z25,z46]),(0,[z83,z0,z1,z2,z3,z4,z10]),(0,[z627,z0,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z74,z4,z7]),(0,[z0,z1,z2,z3,z74,z4,z29]),(0,[z248,z1,z2,z33,z3,z4,z7]),(0,[z0,z1,z2,z229,z3,z4,z7]),(0,[z0,z1,z2,z3,z21,z86,z7]),(0,[z0,z1,z2,z87,z3,z4,z41]),(0,[z0,z52,z1,z103,z3,z4,z7]),(0,[z0,z1,z2,z158,z45,z4,z7]),(0,[z0,z352,z1,z2,z3,z4,z41])],[(0,[z16,z0,z1,z166,z2,z3,z4]),(0,[z0,z1,z628,z2,z3,z4,z7]),(0,[z0,z1,z2,z629,z3,z4,z7]),(0,[z44,z0,z1,z2,z212,z3,z4]),(0,[z0,z2,z45,z3,z35,z4,z7]),(0,[z77,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z630,z3,z4,z7]),(0,[z0,z141,z1,z2,z3,z4,z7])],[(0,[z569,z0,z1,z2,z3,z4,z7]),(1,[z0,z1,z102,z2,z3,z4]),(0,[z0,z1,z2,z3,z26,z4,z10]),(0,[z0,z1,z2,z3,z4,z7,z631])],[(0,[z156,z0,z157,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z250]),(1,[z0,z1,z2,z3,z360,z7]),(0,[z632,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z509,z7]),(0,[z0,z1,z2,z3,z633,z4,z7]),(0,[z0,z1,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z158,z3,z4,z25])],[(0,[z1,z55,z2,z272,z3,z4,z7]),(0,[z0,z1,z2,z528,z3,z4,z7]),(0,[z0,z1,z2,z634,z3,z4,z7])]],
   [[(0,[z0,z1,z635,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z636]),(0,[z0,z1,z2,z3,z4,z172,z25]),(0,[z0,z1,z151,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z152,z7])],[(0,[z0,z1,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z147,z272,z3,z4]),(0,[z16,z219,z0,z1,z2,z3,z4]),(0,[z0,z637,z1,z2,z3,z4,z7]),(0,[z0,z20,z352,z2,z3,z4,z7]),(0,[z0,z1,z2,z638,z3,z4,z7]),(0,[z0,z1,z2,z158,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z639,z7]),(0,[z0,z1,z2,z158,z3,z4,z29]),(0,[z0,z1,z2,z3,z640,z4,z7]),(0,[z0,z1,z2,z3,z15,z4,z24])],[(0,[z0,z1,z2,z641,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z642,z7]),(1,[z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z177,z41]),(0,[z0,z1,z2,z643,z3,z4,z7]),(0,[z0,z1,z103,z2,z3,z4,z10]),(0,[z644,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z645,z2,z3,z4,z7])],[(1,[z0,z1,z2,z3,z4,z250]),(0,[z40,z16,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z172,z7]),(0,[z0,z1,z2,z3,z4,z172,z29]),(0,[z0,z1,z2,z646,z3,z4,z7]),(0,[z0,z1,z151,z2,z3,z4,z7]),(0,[z0,z1,z151,z2,z3,z4,z29]),(0,[z0,z1,z3,z4,z29,z7,z41]),(0,[z0,z1,z2,z3,z4,z7,z386])],[(0,[z0,z1,z2,z3,z4,z647,z7]),(0,[z0,z1,z2,z648,z3,z4,z7])],[(1,[z0,z1,z2,z146,z4,z7]),(0,[z0,z1,z2,z649,z3,z4,z7]),(0,[z44,z0,z1,z2,z14,z3,z4]),(0,[z0,z34,z1,z2,z3,z4,z397]),(0,[z0,z1,z2,z3,z650,z4,z7]),(0,[z0,z1,z2,z3,z4,z439,z7])],[(0,[z651,z0,z1,z2,z3,z4,z7]),(0,[z143,z44,z0,z1,z2,z3,z4]),(0,[z0,z9,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z190,z25]),(0,[z0,z1,z2,z652,z3,z4,z7]),(0,[z0,z653,z1,z2,z3,z4,z7])],[(0,[z0,z1,z654,z2,z3,z4,z7]),(0,[z655,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z131,z4,z7]),(1,[z0,z1,z2,z3,z4,z115]),(0,[z656,z0,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z657,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z658,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z659,z7]),(0,[z0,z52,z1,z2,z3,z4,z25]),(1,[z0,z1,z2,z120,z4,z7])],[(0,[z248,z0,z1,z2,z76,z4,z7]),(1,[z637,z1,z2,z3,z4,z7]),(0,[z660,z0,z1,z2,z3,z4,z7]),(0,[z0,z9,z1,z2,z3,z4,z7]),(0,[z0,z9,z1,z2,z3,z4,z29]),(0,[z107,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z190,z29]),(0,[z0,z1,z2,z3,z4,z190,z7]),(0,[z0,z1,z2,z212,z3,z4,z190])],[(0,[z64,z1,z166,z2,z3,z4,z7]),(0,[z143,z0,z52,z2,z3,z4,z7]),(0,[z143,z0,z2,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z661,z25]),(1,[z0,z1,z2,z3,z4,z225])],[(0,[z662,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z11,z2,z3,z4]),(0,[z0,z352,z1,z2,z3,z172,z7]),(1,[z0,z1,z95,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z663,z7])],[(0,[z0,z1,z2,z3,z4,z344,z7]),(0,[z0,z1,z2,z128,z3,z22,z7])],[(1,[z165,z55,z2,z3,z4,z7]),(0,[z135,z0,z1,z2,z3,z4,z7]),(0,[z16,z0,z1,z17,z3,z4,z7]),(0,[z143,z637,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z661,z7])],[(0,[z0,z1,z664,z2,z3,z4,z7]),(0,[z44,z0,z52,z1,z2,z3,z4]),(0,[z0,z34,z1,z2,z3,z4,z41]),(0,[z0,z1,z665,z2,z3,z4,z7]),(0,[z0,z1,z2,z2,z3,z4,z41]),(0,[z0,z666,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z556,z4,z7]),(0,[z44,z0,z58,z1,z2,z3,z4]),(0,[z44,z0,z20,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z369]),(0,[z0,z1,z667,z2,z3,z4,z7]),(0,[z0,z1,z668,z2,z3,z4,z7]),(0,[z0,z1,z2,z14,z3,z4,z10])]],
   [[(0,[z0,z1,z2,z3,z669,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z88]),(0,[z0,z1,z2,z3,z4,z670,z7]),(0,[z0,z671,z1,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z266]),(0,[z0,z1,z2,z3,z4,z672,z7])],[(0,[z16,z0,z1,z2,z3,z4,z183])],[(0,[z64,z156,z1,z2,z3,z4,z7]),(0,[z219,z0,z1,z2,z3,z69,z7]),(1,[z0,z1,z2,z3,z4,z84]),(0,[z0,z1,z2,z3,z4,z673,z7]),(0,[z0,z1,z2,z3,z674,z4,z7])],[(0,[z44,z0,z1,z2,z45,z3,z4]),(1,[z243,z1,z2,z3,z4,z7]),(0,[z143,z0,z1,z2,z3,z4,z369]),(0,[z0,z58,z1,z2,z35,z4,z7]),(0,[z0,z675,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z10]),(0,[z0,z1,z2,z105,z3,z4,z25])],[(0,[z219,z0,z1,z2,z3,z4,z25]),(0,[z219,z0,z1,z2,z128,z3,z7]),(0,[z0,z1,z2,z676,z3,z4,z7]),(0,[z16,z0,z1,z2,z3,z4,z41]),(0,[z677,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z27,z10]),(0,[z0,z1,z2,z3,z4,z577,z7]),(0,[z678,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z183])],[(0,[z242,z0,z1,z2,z3,z4,z7]),(0,[z242,z0,z1,z2,z3,z4,z29]),(0,[z248,z0,z1,z2,z74,z4,z7]),(1,[z0,z1,z2,z3,z421,z4]),(0,[z118,z16,z0,z1,z2,z3,z4]),(0,[z0,z679,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z225,z7])],[(0,[z243,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z397,z7]),(0,[z0,z1,z2,z3,z4,z501,z7]),(0,[z0,z1,z2,z3,z4,z7,z114]),(0,[z0,z1,z2,z105,z3,z4,z29]),(0,[z0,z1,z2,z105,z3,z4,z7])],[(0,[z32,z0,z1,z2,z3,z4,z29]),(0,[z0,z1,z2,z680,z3,z4,z7]),(0,[z0,z1,z2,z681,z3,z4,z7]),(0,[z219,z0,z1,z2,z3,z4,z7]),(0,[z682,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z683,z4,z7]),(0,[z0,z684,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z29,z41])]],
   [[(0,[z685,z0,z1,z2,z3,z4,z7]),(0,[z51,z44,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z10])],[(1,[z156,z157,z2,z3,z4,z7]),(0,[z107,z0,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z69,z172,z7]),(1,[z0,z1,z224,z158,z4,z7]),(0,[z0,z1,z2,z3,z4,z686,z7]),(0,[z0,z1,z2,z687,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z7,z688]),(0,[z0,z1,z2,z14,z3,z7,z89])],[(0,[z0,z1,z2,z443,z3,z4,z7]),(0,[z545,z0,z1,z2,z3,z4,z7]),(1,[z51,z1,z2,z3,z86,z7]),(0,[z0,z1,z2,z491,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z25,z7]),(0,[z0,z1,z2,z3,z262,z4,z7])],[(0,[z0,z689,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z690,z4,z7]),(0,[z0,z1,z2,z45,z3,z4,z41]),(0,[z0,z9,z2,z3,z4,z7,z10])],[(0,[z691,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z86,z4,z509]),(0,[z16,z0,z1,z2,z212,z3,z4]),(0,[z143,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z692,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z233]),(0,[z0,z1,z2,z212,z3,z4,z25]),(1,[z0,z1,z2,z212,z4,z190]),(0,[z0,z1,z2,z693,z3,z4,z7])],[(0,[z0,z1,z2,z272,z3,z4,z7]),(0,[z0,z1,z2,z272,z3,z4,z29]),(0,[z0,z1,z2,z33,z3,z4,z10]),(0,[z16,z0,z1,z2,z307,z3,z4]),(1,[z0,z1,z2,z3,z131,z7]),(0,[z0,z1,z2,z3,z4,z29,z686]),(0,[z694,z0,z1,z2,z3,z4,z7])],[(0,[z165,z0,z1,z2,z453,z4,z7]),(0,[z16,z0,z1,z17,z2,z3,z4]),(0,[z0,z1,z103,z2,z3,z4,z67]),(0,[z0,z1,z2,z3,z12,z4,z10])]],
   [[(0,[z0,z20,z2,z3,z21,z4,z7]),(1,[z0,z1,z151,z3,z26,z7]),(0,[z0,z1,z2,z578,z3,z4,z41]),(0,[z0,z1,z2,z212,z3,z4,z29]),(0,[z0,z1,z695,z2,z3,z4,z7]),(0,[z0,z1,z2,z212,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z7,z586]),(0,[z51,z0,z1,z2,z128,z3,z7]),(0,[z0,z1,z2,z3,z86,z22,z7]),(0,[z696,z0,z1,z2,z3,z4,z7]),(0,[z0,z2,z3,z4,z25,z7,z10])],[(0,[z156,z0,z1,z2,z3,z4,z29]),(0,[z697,z0,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z698,z3,z4,z7]),(0,[z0,z1,z699,z2,z3,z4,z7]),(1,[z0,z1,z2,z3,z4,z233]),(0,[z0,z1,z2,z700,z3,z4,z7])],[(0,[z44,z1,z2,z3,z4,z177,z7])],[],[(0,[z16,z0,z1,z2,z14,z3,z4]),(0,[z44,z0,z1,z2,z3,z4,z89]),(0,[z0,z1,z2,z3,z4,z701,z7]),(0,[z0,z1,z2,z3,z4,z7,z702])],[(1,[z143,z0,z87,z3,z4,z7]),(0,[z0,z703,z1,z2,z3,z4,z7]),(0,[z0,z1,z704,z2,z3,z4,z7]),(0,[z0,z1,z2,z23,z3,z4,z25]),(0,[z0,z705,z1,z2,z3,z4,z7]),(0,[z0,z1,z706,z2,z3,z4,z7])],[(0,[z242,z0,z1,z272,z3,z4,z7]),(0,[z16,z0,z1,z2,z497,z3,z4]),(0,[z662,z16,z0,z1,z2,z3,z4]),(0,[z329,z44,z0,z1,z2,z3,z4]),(0,[z0,z34,z1,z2,z35,z4,z7]),(0,[z0,z1,z11,z2,z3,z4,z10])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z707]),(0,[z0,z1,z272,z3,z4,z38]),(0,[z0,z1,z2,z708,z3,z7]),(0,[z32,z1,z2,z399,z74,z7]),(0,[z107,z0,z1,z307,z3,z4]),(0,[z709,z0,z1,z2,z3,z4]),(0,[z0,z58,z2,z45,z4,z29])],[(0,[z0,z1,z2,z3,z4,z710]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z1,z2,z712,z3,z7]),(0,[z0,z1,z2,z3,z4,z713]),(0,[z44,z0,z1,z2,z3,z714]),(0,[z44,z0,z1,z2,z715,z4]),(0,[z71,z1,z2,z3,z4,z177]),(0,[z0,z1,z2,z3,z4,z716])],[(0,[z0,z1,z2,z3,z4,z250]),(0,[z0,z1,z2,z3,z4,z717]),(0,[z0,z679,z2,z35,z4,z7]),(0,[z0,z1,z3,z4,z718,z7])],[(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z1,z2,z720,z3,z4])],[(0,[z0,z1,z2,z146,z4,z29]),(0,[z0,z1,z721,z3,z4,z7]),(0,[z16,z1,z2,z492,z3,z4]),(0,[z0,z1,z2,z3,z722,z7]),(0,[z723,z1,z2,z3,z4,z314]),(0,[z0,z1,z2,z3,z724,z7])],[(0,[z725,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z726,z3,z4])],[(0,[z0,z1,z3,z4,z109,z41]),(0,[z0,z1,z2,z3,z4,z727]),(0,[z0,z1,z2,z3,z4,z728]),(0,[z0,z1,z2,z105,z76,z41])],[(0,[z156,z1,z443,z3,z4,z7]),(0,[z32,z0,z1,z307,z3,z4]),(0,[z437,z0,z1,z2,z128,z7]),(0,[z0,z1,z2,z120,z4,z29])],[(0,[z243,z1,z2,z3,z18,z7])],[],[(0,[z0,z1,z2,z3,z4,z25]),(0,[z0,z1,z2,z729,z4,z7]),(0,[z61,z156,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z730,z7]),(0,[z269,z0,z1,z2,z59,z4]),(0,[z637,z1,z2,z3,z4,z41]),(0,[z0,z1,z95,z3,z4,z731])],[(0,[z165,z207,z1,z2,z3,z4]),(0,[z0,z1,z732,z2,z3,z4]),(0,[z0,z1,z307,z497,z3,z4]),(0,[z733,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z734]),(0,[z243,z1,z2,z178,z4,z7]),(0,[z0,z1,z2,z244,z18,z7])],[(0,[z44,z1,z2,z3,z4,z68]),(0,[z735,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z736])],[(0,[z165,z55,z2,z3,z4,z41]),(0,[z219,z1,z2,z556,z69,z7]),(0,[z0,z1,z2,z3,z4,z369])],[(0,[z301,z0,z2,z3,z4,z25])]],
   [[(0,[z0,z1,z224,z307,z3,z4]),(0,[z207,z1,z2,z3,z4,z88])],[(0,[z0,z1,z2,z33,z360,z7]),(0,[z0,z1,z2,z178,z4,z10]),(0,[z0,z559,z2,z3,z172,z7])],[(0,[z0,z1,z2,z737,z4,z7]),(0,[z0,z1,z2,z220,z4,z10]),(0,[z44,z0,z352,z2,z3,z172]),(0,[z243,z1,z2,z3,z4,z29]),(0,[z0,z1,z3,z738,z27,z7])],[(0,[z0,z1,z2,z3,z739,z4]),(0,[z51,z1,z2,z3,z86,z385]),(0,[z0,z740,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z131,z161])],[(0,[z0,z1,z2,z556,z4,z41]),(0,[z0,z1,z2,z3,z421,z4]),(0,[z0,z1,z168,z3,z4,z41]),(0,[z0,z1,z2,z741,z4,z7])],[],[(0,[z16,z0,z1,z742,z3,z4]),(0,[z44,z550,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z743])],[(0,[z0,z1,z744,z3,z4,z7]),(0,[z0,z1,z2,z745,z3,z314]),(0,[z0,z1,z2,z3,z4,z746])],[(0,[z16,z0,z1,z2,z280,z3]),(0,[z44,z0,z1,z2,z556,z4]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z1,z224,z158,z4,z29]),(0,[z0,z1,z2,z3,z4,z748])],[(0,[z165,z55,z2,z3,z138,z7]),(0,[z0,z1,z2,z76,z360,z7]),(0,[z51,z1,z2,z3,z86,z7])],[(0,[z165,z55,z443,z3,z4,z7]),(0,[z156,z157,z2,z3,z4,z41]),(0,[z16,z0,z58,z2,z45,z4]),(0,[z0,z1,z749,z2,z3,z4])],[(0,[z16,z156,z157,z2,z3,z4]),(0,[z0,z1,z307,z105,z3,z4]),(0,[z0,z1,z2,z750,z3,z4]),(0,[z445,z0,z1,z17,z3,z4]),(0,[z243,z1,z2,z244,z4,z7]),(0,[z751,z1,z2,z3,z4,z7]),(0,[z143,z0,z87,z3,z18,z7]),(0,[z0,z1,z2,z212,z4,z752])],[(0,[z0,z1,z2,z753,z3,z4])],[(0,[z0,z1,z2,z3,z4,z754]),(0,[z248,z0,z1,z2,z399,z7]),(0,[z755,z0,z1,z2,z3,z4]),(0,[z0,z1,z87,z3,z4,z150]),(0,[z0,z1,z2,z3,z131,z7])],[(0,[z0,z1,z2,z3,z4,z256]),(0,[z0,z1,z2,z3,z4,z756])],[(0,[z0,z1,z2,z757,z3,z4]),(0,[z0,z1,z2,z3,z4,z758]),(0,[z0,z1,z2,z3,z4,z759]),(0,[z0,z1,z2,z230,z4,z10]),(0,[z0,z1,z2,z760,z4,z7]),(0,[z143,z0,z87,z178,z4,z7]),(0,[z0,z2,z3,z21,z761,z7]),(0,[z0,z1,z151,z3,z26,z29])]],
   [[(0,[z1,z2,z33,z762,z4,z7]),(0,[z0,z1,z2,z3,z275,z29]),(0,[z0,z1,z103,z3,z4,z150])],[(0,[z0,z1,z2,z3,z4,z763]),(0,[z0,z119,z2,z3,z4,z10]),(0,[z0,z1,z2,z764,z4,z7]),(0,[z0,z1,z144,z3,z4,z41])],[(0,[z0,z1,z2,z146,z4,z304]),(0,[z242,z44,z1,z272,z3,z4])],[(0,[z0,z1,z2,z765,z4,z7]),(0,[z0,z1,z2,z3,z766,z4]),(0,[z0,z34,z2,z35,z4,z397]),(0,[z0,z352,z2,z3,z172,z41]),(0,[z0,z1,z2,z3,z409,z24])],[(0,[z0,z1,z654,z3,z4,z41]),(0,[z0,z1,z2,z229,z22,z7]),(0,[z0,z103,z767,z3,z4,z7]),(0,[z723,z1,z2,z3,z4,z41])],[(0,[z0,z1,z2,z3,z4,z768]),(0,[z143,z0,z87,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z769])],[(0,[z61,z135,z1,z2,z3,z4]),(0,[z0,z1,z2,z229,z76,z7]),(0,[z0,z1,z2,z3,z4,z770])],[(0,[z0,z1,z2,z771,z3,z360]),(1,[z0,z767,z3,z4,z7]),(0,[z0,z1,z772,z3,z4,z25])],[(0,[z0,z1,z2,z3,z4,z773]),(0,[z227,z0,z2,z3,z4,z38])],[(0,[z16,z0,z1,z2,z3,z4]),(0,[z64,z1,z609,z3,z4,z7]),(0,[z77,z0,z1,z307,z3,z4]),(0,[z0,z1,z101,z307,z3,z4]),(0,[z16,z0,z1,z774,z3,z4]),(0,[z0,z1,z307,z3,z4,z89]),(0,[z0,z1,z2,z244,z275,z7])],[(0,[z0,z1,z2,z3,z4,z775])],[(0,[z16,z637,z1,z2,z3,z4]),(0,[z776,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z777])],[(0,[z0,z1,z264,z3,z4,z41])],[(0,[z0,z1,z576,z3,z4,z41])],[(0,[z61,z0,z1,z2,z3,z4]),(0,[z143,z0,z87,z244,z4,z7])],[(0,[z0,z1,z778,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z779]),(0,[z0,z1,z2,z780,z3,z4]),(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z2,z3,z4,z782]),(0,[z0,z1,z2,z783,z4,z41]),(0,[z0,z1,z2,z128,z419,z7])]],
   [[(0,[z0,z1,z2,z784,z4,z7]),(0,[z143,z16,z0,z87,z3,z4]),(0,[z44,z0,z1,z2,z3,z785]),(0,[z0,z1,z2,z3,z4,z53])],[(0,[z165,z16,z55,z2,z3,z4]),(0,[z0,z1,z2,z786,z3,z4]),(0,[z16,z54,z1,z2,z3,z4]),(0,[z0,z154,z2,z3,z4,z25])],[(0,[z0,z1,z787,z3,z4,z7]),(0,[z0,z1,z312,z3,z27,z7]),(0,[z0,z1,z2,z105,z788,z7])],[(0,[z440,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z3,z4,z790]),(0,[z0,z1,z2,z3,z4,z791]),(0,[z0,z1,z2,z3,z4,z792]),(0,[z0,z1,z2,z3,z785,z41])],[(0,[z793,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z220,z4]),(0,[z16,z0,z1,z151,z3,z26])],[(0,[z44,z0,z1,z443,z3,z4]),(0,[z0,z1,z794,z2,z3,z4])],[(0,[z0,z1,z2,z128,z360,z7]),(0,[z540,z1,z2,z3,z4,z177]),(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z2,z3,z501,z84]),(0,[z0,z446,z2,z3,z21,z7]),(0,[z0,z1,z101,z3,z27,z29])],[(0,[z78,z0,z1,z2,z3,z4]),(0,[z32,z1,z2,z74,z360,z7]),(0,[z0,z1,z2,z3,z4,z797]),(0,[z0,z1,z2,z229,z4,z10]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z0,z1,z2,z3,z4,z799]),(0,[z0,z1,z2,z4,z7,z752])],[(0,[z0,z1,z2,z649,z22,z7]),(0,[z620,z1,z2,z3,z69,z7]),(0,[z0,z0,z1,z307,z3,z4]),(0,[z0,z1,z307,z3,z4,z183]),(0,[z800,z1,z2,z3,z4,z7])],[(0,[z1,z2,z3,z4,z801,z7]),(0,[z0,z1,z3,z4,z41,z562])],[(0,[z16,z32,z1,z2,z74,z4]),(0,[z0,z1,z2,z802,z3,z4]),(0,[z16,z0,z1,z721,z3,z4]),(0,[z0,z1,z2,z803,z4,z7])],[(0,[z0,z1,z307,z3,z4,z41]),(0,[z162,z0,z300,z2,z3,z4]),(0,[z61,z44,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z501,z10]),(0,[z0,z1,z2,z3,z4,z804])],[(0,[z805,z0,z1,z2,z3,z4]),(0,[z16,z1,z2,z3,z4,z472]),(0,[z0,z1,z2,z3,z4,z806]),(0,[z0,z1,z2,z3,z4,z807])],[(0,[z392,z0,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z808]),(0,[z44,z0,z1,z307,z3,z4]),(0,[z16,z0,z809,z2,z3,z4]),(0,[z0,z300,z2,z3,z4,z25]),(0,[z16,z1,z2,z98,z3,z4]),(0,[z810,z1,z2,z3,z4,z7])],[(0,[z44,z0,z1,z2,z3,z138]),(0,[z0,z1,z2,z280,z3,z10]),(0,[z0,z1,z2,z399,z105,z7]),(0,[z811,z0,z1,z2,z3,z4]),(1,[z0,z1,z3,z738,z7])]],
   [[(0,[z0,z1,z2,z812,z3,z4]),(0,[z16,z1,z2,z123,z3,z4]),(0,[z1,z2,z3,z4,z177,z813]),(0,[z0,z1,z2,z178,z18,z7])],[(0,[z0,z1,z70,z87,z3,z4]),(0,[z811,z637,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z814,z7]),(0,[z0,z1,z2,z3,z761,z7]),(0,[z40,z0,z2,z3,z4,z815])],[(0,[z0,z1,z2,z3,z360,z41]),(0,[z0,z1,z2,z3,z4,z816])],[(0,[z165,z102,z55,z2,z3,z4]),(0,[z0,z1,z2,z3,z817,z7]),(0,[z0,z1,z2,z818,z3,z4]),(0,[z0,z1,z2,z3,z336,z24]),(0,[z0,z1,z2,z3,z4,z819])],[(0,[z0,z1,z55,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z1,z2,z821,z4,z7]),(0,[z0,z1,z2,z822,z4,z7]),(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z144,z3,z4,z314]),(0,[z0,z1,z11,z12,z4,z41]),(0,[z0,z1,z2,z28,z4,z163]),(0,[z0,z1,z2,z824,z3,z4])],[(0,[z16,z71,z1,z2,z3,z4]),(0,[z0,z1,z307,z307,z3,z4]),(0,[z0,z1,z2,z471,z3,z89])],[(0,[z0,z1,z2,z3,z4,z825]),(0,[z0,z1,z272,z3,z4,z67]),(0,[z0,z1,z2,z3,z18,z29]),(0,[z0,z1,z2,z3,z4,z161]),(0,[z0,z1,z2,z3,z4,z826])],[(0,[z0,z1,z307,z3,z827,z4]),(0,[z828,z0,z1,z2,z3,z4]),(0,[z0,z1,z646,z3,z4,z29]),(0,[z0,z829,z2,z3,z4,z7])],[(0,[z242,z1,z272,z3,z4,z5]),(0,[z0,z1,z2,z830,z3,z4]),(0,[z0,z1,z2,z3,z831,z7]),(0,[z0,z1,z17,z3,z4,z25]),(0,[z0,z1,z349,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z832])],[(0,[z0,z1,z272,z3,z4,z79]),(0,[z242,z1,z833,z3,z4,z7]),(0,[z219,z1,z2,z3,z69,z25]),(0,[z0,z1,z2,z3,z4,z834]),(0,[z0,z1,z835,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z383])],[(0,[z0,z1,z2,z836,z4,z7]),(0,[z0,z1,z2,z3,z4,z837]),(0,[z0,z1,z2,z3,z4,z385]),(0,[z0,z1,z2,z3,z4,z838]),(0,[z0,z1,z2,z178,z4,z29]),(0,[z0,z20,z2,z491,z21,z7])],[(0,[z0,z1,z2,z220,z4,z29]),(0,[z0,z2,z634,z3,z4,z25]),(0,[z0,z1,z839,z3,z4,z25])],[(0,[z0,z1,z2,z840,z3,z7]),(0,[z0,z1,z307,z14,z3,z4]),(0,[z0,z1,z2,z3,z4,z396])],[(0,[z0,z1,z2,z3,z4,z841]),(0,[z64,z1,z166,z3,z4,z7]),(0,[z0,z1,z2,z4,z842,z7]),(0,[z0,z1,z2,z843,z3,z4])],[(0,[z844,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z742,z3,z4]),(0,[z0,z1,z2,z845,z4,z7]),(0,[z0,z1,z2,z846,z4,z7]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z61,z0,z1,z848,z3,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z7]),(0,[z156,z1,z272,z3,z4,z41]),(0,[z1,z2,z762,z74,z4,z7]),(0,[z0,z1,z2,z399,z3,z10]),(0,[z162,z0,z1,z17,z3,z4]),(0,[z0,z1,z2,z128,z326,z7])],[(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z2,z3,z4,z850]),(0,[z44,z694,z1,z2,z3,z4]),(0,[z0,z851,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z2,z3,z4,z853])],[(0,[z0,z1,z443,z3,z4,z710]),(0,[z165,z0,z154,z2,z3,z4])],[(0,[z71,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z7,z854])],[(0,[z0,z1,z2,z453,z4,z10]),(0,[z0,z1,z2,z3,z4,z855]),(0,[z242,z1,z147,z272,z3,z4]),(0,[z0,z1,z856,z2,z3,z4])],[(0,[z431,z1,z2,z33,z4,z7]),(0,[z857,z0,z1,z2,z3,z4]),(0,[z0,z406,z2,z3,z4,z25])],[(0,[z0,z1,z2,z3,z858,z7]),(0,[z0,z1,z549,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z859]),(0,[z0,z1,z2,z3,z4,z860]),(0,[z0,z861,z1,z2,z3,z4]),(0,[z0,z1,z2,z862,z3,z4])],[(0,[z0,z1,z2,z3,z863,z7]),(0,[z864,z55,z2,z3,z4,z7]),(0,[z0,z1,z865,z2,z3,z4]),(0,[z866,z243,z1,z2,z3,z4]),(0,[z0,z1,z3,z554,z4,z41])],[(0,[z0,z1,z867,z2,z3,z4]),(0,[z0,z1,z2,z868,z4,z7]),(0,[z0,z1,z2,z230,z4,z29]),(0,[z0,z1,z2,z869,z4,z7])],[(0,[z0,z1,z2,z244,z4,z29]),(0,[z0,z1,z2,z3,z4,z247]),(0,[z0,z1,z2,z3,z4,z870]),(0,[z871,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z196]),(0,[z0,z1,z2,z741,z4,z41])],[(0,[z0,z1,z2,z3,z138,z25]),(0,[z248,z0,z1,z307,z3,z4]),(0,[z0,z1,z307,z45,z3,z4]),(0,[z0,z1,z2,z872,z3,z4])],[(0,[z0,z1,z443,z3,z4,z25]),(0,[z118,z0,z1,z2,z3,z336]),(0,[z0,z1,z2,z3,z4,z873]),(0,[z0,z1,z2,z3,z4,z874])],[(0,[z0,z1,z875,z2,z3,z4]),(0,[z16,z0,z1,z2,z876,z4]),(0,[z0,z52,z767,z3,z4,z7])],[(0,[z0,z1,z2,z3,z138,z7]),(0,[z0,z1,z2,z3,z4,z877]),(0,[z878,z0,z1,z2,z3,z4]),(0,[z16,z520,z1,z2,z3,z4]),(0,[z0,z1,z2,z178,z275,z7]),(0,[z0,z1,z224,z158,z4,z565])],[(0,[z0,z1,z2,z3,z4,z879]),(0,[z51,z1,z2,z3,z86,z41]),(0,[z1,z2,z3,z4,z880,z7]),(0,[z0,z1,z2,z3,z4,z881]),(0,[z0,z1,z101,z3,z4,z439])],[(0,[z71,z1,z55,z2,z3,z4]),(0,[z540,z1,z2,z3,z4,z109])]],
   [[(0,[z0,z1,z2,z3,z4,z882]),(0,[z0,z2,z87,z3,z4,z38]),(0,[z0,z52,z2,z3,z4,z38]),(0,[z883,z0,z1,z2,z3,z4]),(0,[z0,z1,z151,z3,z26,z152])],[(0,[z0,z1,z2,z3,z4,z884]),(0,[z42,z0,z1,z166,z3,z4]),(0,[z16,z0,z1,z224,z158,z4]),(0,[z0,z1,z2,z885,z4,z7]),(0,[z0,z1,z2,z3,z886,z7])],[(0,[z887,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z128,z537,z7]),(0,[z0,z1,z2,z3,z131,z41]),(0,[z0,z1,z2,z3,z4,z888])],[(0,[z0,z1,z110,z3,z4,z41]),(0,[z889,z1,z2,z3,z4,z7]),(0,[z723,z1,z2,z3,z4,z10])],[(0,[z0,z1,z2,z128,z556,z7]),(0,[z40,z0,z1,z307,z3,z4]),(0,[z890,z0,z1,z2,z3,z4]),(0,[z143,z0,z87,z3,z4,z277])],[(0,[z0,z1,z2,z3,z4,z891])],[(0,[z16,z0,z1,z307,z3,z4]),(0,[z44,z0,z1,z2,z244,z4]),(0,[z44,z1,z2,z3,z159,z4])],[(0,[z0,z1,z2,z3,z892,z7]),(0,[z0,z1,z2,z3,z4,z893]),(0,[z0,z1,z894,z2,z3,z4])],[(0,[z0,z1,z2,z74,z360,z7]),(0,[z0,z1,z583,z3,z4,z41]),(0,[z16,z0,z1,z778,z3,z4]),(0,[z895,z0,z1,z2,z3,z4]),(0,[z0,z58,z2,z45,z501,z7])],[(0,[z637,z1,z2,z3,z4,z610]),(0,[z0,z9,z2,z3,z4,z247]),(0,[z0,z1,z896,z12,z4,z7])],[(0,[z0,z1,z2,z3,z473,z25]),(0,[z16,z0,z1,z744,z3,z4]),(0,[z0,z1,z897,z2,z3,z4]),(1,[z0,z1,z3,z4,z731])],[(0,[z0,z1,z2,z491,z4,z115])],[(0,[z0,z1,z442,z3,z4,z41])],[(0,[z0,z1,z2,z3,z473,z7]),(0,[z0,z898,z2,z3,z4,z7]),(0,[z125,z1,z2,z3,z86,z7]),(0,[z899,z0,z1,z2,z3,z4]),(0,[z0,z1,z772,z3,z4,z7])],[(0,[z0,z1,z2,z900,z4,z7]),(0,[z0,z1,z2,z3,z4,z305]),(0,[z16,z0,z901,z2,z3,z4]),(0,[z0,z1,z2,z3,z902,z7])],[(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z1,z2,z3,z4,z904]),(0,[z0,z1,z2,z896,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z352,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z906])],[(0,[z0,z1,z324,z3,z4,z25]),(0,[z242,z1,z272,z3,z4,z29]),(0,[z0,z1,z2,z907,z4,z7]),(0,[z16,z540,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z908]),(0,[z0,z1,z2,z3,z4,z909]),(0,[z910,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z911])],[(0,[z71,z156,z1,z2,z3,z4]),(0,[z0,z1,z2,z912,z4,z7]),(0,[z0,z1,z2,z913,z4,z7])],[(0,[z0,z1,z2,z3,z4,z914])],[(0,[z0,z1,z324,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z915]),(0,[z0,z1,z307,z158,z3,z4]),(0,[z0,z1,z2,z3,z4,z916]),(0,[z0,z1,z2,z3,z4,z917]),(0,[z0,z1,z2,z14,z3,z386])],[(0,[z44,z243,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z501,z29]),(0,[z0,z1,z2,z918,z3,z4])],[(1,[z1,z833,z3,z4,z7]),(0,[z64,z1,z166,z3,z4,z344]),(0,[z919,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z745,z3,z10])],[(0,[z0,z1,z920,z3,z4,z7]),(0,[z0,z1,z2,z921,z4,z7]),(0,[z16,z248,z1,z2,z33,z4])],[(0,[z0,z1,z2,z3,z4,z922]),(0,[z0,z1,z2,z280,z3,z29]),(0,[z0,z1,z2,z3,z4,z923]),(0,[z0,z1,z2,z362,z76,z7]),(0,[z924,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z491,z4,z173])],[(0,[z0,z1,z2,z3,z4,z344]),(0,[z0,z925,z2,z3,z4,z7]),(0,[z0,z1,z2,z399,z22,z7]),(0,[z16,z44,z1,z2,z3,z4]),(0,[z16,z0,z1,z926,z3,z4]),(0,[z0,z52,z103,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z927])],[(0,[z0,z1,z2,z3,z4,z928]),(0,[z0,z1,z929,z3,z4,z7]),(0,[z0,z1,z3,z930,z4,z7]),(0,[z0,z1,z2,z931,z3,z4]),(0,[z44,z0,z1,z17,z3,z4])],[(0,[z0,z1,z2,z3,z4,z932]),(0,[z42,z0,z1,z70,z3,z4]),(0,[z0,z1,z2,z35,z131,z7]),(0,[z0,z1,z2,z3,z4,z933]),(0,[z0,z1,z151,z3,z738,z7]),(0,[z0,z1,z2,z3,z4,z752])],[(0,[z0,z1,z2,z3,z4,z934]),(0,[z0,z58,z154,z2,z3,z4]),(0,[z0,z1,z2,z935,z3,z4]),(0,[z0,z1,z2,z741,z4,z314]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z1,z2,z491,z4,z10]),(0,[z332,z0,z2,z3,z4,z277])],[(0,[z165,z55,z2,z146,z4,z7]),(0,[z207,z0,z1,z2,z3,z4]),(0,[z16,z0,z352,z2,z3,z172]),(0,[z44,z0,z1,z2,z937,z4]),(0,[z0,z2,z45,z938,z4,z7]),(0,[z0,z1,z2,z3,z4,z939])],[(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z1,z2,z3,z4,z941])],[(0,[z32,z44,z1,z2,z74,z4])]],
   [[(0,[z0,z1,z2,z3,z57,z25])],[(0,[z0,z1,z2,z3,z4,z942]),(0,[z0,z1,z2,z3,z360,z10])],[(0,[z0,z2,z468,z3,z4,z10]),(0,[z0,z705,z2,z3,z4,z10]),(0,[z0,z1,z492,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z943])],[(0,[z0,z1,z2,z3,z57,z7]),(0,[z0,z1,z2,z3,z944,z7]),(0,[z248,z1,z2,z33,z4,z25]),(0,[z16,z0,z1,z2,z556,z4]),(0,[z0,z1,z2,z459,z76,z7]),(0,[z44,z0,z1,z2,z178,z4]),(0,[z44,z0,z1,z2,z3,z501]),(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z848,z3,z4])],[],[],[(0,[z0,z1,z2,z946,z4,z7]),(0,[z248,z1,z2,z33,z4,z7]),(0,[z44,z0,z1,z2,z3,z360]),(0,[z0,z1,z307,z3,z4,z69]),(0,[z0,z1,z947,z2,z3,z4])],[(0,[z32,z1,z2,z74,z4,z25]),(0,[z0,z1,z2,z3,z4,z948])],[(0,[z540,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z949,z7]),(0,[z0,z1,z2,z3,z4,z950]),(0,[z0,z1,z2,z105,z76,z10])],[(0,[z0,z1,z2,z399,z3,z29]),(0,[z587,z1,z2,z74,z4,z7]),(0,[z0,z1,z2,z3,z4,z951]),(1,[z0,z1,z2,z3,z952])],[(0,[z0,z1,z2,z3,z953,z7]),(0,[z660,z1,z272,z3,z4,z7]),(0,[z32,z1,z2,z74,z4,z7]),(0,[z207,z44,z1,z2,z3,z4])],[(0,[z44,z0,z1,z2,z3,z473])],[(0,[z0,z205,z2,z35,z4,z7]),(0,[z44,z0,z1,z2,z128,z22]),(0,[z637,z1,z2,z3,z4,z10])],[(0,[z0,z1,z2,z453,z4,z29]),(0,[z0,z1,z2,z3,z954,z7]),(0,[z0,z1,z2,z3,z955,z7])],[(0,[z0,z1,z17,z3,z4,z7]),(0,[z956,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z957]),(0,[z0,z1,z224,z158,z4,z225]),(0,[z0,z1,z958,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z959]),(0,[z219,z1,z2,z3,z69,z7]),(0,[z44,z1,z2,z3,z4,z813]),(0,[z0,z1,z2,z3,z4,z960]),(0,[z0,z1,z2,z132,z22,z7])]],
   [[(0,[z165,z55,z2,z3,z4,z10]),(0,[z0,z1,z2,z961,z4,z7]),(0,[z0,z1,z2,z962,z3,z4]),(0,[z569,z0,z154,z2,z3,z4])],[(0,[z0,z1,z324,z3,z473,z7]),(0,[z107,z0,z1,z70,z3,z4]),(0,[z0,z1,z839,z3,z4,z7]),(0,[z963,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z2,z965,z4,z7]),(0,[z0,z1,z2,z3,z4,z966]),(0,[z64,z1,z166,z3,z4,z41]),(0,[z44,z0,z1,z2,z399,z3])],[(0,[z0,z1,z2,z3,z714,z7])],[(0,[z0,z1,z967,z2,z3,z4]),(0,[z0,z1,z968,z3,z4,z7]),(0,[z0,z1,z2,z3,z969,z7]),(0,[z970,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z3,z4,z344,z41]),(0,[z0,z1,z307,z3,z76,z4])],[(0,[z0,z1,z2,z556,z4,z10]),(0,[z971,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z972])],[(0,[z0,z1,z2,z973,z3,z4]),(0,[z0,z1,z974,z307,z3,z4])],[(0,[z0,z1,z2,z975,z4,z7]),(0,[z0,z1,z2,z976,z4,z7]),(0,[z977,z0,z1,z2,z3,z4]),(0,[z0,z73,z2,z3,z4,z10]),(0,[z0,z1,z2,z604,z3,z386])],[(1,[z864,z2,z3,z4,z7]),(0,[z0,z1,z2,z978,z3,z4]),(1,[z723,z1,z2,z3,z4]),(0,[z0,z1,z979,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z980])],[(0,[z0,z1,z2,z3,z4,z981]),(0,[z982,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z737,z4,z41])],[(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z1,z2,z3,z131,z84])],[(0,[z156,z157,z2,z3,z4,z10]),(0,[z216,z0,z1,z2,z3,z375]),(0,[z0,z1,z2,z3,z4,z984])],[(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z1,z2,z3,z986,z4]),(0,[z51,z1,z2,z3,z86,z10]),(0,[z44,z1,z2,z3,z4,z688]),(0,[z0,z539,z2,z3,z4,z10]),(0,[z0,z1,z391,z3,z4,z41])],[(0,[z32,z1,z2,z762,z4,z7]),(0,[z0,z1,z2,z399,z426,z3]),(0,[z0,z1,z3,z4,z29,z41]),(0,[z0,z1,z2,z3,z4,z987])],[(0,[z0,z1,z2,z988,z4,z7]),(0,[z0,z1,z2,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z989]),(0,[z16,z0,z1,z2,z220,z4]),(0,[z0,z2,z3,z4,z38,z314])]],
   [[(0,[z16,z0,z1,z443,z3,z4]),(0,[z0,z1,z2,z990,z3,z4]),(0,[z0,z1,z2,z3,z4,z991])],[(0,[z0,z1,z443,z3,z4,z7]),(0,[z0,z1,z2,z3,z131,z10])],[(0,[z0,z1,z2,z453,z4,z265]),(0,[z0,z1,z2,z3,z4,z992]),(0,[z0,z1,z2,z993,z3,z4]),(0,[z64,z1,z833,z3,z4,z7]),(0,[z0,z1,z2,z3,z994,z4]),(0,[z0,z1,z995,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z996])],[(0,[z0,z1,z104,z3,z4,z41]),(0,[z0,z2,z3,z4,z247,z25])],[(0,[z107,z0,z1,z147,z3,z4]),(0,[z248,z1,z2,z33,z4,z305]),(0,[z0,z1,z2,z3,z997,z7]),(0,[z0,z1,z2,z788,z22,z7])],[(0,[z0,z1,z995,z3,z4,z7]),(0,[z0,z352,z2,z3,z172,z10])],[(0,[z0,z564,z2,z3,z4,z10]),(0,[z0,z1,z2,z14,z3,z465]),(0,[z0,z1,z2,z3,z4,z998])],[(0,[z0,z1,z272,z3,z4,z41]),(0,[z0,z1,z307,z3,z4,z27]),(0,[z0,z2,z3,z4,z25,z815]),(0,[z0,z1,z2,z31,z4,z195]),(0,[z0,z1,z158,z896,z4,z7])],[(0,[z0,z999,z1,z2,z3,z4]),(0,[z0,z1,z2,z212,z4,z461])],[(0,[z16,z0,z1,z968,z3,z4])],[(0,[z16,z0,z1,z2,z3,z138])],[(0,[z0,z1,z2,z453,z4,z304]),(0,[z219,z1,z2,z3,z892,z7]),(0,[z1000,z1,z2,z3,z4,z7]),(0,[z0,z2,z3,z4,z815,z10])],[(0,[z44,z548,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1001])],[(0,[z16,z0,z1,z2,z3,z360]),(0,[z1002,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z2,z3,z1004,z4])],[(0,[z1,z272,z3,z4,z68,z41]),(0,[z1005,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1006,z7])]],
   [[(0,[z0,z1,z2,z1007,z3,z4]),(0,[z0,z1,z147,z3,z4,z41]),(0,[z0,z1,z2,z1008,z4,z7]),(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1,z2,z3,z4,z1010]),(0,[z198,z0,z1,z3,z4,z277])],[(0,[z16,z1,z2,z192,z3,z4]),(0,[z1011,z0,z1,z2,z3,z4]),(0,[z0,z1,z742,z3,z4,z25]),(0,[z107,z0,z1,z3,z4,z29])],[(0,[z0,z1,z2,z3,z4,z1012]),(0,[z0,z1,z2,z3,z473,z41]),(0,[z0,z1,z2,z1013,z3,z4]),(0,[z637,z1,z87,z3,z4,z7]),(0,[z0,z52,z103,z3,z4,z29])],[(0,[z0,z1,z2,z3,z1014,z7]),(0,[z242,z16,z1,z272,z3,z4]),(0,[z0,z1,z2,z3,z1015,z7]),(0,[z0,z1,z1016,z3,z4,z7]),(0,[z0,z1,z2,z229,z4,z29])],[(0,[z0,z1,z1017,z2,z3,z4]),(0,[z0,z1,z742,z3,z4,z7]),(0,[z156,z157,z2,z3,z4,z63]),(0,[z0,z213,z2,z3,z4,z10]),(0,[z1018,z0,z1,z2,z3,z4]),(0,[z0,z1,z307,z31,z3,z4]),(0,[z198,z0,z1,z3,z4,z29]),(0,[z1019,z0,z1,z2,z3,z4])],[(0,[z637,z1,z103,z3,z4,z7]),(0,[z0,z1,z2,z491,z4,z29])],[(0,[z16,z44,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z1,z3,z738,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1021]),(0,[z0,z1,z17,z3,z4,z344]),(0,[z0,z1,z307,z1022,z3,z4]),(0,[z16,z1,z2,z3,z4,z813]),(0,[z1023,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z1024,z3,z7]),(0,[z0,z1,z2,z3,z4,z1025]),(0,[z42,z0,z1,z272,z3,z4]),(0,[z0,z1,z2,z1026,z3,z4]),(0,[z0,z1,z307,z3,z35,z4]),(0,[z0,z1027,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z314]),(0,[z0,z1,z2,z3,z1028,z7]),(0,[z0,z653,z2,z3,z21,z7]),(0,[z0,z1,z2,z3,z4,z1029])],[(0,[z0,z1,z324,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1030]),(0,[z0,z1,z2,z3,z4,z1031]),(0,[z16,z374,z1,z2,z3,z4])],[(0,[z0,z1,z1032,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1033]),(0,[z0,z1,z147,z307,z3,z4]),(0,[z0,z1,z2,z76,z129,z7]),(0,[z207,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z1034,z3,z4])],[(0,[z637,z1,z2,z3,z18,z7]),(0,[z0,z2,z3,z4,z10,z467]),(0,[z0,z1,z2,z3,z4,z1035])],[(0,[z0,z1,z2,z331,z4,z114])],[(0,[z0,z1,z307,z3,z4,z10]),(0,[z44,z0,z52,z103,z3,z4]),(0,[z445,z1,z2,z3,z4,z686])],[(0,[z0,z1,z443,z3,z473,z7]),(0,[z0,z1,z2,z146,z4,z25]),(0,[z569,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1036])],[(0,[z0,z1,z2,z3,z4,z1037]),(0,[z219,z0,z1,z307,z3,z4]),(0,[z0,z1038,z1,z2,z3,z4]),(0,[z0,z130,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z1039,z7]),(0,[z0,z2,z3,z4,z277,z247])]],
   [[(0,[z0,z1,z2,z1040,z3,z4]),(0,[z0,z1,z2,z3,z15,z361]),(0,[z0,z1,z2,z3,z4,z1041])],[(0,[z0,z1,z2,z3,z4,z1042]),(0,[z0,z1,z2,z3,z4,z1043]),(0,[z660,z16,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z18,z369]),(0,[z1044,z1,z2,z3,z4,z7]),(0,[z0,z1045,z1,z2,z3,z4]),(1,[z0,z2,z3,z761,z7]),(0,[z0,z1,z2,z120,z4,z25]),(0,[z0,z1,z2,z1046,z3,z4]),(0,[z0,z1,z2,z105,z76,z29]),(0,[z0,z1,z2,z3,z4,z1047])],[(0,[z0,z1,z2,z3,z1048,z7]),(0,[z0,z1,z2,z1049,z3,z4])],[(0,[z165,z0,z1,z307,z3,z4]),(0,[z568,z0,z1,z2,z255,z4]),(0,[z61,z0,z1,z1050,z3,z4])],[(0,[z0,z1,z324,z3,z138,z7]),(0,[z0,z1,z2,z31,z640,z4])],[(0,[z637,z1,z2,z3,z4,z29])],[(0,[z0,z1,z154,z2,z3,z4]),(0,[z0,z1,z166,z3,z4,z38]),(0,[z0,z1,z2,z399,z80,z3]),(0,[z1,z2,z3,z4,z880,z314]),(0,[z0,z1051,z1,z2,z3,z4]),(0,[z0,z1,z11,z12,z4,z10]),(0,[z0,z1,z2,z3,z4,z1052])],[(0,[z0,z1,z2,z1053,z4,z7]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z470,z1,z2,z3,z86,z7]),(0,[z0,z1,z2,z128,z60,z7]),(0,[z0,z1,z2,z3,z4,z1055])],[(0,[z50,z0,z1,z2,z497,z4]),(0,[z0,z666,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z4,z1056]),(0,[z165,z55,z2,z3,z4,z29]),(0,[z0,z1,z166,z3,z4,z67]),(0,[z0,z1,z2,z4,z7,z1057])],[(0,[z0,z1,z272,z3,z4,z314]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z16,z1,z2,z3,z4,z663])],[(0,[z0,z1,z1059,z2,z3,z4]),(0,[z248,z1,z2,z33,z4,z41]),(0,[z0,z1,z307,z3,z4,z1060]),(0,[z0,z2,z87,z3,z4,z247]),(0,[z0,z52,z2,z3,z4,z247])],[(0,[z0,z1,z2,z3,z1061,z4]),(0,[z0,z1,z166,z3,z4,z79]),(0,[z0,z1,z2,z3,z4,z813]),(0,[z44,z0,z20,z2,z3,z21]),(0,[z0,z1,z2,z3,z4,z1062])],[(0,[z0,z1,z2,z1063,z3,z7]),(0,[z0,z58,z2,z45,z131,z7])],[(0,[z0,z1,z1064,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1065]),(0,[z16,z0,z1,z2,z3,z1066]),(0,[z637,z1,z2,z244,z4,z7]),(0,[z0,z1,z2,z3,z4,z84])],[(0,[z32,z1,z2,z74,z4,z41]),(0,[z0,z1,z2,z762,z4,z7]),(0,[z0,z1,z2,z556,z4,z29]),(0,[z0,z1,z2,z1026,z556,z4]),(0,[z0,z1067,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z7,z813]),(0,[z44,z0,z1,z2,z3,z1068]),(0,[z0,z1,z2,z3,z4,z1069])]],
   [[(0,[z1070,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z101,z3,z27]),(0,[z243,z1,z2,z3,z4,z369])],[(0,[z16,z0,z1,z2,z244,z4]),(0,[z0,z1,z2,z3,z4,z815])],[(0,[z61,z1,z2,z3,z4,z586]),(0,[z0,z1,z2,z3,z954,z41]),(0,[z0,z1,z106,z3,z4,z29])],[(0,[z0,z1,z17,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1071])],[(0,[z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1,z658,z3,z4,z41]),(0,[z219,z1,z2,z3,z69,z41]),(0,[z16,z0,z1,z1073,z3,z4]),(0,[z1074,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z244,z4,z369]),(0,[z0,z1,z2,z3,z4,z439]),(0,[z107,z0,z1,z3,z4,z150]),(0,[z0,z141,z2,z3,z4,z314])],[(0,[z156,z157,z2,z3,z4,z29]),(0,[z0,z352,z2,z3,z172,z171])],[(0,[z0,z809,z2,z3,z4,z7]),(0,[z0,z1,z2,z1075,z3,z4]),(0,[z0,z9,z154,z2,z3,z4]),(0,[z0,z1,z307,z3,z4,z46]),(0,[z0,z259,z2,z3,z4,z10]),(0,[z0,z1,z2,z1076,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1077]),(0,[z44,z534,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z3,z18])],[(0,[z0,z1,z2,z1078,z4,z7]),(0,[z637,z1,z2,z3,z275,z7]),(0,[z0,z1,z2,z4,z788,z7])],[(0,[z0,z1,z151,z3,z26,z25]),(0,[z0,z1,z2,z3,z4,z1079])],[(0,[z0,z1,z2,z3,z4,z1080]),(0,[z0,z1,z1073,z3,z4,z7]),(0,[z358,z1,z2,z33,z4,z7]),(0,[z0,z1,z2,z105,z347,z7]),(0,[z0,z1,z2,z1081,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1082]),(0,[z219,z1,z2,z194,z3,z69]),(0,[z0,z1,z307,z3,z4,z22]),(0,[z0,z1,z2,z3,z4,z1083]),(0,[z0,z1,z2,z741,z4,z10]),(0,[z0,z1,z2,z3,z4,z1084])],[(0,[z0,z1,z2,z1085,z4,z7]),(0,[z0,z1,z2,z1086,z3,z4]),(0,[z568,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1087]),(0,[z0,z1,z151,z3,z26,z7])],[(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z1,z17,z307,z3,z4]),(0,[z44,z1,z2,z122,z3,z4]),(0,[z0,z1,z3,z4,z29,z439]),(0,[z0,z1,z410,z3,z4,z29])],[(0,[z165,z55,z2,z3,z4,z265]),(0,[z0,z1,z2,z3,z4,z1089]),(0,[z0,z1,z2,z3,z275,z369]),(0,[z1090,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z233]),(0,[z0,z352,z2,z3,z172,z29]),(0,[z0,z1,z2,z3,z4,z1091])],[(0,[z0,z1,z2,z3,z4,z1092]),(0,[z0,z1,z2,z3,z4,z1093]),(0,[z0,z1,z2,z3,z4,z1094])]],
   [[(0,[z0,z1,z2,z3,z4,z1095]),(0,[z0,z1,z2,z3,z4,z1096]),(0,[z16,z243,z1,z2,z3,z4]),(0,[z71,z1,z2,z3,z4,z553])],[(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z9,z2,z3,z4,z815])],[(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z20,z2,z3,z21,z25])],[(0,[z0,z1,z2,z3,z4,z1099]),(0,[z0,z1,z1100,z3,z4,z7]),(0,[z143,z0,z87,z3,z4,z369])],[(0,[z207,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z1101,z4]),(0,[z0,z1,z2,z497,z4,z190]),(0,[z0,z34,z2,z35,z4,z25]),(0,[z0,z1,z2,z1102,z4,z7])],[(0,[z0,z1,z2,z3,z138,z41]),(0,[z156,z0,z119,z2,z3,z4]),(0,[z16,z0,z1,z17,z3,z4]),(0,[z1103,z0,z1,z2,z3,z4]),(0,[z0,z20,z2,z3,z21,z7])],[(0,[z0,z1,z443,z3,z4,z41]),(0,[z0,z1,z2,z937,z4,z7]),(0,[z514,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z0,z1,z272,z3,z4,z439]),(0,[z0,z1,z2,z105,z556,z7]),(0,[z0,z1,z2,z105,z273,z7]),(0,[z1,z2,z3,z4,z880,z41])],[(0,[z165,z55,z2,z3,z4,z304]),(0,[z0,z34,z2,z35,z4,z7])],[(0,[z0,z1,z1105,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1106])],[(0,[z0,z901,z2,z3,z4,z7])],[],[],[(0,[z0,z1,z2,z3,z4,z63]),(0,[z16,z0,z1,z2,z900,z4]),(0,[z0,z1,z2,z3,z4,z1107]),(0,[z0,z1,z2,z3,z4,z1108])],[(0,[z0,z58,z1,z307,z3,z4]),(0,[z0,z2,z3,z4,z25,z10]),(0,[z0,z1,z2,z3,z4,z1109]),(0,[z0,z1,z2,z541,z4,z404])],[(0,[z0,z1,z2,z3,z4,z1110]),(0,[z0,z1,z2,z3,z4,z1111]),(0,[z64,z1,z166,z3,z4,z167]),(0,[z0,z1112,z1,z307,z3,z4]),(0,[z16,z0,z1,z2,z178,z4]),(0,[z16,z0,z1,z2,z3,z501])],[(0,[z0,z1,z2,z3,z4,z1113]),(0,[z0,z1,z1114,z2,z3,z4]),(0,[z0,z1,z2,z31,z255,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z1115])],[(0,[z0,z1,z443,z3,z138,z7]),(0,[z0,z1,z2,z3,z1116,z7]),(0,[z0,z1,z2,z3,z4,z167]),(0,[z0,z1,z2,z399,z45,z7]),(0,[z248,z1,z2,z762,z4,z7]),(0,[z0,z1,z2,z3,z4,z191])],[(0,[z0,z1,z2,z1117,z3,z4]),(0,[z0,z1,z2,z3,z4,z1118]),(0,[z1119,z0,z1,z2,z3,z4]),(0,[z1120,z1,z2,z3,z4,z7])],[(0,[z1,z833,z272,z3,z4,z7]),(0,[z299,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1121]),(0,[z0,z1,z3,z896,z4,z7])],[(0,[z0,z1,z2,z1122,z4,z7]),(0,[z16,z0,z20,z2,z3,z21]),(0,[z0,z1,z2,z3,z4,z610]),(0,[z0,z52,z103,z3,z4,z411]),(0,[z0,z1,z2,z3,z624,z24]),(0,[z0,z1,z101,z3,z738,z7]),(1,[z0,z1,z2,z788,z7]),(0,[z0,z1,z2,z3,z4,z1123])],[(0,[z0,z1,z2,z3,z4,z1124]),(0,[z0,z1,z166,z3,z4,z754]),(0,[z0,z1,z2,z3,z4,z1125]),(0,[z1126,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z955,z314]),(0,[z0,z1,z2,z23,z4,z190]),(0,[z0,z1,z2,z3,z4,z1127]),(0,[z0,z1,z101,z3,z27,z266]),(0,[z0,z1,z2,z3,z15,z24])],[(0,[z16,z0,z1,z2,z3,z473]),(0,[z0,z154,z2,z3,z35,z4]),(0,[z0,z1,z307,z3,z4,z29]),(0,[z0,z58,z2,z45,z4,z161]),(0,[z0,z1,z2,z382,z3,z214]),(0,[z107,z0,z1,z3,z4,z731]),(0,[z0,z1,z2,z3,z4,z1128])],[(0,[z16,z0,z1,z2,z128,z22]),(0,[z0,z20,z2,z3,z761,z7]),(0,[z0,z1,z2,z128,z22,z25]),(0,[z1129,z0,z1,z2,z3,z4])],[(0,[z16,z0,z1,z101,z3,z27]),(0,[z0,z1,z2,z3,z4,z1130])],[(0,[z0,z1,z1131,z2,z3,z7])],[(0,[z44,z0,z1,z2,z229,z4]),(0,[z0,z1,z3,z4,z311,z41]),(0,[z0,z1,z2,z128,z22,z7])],[(0,[z0,z393,z103,z3,z4,z7]),(0,[z51,z0,z1,z2,z229,z7]),(0,[z44,z0,z1,z2,z3,z1116]),(0,[z0,z1,z2,z3,z4,z1132]),(0,[z0,z1,z2,z471,z3,z97])],[(0,[z0,z1,z2,z3,z4,z1133]),(0,[z0,z1,z2,z229,z194,z4]),(0,[z118,z0,z1,z307,z3,z4])],[(0,[z44,z0,z1,z2,z146,z4]),(0,[z1,z2,z833,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1134]),(0,[z0,z1,z2,z3,z360,z29]),(0,[z16,z0,z1,z2,z399,z3]),(0,[z0,z58,z2,z45,z4,z25]),(0,[z0,z1,z2,z3,z4,z1135]),(0,[z0,z1,z2,z3,z4,z1136])],[(0,[z0,z1,z2,z3,z4,z1137]),(0,[z0,z1,z307,z3,z4,z24]),(0,[z0,z2,z3,z4,z38,z10])],[(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z2,z3,z1139,z4]),(0,[z16,z0,z1,z2,z3,z18]),(0,[z0,z1,z2,z3,z4,z1140]),(0,[z0,z1,z11,z12,z4,z184]),(0,[z0,z1,z11,z12,z4,z29]),(0,[z0,z1,z2,z3,z4,z1141])]],
   [[(0,[z0,z1,z2,z147,z3,z4]),(0,[z32,z1,z2,z74,z57,z7]),(0,[z0,z1,z307,z212,z3,z4]),(0,[z0,z1,z2,z3,z18,z25]),(0,[z0,z58,z2,z45,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1142]),(0,[z44,z0,z1,z324,z3,z4]),(0,[z157,z864,z2,z3,z4,z7]),(0,[z0,z1,z70,z3,z4,z41]),(0,[z0,z1,z668,z158,z4,z7]),(0,[z0,z13,z2,z3,z4,z25])],[(0,[z637,z1,z2,z178,z4,z7]),(0,[z0,z1,z2,z3,z4,z1143]),(0,[z0,z1,z2,z3,z4,z1144]),(0,[z0,z1,z85,z3,z4,z41]),(0,[z1145,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1146]),(0,[z0,z1,z2,z3,z4,z1147]),(0,[z0,z1,z154,z307,z3,z4]),(0,[z1148,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z18,z7])],[(0,[z0,z1,z2,z146,z4,z7]),(0,[z0,z1,z1149,z3,z4,z7]),(0,[z16,z1,z307,z3,z4,z46]),(0,[z0,z1,z1150,z2,z3,z4])],[(0,[z0,z1,z848,z3,z4,z7])],[(0,[z156,z864,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1151]),(0,[z0,z1,z2,z3,z4,z115])],[(0,[z0,z1,z324,z3,z4,z1099]),(0,[z0,z1,z2,z3,z4,z1152]),(0,[z0,z1,z2,z120,z4,z7])],[(0,[z0,z1,z2,z178,z4,z369]),(0,[z0,z1,z2,z1153,z4,z7])],[(0,[z0,z1,z2,z1154,z3,z4]),(0,[z0,z1,z2,z1155,z3,z4])],[(0,[z0,z1,z95,z3,z4,z41])],[(0,[z0,z1,z2,z3,z57,z41]),(0,[z44,z0,z1,z2,z3,z131])],[(0,[z0,z1,z1050,z3,z4,z7]),(0,[z0,z1,z158,z3,z4,z439])],[(0,[z44,z0,z1,z2,z453,z4]),(0,[z0,z1,z2,z1156,z3,z4]),(0,[z0,z1,z307,z3,z336,z4]),(0,[z0,z1,z476,z3,z4,z439]),(0,[z0,z1,z2,z3,z4,z184])],[(0,[z32,z1,z2,z74,z4,z10]),(0,[z0,z1,z2,z3,z1157,z4]),(0,[z283,z0,z1,z70,z3,z4]),(0,[z0,z140,z2,z3,z4,z25])],[(0,[z243,z1,z2,z3,z4,z25])]],
   [[(0,[z242,z367,z1,z272,z3,z4]),(0,[z0,z1,z2,z1158,z4,z7]),(0,[z0,z1,z2,z3,z4,z1159])],[(0,[z0,z1,z2,z146,z138,z7])],[(0,[z243,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1160,z7]),(0,[z181,z1,z2,z74,z4,z7]),(0,[z0,z1,z17,z3,z4,z10]),(0,[z0,z1,z2,z578,z3,z89])],[(0,[z0,z157,z1,z307,z3,z4]),(0,[z0,z1,z307,z272,z3,z4]),(0,[z0,z136,z2,z3,z4,z10]),(0,[z219,z1,z2,z3,z69,z10]),(0,[z44,z0,z1,z2,z1161,z4]),(0,[z0,z1,z2,z244,z4,z25]),(0,[z0,z1,z2,z3,z4,z173]),(0,[z1162,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1163]),(0,[z0,z1,z95,z307,z3,z4]),(0,[z44,z0,z1,z2,z491,z4]),(0,[z0,z1,z2,z3,z1164,z7]),(0,[z0,z1,z390,z3,z4,z29])],[(0,[z207,z157,z1,z2,z3,z4]),(0,[z242,z1,z272,z3,z4,z79]),(0,[z0,z1,z224,z158,z4,z25]),(0,[z0,z1,z2,z3,z955,z41])],[(0,[z44,z0,z34,z2,z35,z4]),(0,[z0,z1,z405,z3,z4,z29])],[(0,[z534,z1,z166,z3,z4,z7]),(0,[z0,z1,z2,z45,z131,z7]),(0,[z0,z1,z2,z3,z4,z1165])],[(0,[z0,z1,z2,z3,z1166,z7]),(0,[z0,z1,z2,z3,z4,z1167]),(0,[z51,z44,z1,z2,z3,z86]),(0,[z0,z1,z2,z1168,z3,z4]),(0,[z0,z1,z2,z3,z4,z1169]),(0,[z0,z1,z224,z158,z4,z7])],[(0,[z51,z1,z2,z3,z86,z29])],[(0,[z0,z1,z2,z3,z4,z1170])],[(0,[z0,z1,z2,z3,z4,z1171]),(0,[z0,z1,z2,z3,z4,z1172]),(0,[z0,z1,z312,z3,z4,z41]),(0,[z40,z0,z2,z3,z4,z38]),(0,[z0,z1,z2,z578,z3,z546]),(0,[z0,z1,z2,z3,z952,z89])],[(0,[z0,z1,z2,z1173,z3,z4]),(0,[z0,z1,z2,z3,z1068,z7])],[(0,[z0,z1,z2,z3,z4,z1174]),(0,[z0,z1,z2,z229,z360,z7]),(0,[z0,z1,z2,z3,z275,z25]),(0,[z0,z1,z2,z3,z131,z29])],[(0,[z0,z1,z2,z3,z4,z1175]),(0,[z156,z598,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z0,z1,z2,z1177,z3,z4]),(0,[z16,z0,z1,z1178,z3,z4]),(0,[z44,z1,z2,z3,z4,z577]),(0,[z0,z2,z3,z180,z4,z10]),(0,[z0,z1,z2,z3,z4,z1179])],[(0,[z0,z1,z2,z3,z4,z1180]),(0,[z143,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1181])]],
   [[(0,[z0,z1,z2,z3,z4,z1182]),(0,[z16,z0,z1,z2,z1183,z4]),(0,[z61,z1,z2,z3,z4,z46]),(0,[z179,z44,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z29,z571]),(0,[z0,z1,z2,z3,z275,z7]),(0,[z0,z1,z2,z3,z4,z1184])],[(0,[z0,z1,z2,z146,z473,z7]),(0,[z0,z1,z2,z1185,z4,z7]),(0,[z0,z1,z2,z3,z4,z1186]),(0,[z0,z1,z2,z3,z4,z1187]),(0,[z0,z1,z2,z1188,z4,z7])],[(0,[z0,z1,z2,z3,z4,z265]),(0,[z143,z0,z87,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z1189])],[(0,[z0,z1,z2,z1190,z4,z7]),(0,[z0,z1,z2,z1191,z3,z4]),(0,[z0,z1,z2,z3,z4,z1192])],[(0,[z0,z1,z2,z3,z138,z10]),(0,[z0,z1,z2,z1193,z4,z7]),(1,[z0,z1,z742,z3,z4]),(0,[z0,z2,z3,z4,z1194,z7]),(0,[z0,z1,z2,z3,z1195,z7]),(0,[z0,z1,z2,z399,z35,z7]),(0,[z0,z1,z2,z3,z4,z1196]),(0,[z0,z1,z2,z1197,z3,z4]),(0,[z0,z1,z2,z3,z4,z1198])],[(0,[z0,z1,z443,z3,z4,z10]),(0,[z16,z452,z1,z2,z3,z4]),(0,[z143,z0,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1199]),(0,[z1,z2,z3,z4,z880,z10]),(0,[z0,z460,z2,z3,z4,z10])],[(0,[z44,z0,z1,z2,z120,z4]),(0,[z0,z1,z104,z12,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1200]),(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z994,z360]),(0,[z143,z637,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1201]),(0,[z0,z9,z2,z3,z4,z10]),(0,[z1202,z0,z1,z2,z3,z4])],[(0,[z0,z1,z443,z3,z4,z1077]),(0,[z0,z1,z324,z146,z4,z7]),(0,[z0,z1,z2,z3,z4,z1203]),(0,[z0,z1,z251,z3,z4,z41]),(0,[z0,z300,z1,z307,z3,z4]),(0,[z16,z0,z52,z103,z3,z4]),(0,[z0,z2,z3,z4,z25,z647]),(0,[z0,z1,z151,z3,z26,z196])],[(0,[z162,z0,z1,z995,z3,z4]),(0,[z207,z1,z272,z3,z4,z41]),(0,[z0,z1,z2,z80,z280,z3]),(0,[z0,z1,z2,z1204,z3,z4])],[(0,[z0,z20,z2,z3,z21,z41]),(0,[z0,z174,z2,z3,z4,z247])],[(0,[z242,z1,z272,z3,z4,z25]),(0,[z1205,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1206])],[(0,[z0,z1,z2,z3,z4,z1207]),(0,[z0,z1,z2,z3,z4,z1208]),(0,[z0,z34,z2,z35,z4,z41]),(0,[z1209,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1210])],[(0,[z0,z1,z2,z128,z30,z22])],[(0,[z16,z0,z1,z2,z907,z4])],[(0,[z0,z1,z2,z3,z1211,z7]),(0,[z0,z1,z2,z1212,z3,z4]),(0,[z0,z1,z438,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1213]),(0,[z0,z1,z101,z3,z27,z383])]],
   [[(0,[z0,z1,z2,z3,z1214,z4]),(0,[z0,z1,z2,z70,z3,z4]),(0,[z0,z1,z2,z194,z230,z4]),(0,[z0,z1,z2,z3,z4,z150])],[(0,[z0,z1,z1215,z3,z4,z7]),(0,[z207,z0,z1,z166,z3,z4]),(0,[z0,z1,z2,z3,z1216,z7]),(0,[z0,z1,z3,z4,z41,z378])],[(0,[z0,z1,z2,z1217,z3,z4]),(0,[z545,z0,z119,z2,z3,z4])],[(0,[z1218,z0,z1,z2,z3,z4]),(0,[z0,z1,z570,z3,z26,z7]),(0,[z0,z141,z2,z3,z4,z10]),(0,[z0,z1,z101,z3,z27,z25]),(0,[z1219,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z14,z3,z89])],[(0,[z0,z1,z2,z3,z473,z10]),(0,[z0,z1,z2,z229,z421,z4]),(0,[z0,z1,z2,z1220,z3,z4]),(0,[z0,z1,z2,z331,z4,z183]),(0,[z0,z1,z2,z541,z4,z190]),(0,[z0,z1,z2,z3,z4,z1221])],[(0,[z16,z0,z1,z2,z453,z4]),(0,[z16,z44,z1,z17,z3,z4]),(0,[z0,z1,z2,z4,z1222,z7]),(0,[z0,z1,z2,z1223,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1224]),(0,[z248,z44,z1,z2,z33,z4]),(0,[z0,z1,z101,z3,z27,z7])],[(0,[z0,z1,z2,z3,z4,z1225]),(0,[z0,z1,z2,z3,z4,z1226])],[],[],[(0,[z42,z0,z1,z2,z1227,z4]),(0,[z0,z1,z2,z80,z3,z4]),(0,[z332,z0,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z1228])],[(0,[z0,z1,z324,z3,z4,z10]),(0,[z0,z1,z1229,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1230]),(0,[z0,z1,z2,z3,z4,z1231]),(0,[z0,z1,z2,z3,z7,z1232]),(0,[z0,z1,z2,z3,z1233,z4]),(0,[z0,z544,z2,z3,z4,z10])],[(0,[z135,z0,z119,z2,z3,z4]),(0,[z0,z2,z3,z761,z4,z7])],[(0,[z0,z1,z1234,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1235]),(0,[z16,z0,z34,z2,z35,z4])],[(0,[z0,z1,z2,z128,z22,z41]),(0,[z0,z1,z2,z3,z4,z1236])]],
   [[(0,[z44,z0,z1,z2,z3,z57])],[(0,[z0,z1,z2,z3,z4,z1237]),(0,[z1238,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z230,z4]),(0,[z0,z1,z2,z3,z1239,z4]),(0,[z0,z1,z307,z3,z255,z4]),(0,[z0,z1,z3,z26,z4,z439]),(0,[z0,z1,z2,z3,z15,z121])],[(0,[z0,z1,z1240,z2,z3,z7]),(0,[z1,z2,z3,z892,z69,z7]),(0,[z219,z1,z2,z3,z421,z69]),(0,[z16,z318,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1241])],[(0,[z0,z1,z2,z1242,z4,z7]),(0,[z0,z1,z2,z1243,z3,z4]),(1,[z0,z1,z896,z4,z7])],[(0,[z0,z1,z2,z1183,z4,z7]),(0,[z0,z1,z2,z426,z280,z3]),(0,[z0,z1,z2,z1244,z4,z7]),(0,[z0,z58,z2,z45,z4,z41]),(0,[z0,z1,z2,z3,z4,z1245])],[(0,[z0,z1,z2,z3,z4,z1246]),(0,[z0,z1,z3,z4,z754,z41]),(0,[z1247,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1248,z4,z7])],[(0,[z242,z0,z1,z307,z3,z4]),(0,[z0,z9,z1,z307,z3,z4]),(0,[z1249,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z178,z4,z25]),(0,[z0,z1,z2,z3,z4,z171])],[(0,[z1,z166,z272,z3,z4,z41]),(0,[z0,z1,z500,z3,z4,z41]),(0,[z0,z1,z2,z220,z4,z25]),(0,[z0,z81,z2,z3,z21,z7])],[(0,[z0,z1,z2,z146,z4,z41]),(0,[z165,z55,z2,z453,z4,z7]),(0,[z0,z1,z609,z3,z4,z41]),(0,[z0,z1,z2,z3,z7,z1250]),(0,[z0,z1,z2,z3,z4,z1251]),(0,[z0,z1,z3,z4,z150,z41]),(0,[z0,z2,z3,z4,z137,z25]),(0,[z0,z1,z95,z3,z4,z439])],[(0,[z0,z1,z2,z3,z4,z1252]),(0,[z0,z1,z2,z3,z57,z10]),(0,[z0,z1,z2,z178,z4,z7]),(0,[z1253,z1,z2,z3,z4,z7])],[(0,[z0,z1,z2,z1254,z3,z4]),(0,[z0,z1,z2,z220,z4,z7]),(0,[z0,z1,z2,z105,z303,z7])],[(0,[z0,z1,z2,z3,z4,z1255]),(0,[z1256,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z120,z4,z41])],[(0,[z0,z1,z2,z3,z1257,z4]),(0,[z248,z1,z2,z33,z4,z10]),(0,[z1258,z0,z1,z2,z3,z4])],[],[(0,[z0,z1,z2,z1259,z3,z4]),(0,[z0,z1,z2,z1260,z3,z4]),(0,[z0,z1,z307,z3,z4,z177]),(0,[z0,z2,z3,z761,z172,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z29]),(0,[z1261,z0,z1,z2,z3,z4]),(0,[z1262,z0,z1,z2,z3,z4])],[(0,[z0,z1263,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1264]),(0,[z0,z446,z2,z45,z4,z7]),(1,[z0,z2,z3,z4,z815])],[(0,[z0,z1,z2,z3,z4,z1265])],[(0,[z0,z52,z103,z3,z4,z67])],[(0,[z0,z1,z2,z3,z955,z10]),(0,[z0,z1,z2,z3,z1266,z7])],[(0,[z0,z1,z443,z146,z4,z7]),(0,[z0,z1,z2,z230,z4,z25])],[(0,[z0,z1,z2,z3,z4,z1267]),(0,[z0,z1,z2,z426,z3,z4]),(0,[z662,z0,z1,z2,z3,z465]),(0,[z0,z37,z2,z3,z172,z7]),(0,[z0,z1,z2,z1268,z3,z4]),(0,[z0,z1,z11,z896,z4,z7])],[(0,[z0,z1,z2,z1269,z4,z7]),(0,[z16,z51,z1,z2,z3,z86]),(0,[z243,z1,z2,z3,z4,z41])],[(0,[z1,z864,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z1270,z7]),(0,[z0,z1,z2,z230,z4,z7]),(1,[z0,z1,z848,z3,z4]),(0,[z0,z1,z2,z3,z4,z1271]),(0,[z0,z1,z2,z1272,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1273]),(0,[z0,z1,z2,z3,z4,z1274]),(0,[z0,z1,z2,z244,z4,z7]),(0,[z0,z1,z2,z3,z4,z1275]),(0,[z0,z1,z2,z3,z4,z1276])],[(0,[z0,z1,z2,z3,z4,z1277]),(0,[z44,z0,z1,z2,z105,z76]),(0,[z0,z1,z2,z3,z4,z1278]),(0,[z1279,z0,z1,z2,z3,z4])],[(0,[z42,z0,z1,z2,z3,z954]),(0,[z207,z64,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1280]),(0,[z0,z1,z2,z3,z1281,z7]),(0,[z0,z1,z2,z3,z4,z1282]),(0,[z0,z444,z2,z3,z172,z7]),(0,[z135,z1,z2,z3,z4,z577]),(0,[z0,z1,z2,z31,z4,z163])],[(0,[z0,z864,z2,z3,z4,z7]),(0,[z64,z0,z1,z307,z3,z4]),(0,[z0,z591,z2,z35,z4,z7]),(0,[z0,z1,z224,z158,z4,z41]),(0,[z1283,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z1284,z3,z4])],[(0,[z0,z1,z1285,z2,z3,z4]),(0,[z16,z1,z2,z3,z4,z46]),(0,[z0,z58,z2,z938,z4,z7])],[(0,[z0,z1,z1286,z3,z4,z7]),(0,[z0,z1,z2,z1287,z3,z4]),(0,[z16,z0,z1288,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1289])]],
   [[(0,[z0,z1,z2,z3,z4,z1290]),(1,[z1,z2,z3,z892,z7]),(0,[z1291,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1292]),(0,[z0,z1,z1293,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1294]),(0,[z0,z1,z2,z212,z4,z208])],[(0,[z0,z1,z2,z3,z1295,z7]),(0,[z1296,z0,z1,z2,z3,z4]),(0,[z627,z44,z1,z2,z3,z4]),(0,[z1291,z637,z1,z2,z3,z4])],[],[(0,[z0,z1,z2,z3,z4,z1297]),(0,[z723,z1,z2,z87,z3,z4]),(0,[z0,z1,z151,z3,z26,z41]),(0,[z0,z1,z2,z3,z409,z434])],[(0,[z16,z0,z1,z2,z229,z4]),(0,[z0,z1,z2,z3,z275,z41])],[(0,[z248,z1,z2,z366,z4,z7]),(0,[z51,z1,z2,z611,z3,z7]),(0,[z16,z0,z1298,z2,z3,z4])],[(0,[z1299,z1,z2,z3,z4,z7])],[(0,[z16,z0,z1,z2,z146,z4]),(0,[z64,z540,z1,z2,z3,z4]),(0,[z16,z0,z1,z2,z3,z57]),(0,[z0,z1,z307,z1300,z3,z4]),(0,[z16,z0,z1,z2,z3,z944]),(0,[z0,z1,z1301,z2,z3,z4]),(0,[z40,z0,z119,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1302])],[(0,[z0,z1,z2,z1303,z4,z7]),(0,[z143,z0,z87,z3,z4,z41]),(0,[z0,z1,z2,z3,z738,z7])],[(0,[z0,z1,z2,z1161,z4,z7]),(0,[z135,z0,z130,z2,z3,z4]),(0,[z0,z1,z2,z3,z1304,z7]),(0,[z0,z1,z2,z3,z501,z161]),(0,[z0,z1,z2,z3,z15,z952])],[(0,[z16,z0,z1,z324,z3,z4]),(0,[z0,z1288,z2,z3,z4,z7]),(0,[z44,z1,z2,z3,z4,z177]),(0,[z44,z0,z1,z2,z3,z954]),(0,[z0,z1,z3,z4,z150,z314]),(0,[z0,z1,z2,z3,z4,z1305])],[(0,[z0,z1,z2,z3,z473,z29]),(0,[z0,z1,z1306,z3,z4,z7]),(0,[z0,z1,z166,z3,z4,z41]),(0,[z0,z1,z2,z1307,z3,z4]),(0,[z61,z1,z166,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1308]),(0,[z0,z1,z2,z229,z4,z25]),(0,[z0,z1,z2,z3,z1309,z4])],[(0,[z0,z1,z2,z3,z4,z304]),(0,[z0,z1,z2,z3,z1310,z7]),(0,[z0,z1,z2,z3,z4,z1311])],[(0,[z0,z1,z774,z3,z4,z7]),(0,[z1312,z0,z1,z2,z3,z4]),(0,[z587,z0,z1,z2,z128,z7])]],
   [[(0,[z0,z1,z2,z1313,z3,z4]),(0,[z0,z1,z2,z229,z4,z7]),(0,[z0,z34,z1,z307,z3,z4])],[(0,[z0,z1,z2,z3,z1314,z7]),(0,[z242,z1,z272,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1315])],[(0,[z0,z1,z2,z3,z138,z265]),(0,[z0,z1,z2,z421,z230,z4]),(0,[z0,z1,z3,z4,z277,z439]),(0,[z0,z1,z2,z3,z501,z25]),(0,[z0,z1,z2,z3,z1316,z7])],[(0,[z0,z1,z443,z3,z4,z265]),(0,[z16,z1,z2,z132,z3,z4]),(0,[z0,z1,z2,z1317,z4,z7]),(0,[z0,z573,z2,z45,z4,z7])],[(0,[z0,z1,z324,z3,z4,z29]),(1,[z0,z1,z307,z3,z4]),(0,[z0,z1,z307,z33,z3,z4]),(0,[z0,z1318,z1,z2,z3,z4])],[(0,[z0,z1,z2,z280,z3,z25]),(0,[z0,z1,z2,z3,z501,z7]),(0,[z0,z1,z2,z3,z1319,z4])],[(0,[z0,z1,z2,z3,z1320,z7]),(0,[z16,z0,z1,z2,z3,z131]),(0,[z1321,z0,z1,z2,z3,z4])],[(0,[z0,z1,z166,z307,z3,z4]),(0,[z0,z1,z2,z3,z41,z854]),(0,[z0,z1,z2,z3,z788,z7])],[(0,[z0,z1,z2,z280,z3,z7]),(0,[z0,z1,z307,z3,z4,z109]),(0,[z0,z193,z2,z3,z4,z25])],[(0,[z219,z44,z1,z2,z3,z69]),(0,[z1322,z0,z1,z2,z3,z4]),(0,[z0,z593,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z4,z1323]),(0,[z40,z0,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z4,z1324]),(0,[z0,z1,z2,z4,z1222,z41])],[(0,[z165,z78,z55,z2,z3,z4]),(0,[z0,z1,z307,z87,z3,z4]),(0,[z584,z0,z1,z3,z4,z29]),(0,[z1325,z0,z1,z2,z3,z4]),(0,[z0,z1,z101,z3,z27,z41]),(0,[z1326,z1,z2,z3,z4,z7])],[(0,[z1327,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1328]),(0,[z0,z20,z154,z2,z3,z4]),(0,[z0,z1,z307,z3,z15,z4]),(0,[z16,z1,z2,z3,z4,z523])],[(0,[z0,z1,z833,z3,z4,z7]),(0,[z16,z201,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z731,z7])],[(0,[z0,z1,z87,z3,z4,z439]),(0,[z0,z1,z346,z3,z4,z41])],[(0,[z0,z365,z2,z45,z4,z7]),(0,[z16,z0,z1,z2,z491,z4]),(0,[z1329,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z30,z3,z4])]],
   [[(0,[z0,z1,z1330,z2,z3,z4]),(0,[z0,z1,z2,z1331,z3,z4])],[(0,[z392,z55,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1332]),(0,[z162,z0,z1,z742,z3,z4]),(0,[z0,z1,z2,z3,z4,z350]),(0,[z0,z1,z103,z3,z4,z439])],[(0,[z0,z1,z2,z3,z473,z265]),(0,[z0,z1,z1333,z2,z4,z7]),(0,[z0,z1,z2,z1334,z3,z4]),(0,[z0,z1,z154,z17,z3,z4]),(0,[z0,z1,z2,z3,z4,z1335])],[(0,[z637,z1,z2,z3,z4,z369])],[(0,[z0,z1,z2,z1336,z4,z7]),(0,[z0,z1,z2,z3,z4,z1337]),(0,[z367,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1338,z7]),(0,[z0,z1,z2,z3,z4,z1339])],[(0,[z0,z1,z2,z3,z4,z1340]),(0,[z51,z1,z2,z3,z86,z509])],[(0,[z0,z1,z1341,z3,z4,z7]),(0,[z162,z156,z157,z2,z3,z4]),(0,[z0,z1,z2,z399,z3,z25]),(0,[z248,z1,z2,z33,z4,z29]),(0,[z0,z1,z11,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1342])],[(0,[z156,z157,z2,z3,z4,z250]),(0,[z0,z1,z2,z1227,z4,z7]),(0,[z0,z1,z2,z3,z4,z1343]),(0,[z16,z1,z2,z3,z4,z686]),(0,[z1344,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1345])],[(0,[z0,z1,z2,z146,z4,z10]),(0,[z207,z0,z1,z272,z3,z4])],[(0,[z0,z1,z324,z3,z4,z265]),(0,[z0,z1,z2,z399,z3,z7]),(0,[z0,z1,z2,z1212,z556,z4]),(0,[z0,z1,z2,z3,z4,z1346]),(0,[z0,z1,z2,z3,z295,z403]),(0,[z0,z1,z11,z12,z4,z185])],[(0,[z1,z55,z443,z3,z4,z7]),(0,[z0,z1,z2,z453,z4,z25]),(0,[z32,z1,z2,z74,z4,z29]),(0,[z219,z1,z2,z220,z69,z7]),(0,[z1,z2,z3,z892,z4,z7]),(0,[z723,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1347])],[(0,[z0,z1,z2,z3,z473,z304]),(0,[z585,z1,z166,z3,z4,z7]),(0,[z1,z2,z3,z86,z892,z7]),(0,[z0,z1,z2,z3,z18,z41]),(0,[z0,z1,z2,z3,z4,z1348]),(0,[z0,z1,z2,z120,z4,z10]),(0,[z0,z1,z2,z372,z4,z195]),(0,[z0,z1,z2,z3,z4,z952])],[(0,[z0,z1,z2,z3,z4,z1349]),(0,[z0,z1,z2,z3,z4,z397])],[(0,[z0,z1,z2,z453,z4,z7]),(0,[z0,z1,z2,z1350,z4,z7]),(0,[z143,z0,z87,z3,z4,z314])],[(0,[z0,z1,z17,z3,z4,z29]),(0,[z44,z0,z1,z2,z1227,z4]),(0,[z0,z1,z2,z3,z1351,z7]),(0,[z0,z2,z373,z3,z4,z25])],[(0,[z219,z1,z2,z3,z69,z29]),(0,[z0,z1,z307,z3,z4,z172]),(0,[z0,z1,z1352,z307,z3,z4]),(0,[z0,z1,z103,z307,z3,z4]),(0,[z0,z1,z2,z178,z4,z41]),(0,[z0,z1,z2,z3,z4,z277])]],
   [[(0,[z0,z1,z2,z1353,z4,z7]),(0,[z0,z1,z166,z3,z4,z314]),(0,[z0,z1,z2,z220,z4,z41]),(0,[z0,z1,z2,z1354,z4,z7]),(0,[z0,z1,z1050,z3,z4,z10])],[(0,[z156,z0,z1,z742,z3,z4]),(0,[z0,z1,z2,z3,z4,z1355]),(0,[z16,z0,z1,z2,z120,z4]),(0,[z0,z1,z2,z3,z4,z152])],[(0,[z0,z1,z324,z3,z4,z304]),(0,[z0,z1,z926,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1356]),(0,[z219,z0,z1,z2,z229,z7]),(0,[z0,z1,z2,z229,z21,z7]),(0,[z0,z1,z2,z3,z4,z411])],[(0,[z0,z1,z1357,z3,z4,z7]),(0,[z0,z1,z1358,z3,z4,z7]),(0,[z16,z0,z1,z1359,z3,z4]),(0,[z662,z0,z1,z307,z3,z4]),(0,[z0,z2,z3,z4,z351,z10]),(0,[z0,z1,z2,z3,z4,z1360]),(0,[z0,z1,z2,z76,z788,z7])],[(0,[z162,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z491,z21,z7]),(0,[z0,z1,z2,z1361,z3,z7])],[(0,[z0,z1,z2,z3,z4,z565]),(0,[z0,z1,z2,z3,z4,z731])],[(0,[z1362,z0,z1,z2,z3,z4]),(0,[z0,z1363,z2,z3,z4,z7]),(0,[z243,z1,z2,z3,z4,z10])],[(0,[z0,z1364,z2,z3,z4,z7]),(0,[z219,z1,z2,z230,z69,z7]),(0,[z44,z0,z1,z1064,z3,z4]),(0,[z0,z1,z2,z3,z4,z185])],[],[(0,[z0,z1,z2,z3,z4,z1365]),(0,[z0,z1,z307,z128,z3,z4]),(0,[z0,z1,z2,z1366,z3,z4]),(0,[z44,z355,z1,z2,z3,z4]),(0,[z143,z243,z87,z3,z4,z7]),(0,[z1367,z0,z1,z2,z3,z4])],[],[(0,[z0,z1,z2,z3,z4,z1368]),(0,[z329,z0,z1,z2,z394,z4]),(0,[z1369,z1,z2,z3,z4,z7]),(0,[z0,z20,z2,z3,z21,z115])],[(0,[z16,z1,z17,z3,z4,z46]),(0,[z0,z20,z2,z120,z21,z7]),(0,[z0,z1,z224,z158,z4,z10])],[(0,[z0,z1,z2,z230,z4,z41]),(0,[z0,z1,z307,z3,z26,z4]),(0,[z16,z0,z1,z2,z3,z1216]),(0,[z0,z1,z2,z4,z1222,z314]),(0,[z0,z1,z2,z3,z4,z1370])],[(0,[z0,z1,z2,z244,z4,z41]),(0,[z0,z1,z2,z3,z4,z1371]),(0,[z0,z1,z3,z4,z29,z731])],[(0,[z0,z1,z2,z1372,z4,z7]),(0,[z0,z1,z93,z3,z4,z41]),(0,[z0,z1,z2,z3,z4,z1373])]],
   [[(0,[z0,z1,z2,z3,z138,z29]),(0,[z0,z1,z2,z1374,z3,z7]),(0,[z866,z0,z1,z2,z3,z4])],[(0,[z0,z1,z443,z3,z4,z29]),(0,[z0,z1,z2,z3,z4,z1375])],[(0,[z445,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z771,z3,z4]),(0,[z1376,z1,z2,z3,z4,z7]),(0,[z0,z1,z3,z4,z686,z41])],[(0,[z162,z0,z154,z2,z3,z4]),(0,[z207,z42,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1377,z7]),(0,[z0,z1,z2,z3,z4,z1378]),(0,[z0,z1,z151,z3,z26,z10])],[(0,[z0,z1,z2,z3,z4,z1379]),(0,[z0,z1,z2,z1380,z3,z4]),(0,[z0,z1,z2,z715,z4,z7])],[(0,[z42,z0,z1,z438,z3,z4])],[(0,[z0,z1,z134,z3,z4,z29])],[(0,[z0,z1,z2,z1381,z3,z4]),(0,[z0,z1,z2,z3,z18,z610])],[(0,[z0,z1,z2,z3,z4,z1382]),(0,[z0,z1,z2,z938,z4,z7]),(0,[z0,z20,z2,z3,z21,z173]),(0,[z162,z1,z2,z3,z4,z472])],[(0,[z0,z52,z1,z307,z3,z4]),(0,[z44,z1,z2,z3,z4,z702]),(0,[z143,z0,z87,z3,z4,z10])],[(0,[z0,z1,z2,z3,z4,z1383]),(0,[z0,z20,z1,z307,z3,z4])],[(0,[z0,z1,z2,z3,z15,z403])],[(0,[z207,z1,z2,z272,z3,z4]),(0,[z0,z2,z3,z1384,z4,z7]),(0,[z0,z1,z166,z3,z4,z439]),(0,[z0,z1,z2,z3,z4,z1385]),(0,[z32,z1,z2,z280,z74,z7]),(0,[z16,z0,z1,z2,z230,z4]),(0,[z0,z1,z2,z1386,z3,z4]),(0,[z0,z352,z2,z3,z172,z256]),(0,[z0,z20,z2,z3,z21,z10]),(0,[z0,z1,z2,z3,z4,z1387]),(0,[z0,z1,z420,z3,z4,z41])],[(0,[z42,z0,z1,z2,z3,z4]),(0,[z44,z0,z1,z2,z280,z3]),(0,[z0,z1,z2,z194,z3,z4]),(0,[z0,z1388,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1389])],[(0,[z0,z34,z2,z35,z4,z10])],[(0,[z0,z1,z2,z3,z1390,z7]),(0,[z219,z1,z2,z229,z69,z7]),(0,[z44,z0,z58,z2,z45,z4]),(0,[z0,z1,z2,z3,z4,z1391]),(0,[z0,z1,z2,z745,z3,z7]),(0,[z0,z52,z103,z3,z4,z25])]],
   [[(0,[z162,z71,z1,z2,z3,z4]),(0,[z44,z156,z157,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1392]),(0,[z16,z0,z1,z2,z3,z1393]),(0,[z0,z1,z151,z307,z3,z4]),(0,[z0,z1,z706,z3,z4,z41]),(0,[z0,z1,z2,z128,z788,z7])],[(0,[z0,z1,z324,z453,z4,z7]),(0,[z0,z1,z2,z3,z4,z1394]),(0,[z32,z1,z2,z80,z74,z4]),(0,[z1,z2,z3,z4,z813,z46]),(0,[z0,z1,z2,z3,z4,z1395])],[(0,[z207,z1,z2,z3,z4,z46]),(0,[z0,z52,z103,z3,z4,z7]),(0,[z0,z2,z767,z3,z4,z7]),(0,[z0,z1,z2,z491,z4,z25]),(0,[z0,z1,z3,z4,z1396,z25])],[(0,[z0,z1,z1397,z3,z4,z7]),(0,[z156,z0,z154,z2,z3,z4]),(0,[z50,z0,z1,z307,z3,z4])],[(0,[z0,z1,z2,z3,z1398,z7]),(0,[z0,z1,z2,z3,z375,z89]),(0,[z1399,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z4,z310,z29])],[(0,[z0,z1,z2,z3,z4,z1400]),(0,[z0,z1,z2,z3,z4,z1401]),(0,[z0,z1,z2,z491,z4,z7])],[(0,[z242,z1,z272,z3,z4,z41]),(0,[z243,z1,z2,z3,z4,z610]),(0,[z1402,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z23,z4,z661])],[(0,[z0,z1,z1403,z2,z4,z7]),(0,[z0,z1,z2,z3,z360,z25]),(0,[z248,z1,z2,z33,z4,z350]),(0,[z0,z1,z2,z3,z1404,z7]),(0,[z0,z767,z87,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1405]),(0,[z0,z1,z2,z3,z624,z479])],[(0,[z0,z1,z2,z3,z1406,z7]),(0,[z0,z1,z1178,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1407]),(0,[z44,z0,z1,z11,z12,z4]),(0,[z0,z1,z2,z59,z4,z183]),(0,[z0,z34,z2,z35,z4,z233])],[(0,[z1408,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1409]),(0,[z0,z1,z2,z3,z1410,z7])],[(0,[z0,z1,z2,z3,z501,z41]),(0,[z0,z1,z2,z3,z4,z1411])],[(0,[z16,z64,z1,z166,z3,z4]),(0,[z0,z1,z2,z1412,z4,z7]),(0,[z0,z1,z11,z3,z4,z439])],[(0,[z0,z1,z2,z3,z1393,z7]),(0,[z0,z1,z2,z3,z4,z509])],[(0,[z242,z61,z1,z2,z3,z4]),(0,[z0,z1,z2,z280,z3,z41]),(0,[z44,z0,z1,z2,z3,z275]),(0,[z0,z352,z2,z3,z761,z7]),(0,[z0,z1,z2,z120,z4,z115]),(0,[z1413,z0,z1,z2,z3,z4])],[(0,[z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z138,z304]),(0,[z0,z1,z2,z1414,z3,z4]),(0,[z0,z1,z2,z3,z1415,z7]),(0,[z16,z0,z1,z995,z3,z4]),(0,[z0,z1,z307,z3,z21,z4]),(0,[z0,z1,z2,z105,z76,z25])],[(0,[z0,z1,z443,z3,z4,z304]),(0,[z0,z1,z1416,z2,z3,z4]),(0,[z90,z0,z1,z2,z3,z361])]],
   [[(0,[z0,z1,z2,z3,z4,z1417]),(0,[z44,z637,z1,z2,z3,z4]),(0,[z1256,z243,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1418])],[(0,[z0,z1,z2,z3,z4,z1419]),(0,[z0,z58,z2,z45,z4,z84]),(0,[z0,z1,z2,z128,z22,z10]),(0,[z0,z1,z2,z105,z76,z7])],[(0,[z0,z1,z2,z3,z4,z1420]),(0,[z0,z1,z2,z1300,z3,z4]),(0,[z637,z1,z2,z3,z4,z25]),(0,[z0,z1,z3,z4,z731,z41]),(0,[z0,z1,z3,z4,z354,z29])],[(0,[z0,z1,z1421,z3,z4,z7])],[(0,[z0,z1,z2,z3,z4,z1422]),(0,[z0,z1,z2,z3,z275,z610]),(0,[z0,z1,z2,z3,z4,z1423])],[(0,[z637,z1,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1424]),(0,[z0,z1,z307,z3,z74,z4]),(0,[z0,z1,z2,z229,z172,z7]),(0,[z16,z0,z1,z2,z105,z76]),(1,[z1,z2,z3,z4,z813])],[(0,[z165,z55,z2,z3,z4,z25]),(0,[z0,z1,z2,z3,z1425,z7]),(0,[z0,z1,z2,z3,z57,z29]),(0,[z0,z1,z2,z3,z4,z1426]),(0,[z0,z2,z938,z35,z4,z7]),(0,[z0,z1,z2,z3,z4,z1427]),(0,[z0,z1,z2,z528,z4,z371]),(0,[z0,z1,z2,z3,z4,z225]),(0,[z0,z1,z2,z4,z752,z183]),(0,[z0,z1,z2,z3,z24,z952])],[(0,[z165,z0,z119,z2,z3,z4]),(1,[z207,z1,z272,z3,z4]),(0,[z1428,z1,z2,z3,z4,z7]),(0,[z0,z58,z2,z45,z4,z10]),(0,[z0,z1,z2,z491,z172,z7]),(0,[z0,z2,z3,z4,z10,z631])],[(0,[z0,z1,z2,z3,z4,z1429]),(0,[z0,z1,z2,z3,z4,z1430]),(1,[z1,z2,z762,z4,z7]),(0,[z1431,z0,z1,z2,z3,z4])],[(0,[z165,z55,z2,z3,z4,z7]),(0,[z0,z1,z2,z1432,z3,z4]),(0,[z44,z0,z1,z151,z3,z26]),(0,[z143,z0,z87,z3,z4,z610]),(0,[z0,z1,z2,z3,z15,z387])],[(0,[z32,z0,z1,z2,z399,z7]),(0,[z0,z1,z2,z556,z69,z7]),(0,[z1433,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z18,z10]),(0,[z1434,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z120,z4,z173])],[],[(0,[z0,z1,z2,z556,z4,z25]),(0,[z0,z1,z848,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z266]),(0,[z0,z1,z2,z1227,z4,z41])],[(0,[z32,z1,z2,z426,z74,z4]),(0,[z0,z1,z2,z1435,z3,z4]),(0,[z0,z154,z2,z3,z4,z172]),(0,[z0,z1,z1436,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1437])],[(0,[z0,z1,z2,z1438,z3,z4]),(0,[z0,z1,z2,z399,z3,z41])],[(0,[z0,z1,z2,z556,z4,z7]),(0,[z0,z1,z2,z212,z4,z39]),(0,[z0,z1,z2,z31,z4,z752])]],
   [[(0,[z0,z1,z2,z528,z4,z183]),(0,[z0,z1,z2,z116,z4,z208])],[(0,[z51,z1,z2,z3,z892,z7]),(0,[z162,z0,z1,z307,z3,z4]),(0,[z1439,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z453,z4,z41]),(0,[z156,z157,z2,z3,z4,z25]),(0,[z0,z1298,z2,z3,z4,z7]),(0,[z143,z0,z767,z3,z4,z7]),(0,[z0,z1,z1440,z2,z3,z4])],[(0,[z0,z1,z2,z1441,z4,z7]),(0,[z1,z55,z272,z3,z4,z41]),(0,[z51,z1,z2,z3,z86,z25]),(0,[z44,z0,z1,z2,z975,z4])],[(0,[z0,z1,z2,z3,z4,z1442]),(0,[z0,z2,z547,z3,z4,z25])],[(0,[z156,z157,z2,z3,z4,z7]),(0,[z0,z52,z103,z3,z4,z53]),(0,[z1443,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z146,z4,z265]),(0,[z0,z1,z2,z3,z4,z1444]),(0,[z587,z1,z2,z3,z69,z7]),(0,[z0,z1,z2,z1445,z3,z4])],[(0,[z0,z1,z2,z3,z131,z25]),(0,[z0,z1,z3,z26,z738,z7])],[(0,[z242,z0,z1,z70,z3,z4]),(0,[z0,z1,z2,z4,z7,z1446]),(0,[z0,z1,z2,z3,z4,z1447]),(0,[z0,z1,z2,z3,z4,z1448]),(0,[z0,z1,z209,z3,z4,z29])],[(0,[z42,z0,z1,z2,z737,z4]),(0,[z0,z1,z2,z1449,z3,z7]),(0,[z0,z1,z2,z3,z4,z1450]),(0,[z0,z1,z2,z1361,z3,z41]),(0,[z0,z1,z2,z212,z4,z190])],[(0,[z107,z0,z1,z3,z4,z344]),(0,[z0,z1,z2,z3,z1451,z4]),(0,[z0,z1,z2,z3,z4,z1452]),(0,[z0,z1,z1453,z2,z3,z4])],[(0,[z1,z166,z833,z3,z4,z7]),(0,[z0,z352,z2,z3,z172,z25])],[(0,[z0,z1,z2,z1454,z3,z4]),(0,[z42,z0,z1,z2,z3,z785])],[(0,[z0,z1,z2,z453,z138,z7]),(0,[z0,z1,z2,z1455,z3,z7]),(0,[z0,z1,z103,z70,z3,z4]),(0,[z0,z1,z2,z244,z4,z10]),(0,[z1456,z1,z2,z3,z4,z7])],[(0,[z0,z1,z443,z453,z4,z7]),(0,[z0,z1,z284,z3,z4,z41]),(0,[z0,z1,z2,z212,z394,z4]),(0,[z0,z352,z2,z3,z172,z7])],[(0,[z445,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1457]),(0,[z0,z1,z307,z3,z4,z465]),(0,[z0,z1,z307,z3,z12,z4]),(0,[z0,z1,z307,z3,z4,z190]),(0,[z0,z1,z2,z1458,z4,z7]),(0,[z723,z1,z2,z3,z4,z7])]],
   [[(0,[z0,z1,z2,z3,z4,z1459]),(0,[z0,z1,z2,z3,z4,z1460]),(0,[z16,z0,z1,z11,z12,z4]),(0,[z0,z1,z224,z896,z4,z7])],[(0,[z0,z1,z2,z1461,z4,z7]),(0,[z156,z0,z1,z307,z3,z4]),(0,[z0,z1,z2,z3,z4,z1462]),(0,[z0,z34,z2,z938,z4,z7]),(0,[z83,z0,z1,z3,z4,z150]),(0,[z0,z596,z2,z3,z4,z25])],[(0,[z143,z44,z0,z87,z3,z4]),(0,[z243,z1,z2,z3,z275,z7])],[(0,[z165,z44,z55,z2,z3,z4]),(0,[z0,z1,z2,z399,z556,z7]),(0,[z0,z1,z2,z3,z4,z1463]),(0,[z219,z1,z2,z132,z3,z7]),(0,[z0,z1,z2,z3,z4,z1464])],[(0,[z0,z1,z2,z1465,z3,z4]),(0,[z0,z2,z3,z4,z815,z7]),(0,[z0,z1,z2,z3,z4,z1466])],[(0,[z1,z2,z762,z3,z4,z7]),(0,[z51,z0,z1,z307,z3,z4]),(0,[z16,z0,z1,z2,z3,z275]),(0,[z44,z0,z1,z1286,z3,z4]),(0,[z0,z1,z2,z3,z4,z1467]),(1,[z0,z2,z938,z4,z7]),(0,[z0,z20,z2,z3,z21,z29]),(0,[z0,z1,z2,z342,z4,z39]),(0,[z1468,z0,z1,z2,z3,z4])],[(0,[z0,z1,z324,z3,z4,z1420]),(0,[z165,z55,z2,z3,z473,z7]),(0,[z0,z1,z2,z3,z4,z1469]),(0,[z44,z0,z1,z2,z3,z953]),(0,[z0,z1,z2,z1470,z3,z4]),(0,[z0,z1,z2,z128,z191,z22]),(0,[z0,z1,z2,z31,z4,z183]),(0,[z0,z1,z2,z3,z7,z952])],[(0,[z0,z1,z307,z3,z1471,z4]),(0,[z0,z1,z1472,z2,z3,z4]),(0,[z0,z1,z2,z3,z275,z10]),(0,[z0,z1,z2,z3,z4,z1473]),(0,[z0,z34,z2,z35,z4,z29])],[(0,[z165,z864,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1474]),(0,[z1475,z0,z1,z2,z3,z4]),(0,[z0,z1,z3,z692,z4,z41]),(0,[z0,z1,z2,z3,z4,z1476]),(0,[z0,z1,z2,z3,z4,z1477])],[(0,[z16,z321,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1478])],[(0,[z445,z540,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1479]),(0,[z42,z0,z1,z307,z3,z4]),(0,[z44,z0,z1,z2,z737,z4]),(0,[z0,z1,z767,z3,z4,z7]),(0,[z0,z1,z2,z783,z4,z7]),(0,[z0,z1,z2,z3,z262,z121]),(0,[z0,z1,z1480,z2,z3,z4])],[(0,[z0,z1,z2,z556,z86,z7]),(0,[z0,z1,z2,z3,z4,z1481])],[(0,[z0,z1,z2,z1482,z3,z4]),(0,[z1483,z0,z1,z2,z3,z4]),(0,[z44,z450,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1484,z7]),(0,[z0,z1,z2,z3,z4,z1485])],[(0,[z165,z55,z324,z3,z4,z7]),(0,[z0,z1,z2,z453,z473,z7]),(0,[z32,z1,z2,z132,z4,z7]),(0,[z0,z1,z2,z3,z4,z1486]),(0,[z0,z1,z2,z4,z41,z1057]),(0,[z1487,z0,z1,z2,z3,z4])],[(0,[z135,z156,z157,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1488]),(0,[z64,z0,z1,z70,z3,z4]),(0,[z0,z1,z2,z3,z785,z7]),(0,[z0,z1,z2,z3,z4,z1489]),(0,[z0,z1,z2,z178,z4,z610]),(0,[z0,z1,z2,z3,z4,z1490]),(0,[z0,z1,z2,z3,z4,z38]),(0,[z0,z1,z1491,z3,z4,z7])],[(0,[z0,z1492,z2,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z1493])]],
   [[(0,[z0,z1,z2,z3,z1066,z7]),(0,[z0,z1,z2,z1494,z3,z4]),(0,[z0,z1,z1495,z307,z3,z4]),(0,[z16,z0,z1,z1100,z3,z4]),(0,[z1496,z0,z1,z2,z3,z4]),(0,[z1497,z0,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z67]),(0,[z0,z52,z103,z3,z4,z396])],[(0,[z0,z1,z1498,z2,z3,z4]),(0,[z0,z2,z3,z4,z599,z25]),(0,[z1499,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z14,z3,z542])],[(0,[z0,z1,z2,z1500,z3,z7]),(0,[z1,z574,z272,z3,z4,z7]),(0,[z16,z219,z1,z2,z3,z69]),(0,[z0,z1,z750,z307,z3,z4]),(0,[z0,z1,z307,z3,z4,z25]),(0,[z0,z1,z2,z1501,z4,z7])],[(0,[z0,z1,z1502,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z79]),(0,[z0,z2,z3,z938,z4,z7]),(0,[z0,z1,z2,z745,z3,z41]),(0,[z0,z1,z424,z3,z4,z29]),(0,[z0,z1,z2,z4,z190,z752])],[(0,[z1503,z0,z1,z2,z3,z4]),(0,[z242,z1,z272,z3,z4,z10]),(0,[z0,z1,z2,z4,z7,z1504]),(0,[z0,z1,z2,z3,z4,z1505]),(0,[z143,z0,z87,z3,z275,z7])],[(0,[z0,z1,z1359,z3,z4,z7]),(0,[z0,z1,z307,z3,z4,z7]),(0,[z44,z0,z1,z224,z158,z4]),(0,[z0,z1,z2,z14,z3,z214])],[(0,[z61,z1,z55,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1506]),(0,[z0,z1,z2,z876,z4,z7]),(0,[z0,z52,z103,z3,z4,z41]),(0,[z1507,z0,z1,z2,z3,z4])],[(0,[z0,z1,z119,z2,z3,z4]),(0,[z0,z1,z2,z229,z4,z41]),(0,[z0,z1,z2,z3,z4,z1508]),(0,[z0,z1,z3,z4,z1396,z7]),(1,[z0,z1,z2,z4,z752]),(0,[z0,z1,z2,z14,z3,z952])],[(0,[z0,z1509,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z1510,z7]),(0,[z540,z1,z2,z272,z3,z4]),(0,[z0,z1,z2,z491,z4,z41]),(0,[z0,z1,z2,z128,z22,z29])],[(0,[z0,z1,z2,z3,z1511,z7]),(0,[z0,z1,z2,z3,z4,z1512]),(0,[z0,z1,z307,z3,z86,z4]),(0,[z1513,z0,z1,z2,z3,z4])],[(0,[z135,z0,z1,z2,z3,z4]),(0,[z0,z1,z102,z2,z3,z4]),(0,[z16,z1,z235,z2,z3,z4]),(0,[z0,z1,z2,z4,z1222,z10]),(0,[z0,z1,z11,z12,z4,z25]),(0,[z42,z1,z2,z3,z4,z68])],[(0,[z0,z1,z2,z3,z360,z7]),(0,[z0,z1,z2,z1514,z3,z4]),(0,[z0,z1,z2,z3,z4,z1515]),(0,[z0,z1,z2,z3,z4,z1516]),(0,[z0,z1,z2,z244,z4,z610]),(0,[z0,z1,z2,z3,z4,z1517]),(0,[z0,z1,z101,z3,z27,z10])],[(0,[z0,z1518,z1,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z1519]),(0,[z1520,z0,z1,z2,z3,z4]),(0,[z1521,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1522]),(0,[z0,z1,z3,z4,z718,z25]),(0,[z0,z1,z11,z12,z4,z7])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 498).take 490) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 988).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1475).take 58) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1533)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [498, 490, 487, 58] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 228).take 121).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 349).take 107).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 456).take 56).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 114, 121, 107, 56] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38693

theorem PEqualNP.Outside.L_meta_38693 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4243122376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4243122376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38693.solve