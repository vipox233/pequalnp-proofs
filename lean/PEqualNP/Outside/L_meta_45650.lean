import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45650

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
  Nat.testBit (4008241384 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x030a161b00d6d6c0#64 ++ 0x080c28586c035b5b#64 ++ 0x471e3e3f11fffffe#64 ++ 0xf91c78f8fc47ffff#64 : BitVec 256),
   (0x1864cac566317141#64 ++ 0x0061932b1598c5c5#64 ++ 0xb8e7cfc7ee31f1f7#64 ++ 0xfee39f3f1fb8c7c7#64 : BitVec 256),
   (0xc0b16368f03a3a02#64 ++ 0x7302c58da3c0e8e8#64 ++ 0xc0f9f3f8f03e3e1b#64 ++ 0x7303e7cfe3c0f8f8#64 : BitVec 256),
   (0xed01fc00bb402d90#64 ++ 0x17b407f002ed00b6#64 ++ 0xff01fc00ffc03fdf#64 ++ 0xbffc07f003ff00ff#64 : BitVec 256),
   (0xf6fe0000ddad8008#64 ++ 0xc3dbf8000376b600#64 ++ 0xfffe0000ffffc023#64 ++ 0xdffff80003ffff00#64 : BitVec 256),
   (0xffdfbdb600000004#64 ++ 0xa7ff7ef6d8000000#64 ++ 0xffffffff00000003#64 ++ 0xe7fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [8, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x020a001a00868200 0x0808280068021a08 0x00180038000e0000 0x00006000e0003800

def z1 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z2 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z3 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z4 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z5 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe0000ffffc023 0xdffff80003ffff00

def z6 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff00000003 0xe7fffffffc000000

def z7 : W := mkw 0xc0b1636060303000 0x2302c58d8180c0c0 0xc0f9f3f8e0303013 0x7303e7cfe380c0c0

def z8 : W := mkw 0x0820cac562307141 0x0020832b1588c1c5 0x80e1cfc7e03031d7 0x7203873f1f80c0c7

def z9 : W := mkw 0x18448a8500105040 0x0061122a14004141 0xb8e7cfc70031f1f7 0xfee39f3f1c00c7c7

def z10 : W := mkw 0xfffffffefdbfba0e 0xf7fffffffbf6fee8 0xfffffffffffffe3b 0xfffffffffffffff8

def z11 : W := mkw 0x030a141a00c68680 0x080c285068031a1a 0x4718303811ce0e08 0x011c60c0e0473838

def z12 : W := mkw 0x126e000044a58000 0x0049b80001129600 0xfffe0000ffffc023 0xdffff80003ffff00

def z13 : W := mkw 0x0800c80022002100 0x0020032000880084 0x0001cc00000031d4 0x20000730000000c7

def z14 : W := mkw 0x1865ebed66337b43 0x306197afb598cded 0xb8e7ffffee31ffff 0xfee39fffffb8c7ff

def z15 : W := mkw 0xc091212000000000 0x2302448480000000 0xc0f9f3f800000003 0x6303e7cfe0000000

def z16 : W := mkw 0xed91fd20bb402d90 0x37b647f482ed00b6 0xfff9fff8ffc03fdf 0xffffe7ffe3ff00ff

def z17 : W := mkw 0x12de01b600000004 0xa04b7806d8000000 0x00fe03ff00000000 0x4003f80ffc000000

def z18 : W := mkw 0xfcd5a9a400000004 0xa7f356a690000000 0xb8e1c1c000000001 0x06e3870700000000

def z19 : W := mkw 0xf7ff3400dded8c98 0xd7dffcd00377b632 0xfffe3000ffffce2b 0xdffff8c003ffff38

def z20 : W := mkw 0x12fe02c544bdd049 0xc04bf80b1512f741 0x00fe03c7003fc020 0x4003f80f1c00ff00

def z21 : W := mkw 0x1945bdb600000004 0x246516f6d8000000 0xb8e7ffff00000003 0xe6e39ffffc000000

def z22 : W := mkw 0x00b16368603a3a02 0x7002c58da180e8e8 0x00f9f3f8003e3e18 0x6003e7cfe000f8f8

def z23 : W := mkw 0x0020424166317141 0x000081090598c5c5 0x00060e07ee31f1f6 0xf80018381fb8c7c7

def z24 : W := mkw 0xfc65e8c4ff212911 0x17f197a313fc84a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z25 : W := mkw 0xffdfbdb6998c800c 0xe7ff7ef6da663200 0xffffffff11ce0003 0xe7fffffffc473800

def z26 : W := mkw 0x00b00368403a1202 0x6002c00da100e848 0x00f803f8003e0000 0x4003e00fe000f800

def z27 : W := mkw 0xedb1ff68fb7a3f92 0x77b6c7fda3ede8fe 0xfff9fff8fffe3fdf 0xffffe7ffe3fff8ff

def z28 : W := mkw 0x00200000ddad8008 0x400080000376b600 0x00000000ffffc020 0x1800000003ffff00

def z29 : W := mkw 0xe400000099000000 0x0390000002640000 0xff000000ffc00003 0x9ffc000003ff0000

def z30 : W := mkw 0xc9b1ff68f27a3f92 0x7726c7fda3c9e8fe 0xc0f9fff8f03e3fdf 0x7303e7ffe3c0f8ff

def z31 : W := mkw 0x0100140000400480 0x0004005000010012 0x4700300011c00e08 0x011c00c000470038

def z32 : W := mkw 0xef9bbd3200000004 0xa7be6ef4c8000000 0xff19fc3800000003 0xa7fc67f0e0000000

def z33 : W := mkw 0x1844888400000000 0x0061122210000000 0xb8e7cfc700000003 0xe6e39f3f1c000000

def z34 : W := mkw 0xfffffff766317145 0xa7ffffffdd98c5c5 0xffffffffee31f1f7 0xffffffffffb8c7c7

def z35 : W := mkw 0xf6de000000000000 0x83db780000000000 0xfffe000000000003 0xc7fff80000000000

def z36 : W := mkw 0xffffbdb6ddad800c 0xe7fffef6db76b600 0xffffffffffffc023 0xffffffffffffff00

def z37 : W := mkw 0x3f4e9c960d85800c 0x84fd3a7258361600 0x3f060c070fc1c020 0x8cfc18301c3f0700

def z38 : W := mkw 0xed01fe08bb523f90 0x17b407f822ed48fe 0xff19fe38fffe3fdf 0xfffc67f8e3fff8ff

def z39 : W := mkw 0x00204040f0282802 0x5000810103c0a0a0 0x00000000e0000000 0x0000000003800000

def z40 : W := mkw 0xe4200000ddad8008 0x439080000376b600 0xff000000ffffc023 0x9ffc000003ffff00

def z41 : W := mkw 0x0100140000400480 0x0004005000010012 0x47003c0011c03fde 0xb91c00f0004700ff

def z42 : W := mkw 0xec01e800bb002910 0x17b007a002ec00a4 0xb801c000ee000001 0x06e0070003b80000

def z43 : W := mkw 0x020a021b0096d240 0x080828086c025b49 0x001e023f003fc020 0x40007808fc00ff00

def z44 : W := mkw 0x0020424166317141 0x000081090598c5c5 0x00000000ee31f1f4 0x1800000003b8c7c7

def z45 : W := mkw 0x030a141200000000 0x000c285048000000 0x471e3e3f00000002 0xe11c78f8fc000000

def z46 : W := mkw 0x0801ebed22127b43 0x302007afb48849ed 0x0001ffff00003fdc 0x200007fffc0000ff

def z47 : W := mkw 0xfefecac5ffbdf149 0xc3fbfb2b17fef7c5 0xffffcfc7fffff1f7 0xffffff3f1fffffc7

def z48 : W := mkw 0x1b6ededf66f7f7c1 0x086dbb7b7d9bdfdf 0xffffffffffffffff 0xffffffffffffffff

def z49 : W := mkw 0xd8f5ebedf63b7b43 0x7363d7afb7d8eded 0xf8fffffffe3fffff 0xffe3fffffff8ffff

def z50 : W := mkw 0x1864c8c466212101 0x0061932311988484 0xb8e1c1c0ee000001 0x06e3870703b80000

def z51 : W := mkw 0x0021636860323a02 0x3000858da180c8e8 0x80e1f3f8e0303e1b 0x720387cfe380c0f8

def z52 : W := mkw 0xf64e00009d858008 0x83d9380002761600 0xff060000ffc1c023 0x9ffc180003ff0700

def z53 : W := mkw 0xe4b16368f93a3a02 0x7392c58da3e4e8e8 0xfff9f3f8fffe3e1b 0xffffe7cfe3fff8f8

def z54 : W := mkw 0xf6fe0201ddbdd048 0xc3dbf8080776f741 0xfffe0e07fffff1f7 0xfffff8381fffffc7

def z55 : W := mkw 0xc0912128900a0a02 0x73024484a2402828 0x40183038100e0e08 0x010060c0e0403838

def z56 : W := mkw 0xc3bb777bf0fefec2 0x7b0eedddefc3fbfb 0xc7fffffff1ffffff 0xfb1fffffffc7ffff

def z57 : W := mkw 0xd8d5a9a400000000 0x236356a690000000 0xf8ffffff00000003 0xe7e3fffffc000000

def z58 : W := mkw 0x1064000044210000 0x0041900001108400 0xb8e60000ee31c023 0xdee3980003b8c700

def z59 : W := mkw 0xd8f5ebe566317141 0x2363d7af9598c5c5 0xf8ffffffee31f1f7 0xffe3ffffffb8c7c7

def z60 : W := mkw 0x106400c444210001 0x0041900311108400 0x00e001c000000000 0x0003800700000000

def z61 : W := mkw 0x2d009c000b400590 0x04b40270002d0016 0x3f000c000fc001c4 0x8cfc0030003f0007

def z62 : W := mkw 0xc0016000b0002800 0x1300058002c000a0 0xc001f000f0003e1b 0x330007c003c000f8

def z63 : W := mkw 0x0901fc0022402d90 0x142407f0008900b6 0x0001fc0000003fdc 0x200007f0000000ff

def z64 : W := mkw 0x12fe000044ad8008 0xc04bf8000112b600 0x00fe0000003fc020 0x4003f8000000ff00

def z65 : W := mkw 0x1844888506014141 0x0061122214180505 0x38060c070e01c1e4 0x8ce018301c380707

def z66 : W := mkw 0xf6de0000998c8008 0xc3db780002663200 0xfffe000011ce0003 0xc7fff80000473800

def z67 : W := mkw 0xf6fe01b6ddad800c 0xe3dbf806db76b600 0xfffe03ffffffc023 0xdffff80fffffff00

def z68 : W := mkw 0x1844888406010101 0x0061122210180404 0x380000000e000000 0x04e0000000380000

def z69 : W := mkw 0xfefec8c4ffada109 0xc3fbfb2313feb684 0xffffc1c0ffffc023 0xdfffff0703ffff00

def z70 : W := mkw 0x0901fe1b22527fd0 0x1c2407f86c8949ff 0x0001fe3f00003fdc 0x200007f8fc0000ff

def z71 : W := mkw 0x1864c8c566216141 0x0061932315988585 0xb8e7cdc7ee01c1e5 0x8ee39f371fb80707

def z72 : W := mkw 0x030a141300c4c4c0 0x080c28504c031313 0x07060c0701c1c1e4 0x881c18301c070707

def z73 : W := mkw 0xed01bc0000400480 0x07b406f000010012 0xff01fc0011c03fdf 0xbffc07f0004700ff

def z74 : W := mkw 0xd0f56368f43b3a02 0x7343d58da3d0ece8 0xf8fff3f8fe3ffe3b 0xffe3ffcfe3f8fff8

def z75 : W := mkw 0x1bdfbdb600000004 0xa46f7ef6d8000000 0x00ffffff00000000 0x6003fffffc000000

def z76 : W := mkw 0x0000020100105040 0x0000000804004141 0x00060e070031f1f6 0xf80018381c00c7c7

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060e0700000002 0xe00018381c000000

def z78 : W := mkw 0x0900dc0022402580 0x0024037000890096 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z79 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x471e323f11ffce28 0x411c78c8fc47ff38

def z80 : W := mkw 0xfffffffefb7a3f96 0xf7fffffffbede8fe 0xfffffffffffe3fdf 0xfffffffffffff8ff

def z81 : W := mkw 0x13de15b600000004 0xa04f7856d8000000 0x47fe3fff00000002 0xe11ff8fffc000000

def z82 : W := mkw 0x020a000000848000 0x0008280000021200 0x471e000011ffc022 0xd91c78000047ff00

def z83 : W := mkw 0xedb1fc00fb682d90 0x57b6c7f003eda0b6 0xfff9fc00fffe3fdf 0xffffe7f003fff8ff

def z84 : W := mkw 0xef0bfe1bbbd6ffd0 0x1fbc2ff86eef5bff 0xff1ffe3fffffffff 0xfffc7ff8ffffffff

def z85 : W := mkw 0x0801e80022002910 0x142007a0008800a4 0x0001c00000000000 0x0000070000000000

def z86 : W := mkw 0xe501340099400c90 0x179404d002650032 0x4700300011c00e08 0x011c00c000470038

def z87 : W := mkw 0xfd65fec5ff717dd1 0x17f597fb17fdc5f7 0xffe7ffc7fff1ffff 0xffff9fff1fffc7ff

def z88 : W := mkw 0x00204248f03a3a02 0x5000810923c0e8e8 0x00000000f03e3e18 0x1000000003c0f8f8

def z89 : W := mkw 0x3f4e9c9600000004 0x84fd3a7258000000 0x3f060c0700000000 0x84fc18301c000000

def z90 : W := mkw 0xfcf5a9a4dd29000c 0xe7f3d6a69374a400 0xb8e1c1c0ee000001 0x06e3870703b80000

def z91 : W := mkw 0x0000020900d6d6c0 0x0800000824035b5b 0x0000000011fffffc 0x180000000047ffff

def z92 : W := mkw 0x136e161b44f7d6c0 0x084db8586d13df5b 0xfffe3e3fffffffff 0xfffff8f8ffffffff

def z93 : W := mkw 0x032a161bddffd6c8 0x480ca8586f77ff5b 0x471e3e3ffffffffe 0xf91c78f8ffffffff

def z94 : W := mkw 0xfcf5ebecf03a3a06 0xf7f3d7afb3c0e8e8 0xf8f9f3f8f03e3e1b 0x77e3e7cfe3c0f8f8

def z95 : W := mkw 0x1864cacdf63b7b43 0x5061932b37d8eded 0xb8e7cfc7fe3fffff 0xfee39f3f1ff8ffff

def z96 : W := mkw 0xe4004000bb402d90 0x1390010002ed00b6 0xff000000ffc03fdf 0x9ffc000003ff00ff

def z97 : W := mkw 0x1864cacd66f7f7c1 0x0861932b359bdfdf 0xb8e7cfc7ffffffff 0xfee39f3f1fffffff

def z98 : W := mkw 0x00204248f03a3a02 0x5000810923c0e8e8 0x40183238f03e3e1a 0x710060c8e3c0f8f8

def z99 : W := mkw 0xed21fe40fb703d90 0x17b487f903edc0f6 0xffe1ffc0fff03fdf 0xffff87ff03ffc0ff

def z100 : W := mkw 0x106402c544315041 0x0041900b1510c541 0x00e603c70031c020 0x4003980f1c00c700

def z101 : W := mkw 0x020a00130084c040 0x080828004c021301 0x000600070001c020 0x000018001c000700

def z102 : W := mkw 0xed01fec5bb507dd1 0x17b407fb16ed41f7 0xff01ffc7ffc03fdf 0xbffc07ff1fff00ff

def z103 : W := mkw 0x00200248403a1202 0x400080092100e848 0x00000000003e0000 0x000000000000f800

def z104 : W := mkw 0xc0216248f03a3a02 0x5300858923c0e8e8 0xc001f000f03e3e1b 0x330007c003c0f8f8

def z105 : W := mkw 0x0820ca4062303100 0x002083290188c0c4 0xb8e1cfc0ee3031d7 0xfee3873f03b8c0c7

def z106 : W := mkw 0x000000000d858008 0x0000000000361600 0x000000000fc1c020 0x08000000003f0700

def z107 : W := mkw 0x0000400022002100 0x0000010000880084 0x00000000ee0031d4 0x1800000003b800c7

def z108 : W := mkw 0x12de000000000000 0x804b780000000000 0x00fe000000000000 0x4003f80000000000

def z109 : W := mkw 0xedb1ff68f03a3a02 0x77b6c7fda3c0e8e8 0xfff9fff8f03e3e1b 0xf7ffe7ffe3c0f8f8

def z110 : W := mkw 0x1b4e9c9600000000 0x006d3a7258000000 0xffffffff00000003 0xe7fffffffc000000

def z111 : W := mkw 0x1b6eded766f5f5c1 0x086dbb7b5d9bd7d7 0xbfe7cfc7eff1f1f7 0xfeff9f3f1fbfc7c7

def z112 : W := mkw 0xff4fbc9600000004 0x87fd3ef258000000 0xff07fc0700000003 0xa7fc1ff01c000000

def z113 : W := mkw 0xffdffdb6bb402d94 0xb7ff7ff6daed00b6 0xffffffffffc03fdf 0xffffffffffff00ff

def z114 : W := mkw 0x0800cac522107141 0x0020032b148841c5 0x0001cfc7000031d4 0x2000073f1c0000c7

def z115 : W := mkw 0x0800cac522107141 0x0020032b148841c5 0xb801cfc7ee0031d7 0xbee0073f1fb800c7

def z116 : W := mkw 0x1844c88422002100 0x0061132210880084 0xb8e7cfc7ee0031d7 0xfee39f3f1fb800c7

def z117 : W := mkw 0xe501340099400c90 0x179404d002650032 0xff003000ffc00e0b 0x9ffc00c003ff0038

def z118 : W := mkw 0xed01bc0000000000 0x07b406f000000000 0xff01fc0000000003 0xa7fc07f000000000

def z119 : W := mkw 0xfcf4cac5ff397149 0xc3f3d32b17fce5c5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z120 : W := mkw 0xfd45bc8400000000 0x07f516f210000000 0xffe7ffc700000003 0xe7ff9fff1c000000

def z121 : W := mkw 0x00204248fb7a3f92 0x5000810923ede8fe 0x00000000fffe3fdc 0x1800000003fff8ff

def z122 : W := mkw 0xc090000000000000 0x0302400000000000 0xc0f8000000000003 0x4303e00000000000

def z123 : W := mkw 0xffdffc00bb402d90 0x97ff7ff002ed00b6 0xfffffc00ffc03fdf 0xfffffff003ff00ff

def z124 : W := mkw 0xd0f563edf43b7a43 0x7343d58fb7d0ede9 0xc0fff3fff03ffe3b 0x7303ffcfffc0fff8

def z125 : W := mkw 0xef0bfc13bbc4edd0 0x1fbc2ff04eef13b7 0xff07fc07ffc1ffff 0xbffc1ff01fff07ff

def z126 : W := mkw 0xffdfbdb600400484 0xa7ff7ef6d8010012 0xffffffff11c03fdf 0xfffffffffc4700ff

def z127 : W := mkw 0xf4f40000ddad8008 0xc3d3d0000376b600 0xb8e00000ffffc021 0x1ee3800003ffff00

def z128 : W := mkw 0x1b4e9e9f06d7d7c1 0x086d3a7a7c1b5f5f 0x7f1e3e3f1ffffffe 0xfdfc78f8fc7fffff

def z129 : W := mkw 0x0000400022402d90 0x10000100008900b6 0x0000000000003fdc 0x00000000000000ff

def z130 : W := mkw 0x0000020800121200 0x0000000820004848 0x0000323800003e18 0x200000c8e00000f8

def z131 : W := mkw 0x1b4e9c9706c5c5c1 0x086d3a725c1b1717 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z132 : W := mkw 0x0000020800121200 0x0000000820004848 0x40183238103e3e1a 0x710060c8e040f8f8

def z133 : W := mkw 0xc0b16160f0282802 0x7302c58583c0a0a0 0x80e1c1c0e0000001 0x0203870703800000

def z134 : W := mkw 0x3c44888400000004 0x84f1122210000000 0x3800000000000000 0x04e0000000000000

def z135 : W := mkw 0xffdfbfbf0096d244 0xafff7efefc025b49 0xffffffff003fc023 0xe7fffffffc00ff00

def z136 : W := mkw 0xc0b00208d03a1200 0x4302c0082340e848 0xc0f83238f03e3e1b 0x7303e0c8e3c0f8f8

def z137 : W := mkw 0xc0b16160f0282802 0x7302c58583c0a0a0 0xc0f9c1c0f03e0003 0x5303e70703c0f800

def z138 : W := mkw 0xffdfbfbf00d6d6c4 0xafff7efefc035b5b 0xffffffff11ffffff 0xfffffffffc47ffff

def z139 : W := mkw 0x0101340000400c90 0x140404d000010032 0x0000300000000e08 0x000000c000000038

def z140 : W := mkw 0x030a141300c4c4c0 0x080c28504c031313 0x471e3e3f01c1c1e6 0xe91c78f8fc070707

def z141 : W := mkw 0x020a021b0096d240 0x080828086c025b49 0x401e323f103ffe3a 0x710078c8fc40fff8

def z142 : W := mkw 0x2d01fc002b402d90 0x14b407f000ad00b6 0x3f01fc000fc03fdc 0xacfc07f0003f00ff

def z143 : W := mkw 0xfffffffef03a3a06 0xf7fffffffbc0e8e8 0xfffffffff03e3e1b 0xf7ffffffffc0f8f8

def z144 : W := mkw 0xfffffc00ffedad98 0xd7fffff003ffb6b6 0xfffffc00ffffffff 0xfffffff003ffffff

def z145 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xbf01cc00efc001c5 0x8efc073003bf0007

def z146 : W := mkw 0xfd45fc85bf416dd1 0x17f517f216fd05b7 0xff07fc07ffc1ffff 0xbffc1ff01fff07ff

def z147 : W := mkw 0xe400000099000000 0x0390000002640000 0xb8000000ee000001 0x06e0000003b80000

def z148 : W := mkw 0xc001200090000800 0x1300048002400020 0x4000300010000e08 0x010000c000400038

def z149 : W := mkw 0xed01fc0022402d90 0x17b407f0008900b6 0xff01fc0000003fdf 0xa7fc07f0000000ff

def z150 : W := mkw 0xed01fe1bbb527fd0 0x1fb407f86eed49ff 0xff01fe3fffc03fdf 0xbffc07f8ffff00ff

def z151 : W := mkw 0xffdfbfbf005256c4 0xafff7efefc01495b 0xffffffff00003fdf 0xe7fffffffc0000ff

def z152 : W := mkw 0xfdd5fda4bb402d94 0xb7f757f692ed00b6 0xffe1fdc0ffc03fdf 0xbfff87f703ff00ff

def z153 : W := mkw 0xe79b353a900a0a06 0xf79e6cd4ea402828 0x47183038100e0e08 0x011c60c0e0403838

def z154 : W := mkw 0xed21fe48fb7a3f92 0x57b487f923ede8fe 0xff01fc00fffe3fdf 0xbffc07f003fff8ff

def z155 : W := mkw 0xffdfbfb700105044 0xa7ff7efedc004141 0xffffffff0031f1f7 0xfffffffffc00c7c7

def z156 : W := mkw 0x126e02df44b7d241 0x0849b80b7d12df49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z157 : W := mkw 0x020a001200000000 0x0008280048000000 0x001e023f00000000 0x40007808fc000000

def z158 : W := mkw 0xec01a80000000000 0x07b006a000000000 0xb801c00000000001 0x06e0070000000000

def z159 : W := mkw 0x00204241ffbdf149 0x4000810907fef7c5 0x00000000fffff1f4 0x1800000003ffffc7

def z160 : W := mkw 0xffdfbdb699000004 0xa7ff7ef6da640000 0xffffffffffc00003 0xffffffffffff0000

def z161 : W := mkw 0xfffffec5fffdfdd9 0xd7fffffb17fff7f7 0xffffffc7ffffffff 0xffffffff1fffffff

def z162 : W := mkw 0x029a0000008c8008 0xc00a680000023200 0x00180000000e0000 0x0000600000003800

def z163 : W := mkw 0xe69a0000998c8008 0xc39a680002663200 0x4718000011ce0000 0x011c600000473800

def z164 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x071e0e3f01ffc1e4 0xc81c7838fc07ff07

def z165 : W := mkw 0x020a020800969200 0x0008280820025a48 0x471e323811fffe3a 0xf91c78c8e047fff8

def z166 : W := mkw 0x364e00000d858008 0x80d9380000361600 0x3f0600000fc1c020 0x8cfc1800003f0700

def z167 : W := mkw 0xffdfbdb60d85800c 0xa7ff7ef6d8361600 0xffffffff0fc1c023 0xeffffffffc3f0700

def z168 : W := mkw 0xd2ff6368f4bfba0a 0xf34bfd8da3d2fee8 0xc0fff3f8f03ffe3b 0x7303ffcfe3c0fff8

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x000600000031c022 0xd80018000000c700

def z170 : W := mkw 0xfcd5a9a400000004 0xa7f356a690000000 0xb8e7cfc700000003 0xe6e39f3f1c000000

def z171 : W := mkw 0xef0bbc1200000000 0x07bc2ef048000000 0xff1ffe3f00000003 0xe7fc7ff8fc000000

def z172 : W := mkw 0xc2bb637bf0befa42 0x7b0aed8defc2fbe9 0xc0fff3fff03ffe3b 0x7303ffcfffc0fff8

def z173 : W := mkw 0x0001636820123a02 0x3000058da08048e8 0x0001f3f800003e18 0x200007cfe00000f8

def z174 : W := mkw 0xc0b00000d0280000 0x4302c0000340a000 0xc0f80000f03e0003 0x5303e00003c0f800

def z175 : W := mkw 0x000002090096d240 0x0800000824025b49 0x00000000003fc020 0x000000000000ff00

def z176 : W := mkw 0x0000424122107141 0x00000109048841c5 0x00000000000031d4 0x00000000000000c7

def z177 : W := mkw 0x12fe036844bf920a 0xe04bf80da112fe48 0x00fe03f8003fc020 0x4003f80fe000ff00

def z178 : W := mkw 0xf6de000099000000 0x83db780002640000 0xfffe0000ffc00003 0xdffff80003ff0000

def z179 : W := mkw 0x12fe01b644ad800c 0xe04bf806d912b600 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z180 : W := mkw 0x02ba037b40bed242 0x680ae80ded02fb49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z181 : W := mkw 0xf6fe0000dd290008 0xc3dbf8000374a400 0xfffe0000ee000003 0xc7fff80003b80000

def z182 : W := mkw 0x0000020900125240 0x0000000824004949 0x401e3e3f103ffffe 0xf90078f8fc40ffff

def z183 : W := mkw 0xfcf4c8c4ff292109 0xc3f3d32313fca484 0xb8e1c1c0ee000001 0x06e3870703b80000

def z184 : W := mkw 0x1864888444210000 0x0061922211108400 0xb8e7cfc7ee31c023 0xfee39f3f1fb8c700

def z185 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xbfe7cdc700000001 0x86ff9f371c000000

def z186 : W := mkw 0x10f4000044290008 0xc043d0000110a400 0x00e0000000000000 0x0003800000000000

def z187 : W := mkw 0x374e14130dc5c4c8 0x88dd38504c371713 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z188 : W := mkw 0xfefec800ffada108 0xc3fbfb2003feb684 0xffffcc00fffff1f7 0xffffff3003ffffc7

def z189 : W := mkw 0xc0916128b00a2a02 0x73024584a2c028a8 0xc019f038f00e3e1b 0x330067c0e3c038f8

def z190 : W := mkw 0x1864cac5ff717dd1 0x1061932b17fdc5f7 0xb8e7cfc7fff1ffff 0xfee39f3f1fffc7ff

def z191 : W := mkw 0x0901bdb600000004 0x242406f6d8000000 0x0001ffff00000000 0x200007fffc000000

def z192 : W := mkw 0x3f4e9c9700c4c4c4 0x8cfd3a725c031313 0x3f060c0701c1c1e4 0x8cfc18301c070707

def z193 : W := mkw 0xec01e800bb402d90 0x17b007a002ed00b6 0xb801c000ffc03fdd 0x1ee0070003ff00ff

def z194 : W := mkw 0xd8f5e9e4f6292903 0x7363d7a793d8a4a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z195 : W := mkw 0x00200000d0280000 0x400080000340a000 0x00000000f03e0000 0x1000000003c0f800

def z196 : W := mkw 0xc0b12128d02a0a02 0x7302c484a340a828 0xc0f83038f03e0e0b 0x5303e0c0e3c0f838

def z197 : W := mkw 0x030a161b005256c0 0x080c28586c01495b 0x471e3e3f00003fde 0xe11c78f8fc0000ff

def z198 : W := mkw 0x030a141a00c68680 0x080c285068031a1a 0x47183c3811ce3fde 0xb91c60f0e04738ff

def z199 : W := mkw 0xc39b353200000000 0x230e6cd4c8000000 0xc7ffffff00000003 0xe31ffffffc000000

def z200 : W := mkw 0x366e0000ddad8008 0xc0d9b8000376b600 0x3f060000ffffc020 0x9cfc180003ffff00

def z201 : W := mkw 0x000001b600000004 0x20000006d8000000 0x000003ff00000000 0x0000000ffc000000

def z202 : W := mkw 0xc0016208b0123a00 0x1300058822c048e8 0xc019f238f03e3e1b 0x730067c8e3c0f8f8

def z203 : W := mkw 0xfffe9c96ddad800c 0xc7fffa725b76b600 0xfffe0c07ffffc023 0xdffff8301fffff00

def z204 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018323800000002 0x610060c8e0000000

def z205 : W := mkw 0x0100161b005256c0 0x080400586c01495b 0x00003e3f00003fdc 0x200000f8fc0000ff

def z206 : W := mkw 0x3f4fbdb600000004 0xa4fd3ef6d8000000 0x3f07ffff00000000 0xa4fc1ffffc000000

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x40180000103e0002 0x510060000040f800

def z208 : W := mkw 0xe491212000000004 0xa792448480000000 0x0000000000000000 0x0000000000000000

def z209 : W := mkw 0xfc65eac5ff317951 0x17f197ab17fcc5e5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z210 : W := mkw 0xf4f40000dd290008 0xc3d3d0000374a400 0xb8e00000ee000001 0x06e3800003b80000

def z211 : W := mkw 0xf6de00009d8d8008 0xc3db780002763600 0x7f1e00001fcfc020 0x8dfc7800007f3f00

def z212 : W := mkw 0x00004000bb402d90 0x1000010002ed00b6 0x00000000ffc03fdc 0x1800000003ff00ff

def z213 : W := mkw 0xffdfbdb700c4c4c4 0xafff7ef6dc031313 0xffffffff01c1c1e7 0xeffffffffc070707

def z214 : W := mkw 0xe501340099400c90 0x179404d002650032 0x47003c0011c03fde 0xb91c00f0004700ff

def z215 : W := mkw 0xfeffe800ffada918 0xd7fbffa003feb6a4 0xffffc000ffffc023 0xdfffff0003ffff00

def z216 : W := mkw 0x0000424820123a02 0x10000109208048e8 0x0000000000003e18 0x00000000000000f8

def z217 : W := mkw 0xffdfffbfbbd6ffd4 0xbfff7ffefeef5bff 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x10640000ddad8008 0x404190000376b600 0xb8e60000ffffc023 0xdee3980003ffff00

def z219 : W := mkw 0xd2ff63fef03a3a06 0xf34bfd8ffbc0e8e8 0xc0fff3fff03e3e1b 0x7303ffcfffc0f8f8

def z220 : W := mkw 0xe60a000099848000 0x0398280002661200 0xff1e0000ffffc023 0xdffc780003ffff00

def z221 : W := mkw 0xf7fe161bddffd6c8 0xcbdff8586f77ff5b 0xfffe3e3fffffffff 0xfffff8f8ffffffff

def z222 : W := mkw 0x0000020800121200 0x0000000820004848 0x00180238003e0000 0x40006008e000f800

def z223 : W := mkw 0x0901bfbf005256c4 0x2c2406fefc01495b 0x0001ffff00003fdc 0x200007fffc0000ff

def z224 : W := mkw 0x00900128000a0202 0x60024004a0002808 0x00180038000e0000 0x00006000e0003800

def z225 : W := mkw 0xd865eac5f6317941 0x136197ab17d8c5e5 0xf8e7ffc7fe31ffff 0xffe39fff1ff8c7ff

def z226 : W := mkw 0x00b0000040280000 0x4002c0000100a000 0x00f80000003e0000 0x4003e0000000f800

def z227 : W := mkw 0xffffbdb6dd29000c 0xe7fffef6db74a400 0xffffffffee000003 0xe7ffffffffb80000

def z228 : W := mkw 0xfffffffff63b7b47 0xf7ffffffffd8eded 0xfffffffffe3fffff 0xfffffffffff8ffff

def z229 : W := mkw 0x000000000b400590 0x00000000002d0016 0x000000000fc001c4 0x08000000003f0007

def z230 : W := mkw 0x364e000000000000 0x80d9380000000000 0x3f06000000000000 0x84fc180000000000

def z231 : W := mkw 0x0800c80022002100 0x0020032000880084 0xb801cc00ee0031d7 0xbee0073003b800c7

def z232 : W := mkw 0x1064000044210000 0x0041900001108400 0xb8e00000ee000001 0x06e3800003b80000

def z233 : W := mkw 0x020a000000000000 0x0008280000000000 0x471e000000000002 0xc11c780000000000

def z234 : W := mkw 0xfefe8884ddad8008 0xc3fbfa221376b600 0xffffcfc7ffffc023 0xffffff3f1fffff00

def z235 : W := mkw 0x13fe161b44ffd6c8 0xc84ff8586d13ff5b 0x47fe3e3f11fffffe 0xf91ff8f8fc47ffff

def z236 : W := mkw 0x12fe021b44bfd248 0xc84bf8086d12ff49 0x00fe023f003fc020 0x4003f808fc00ff00

def z237 : W := mkw 0xc0916368b01a3a02 0x7302458da2c068e8 0x4019f3f8100e3e18 0x210067cfe04038f8

def z238 : W := mkw 0xc0912128900a0a02 0x73024484a2402828 0xc0f9f3f8100e0e0b 0x6303e7cfe0403838

def z239 : W := mkw 0xe7bb777af03a3a06 0xf79eedddebc0e8e8 0xc7f9f3f8f03e3e1b 0x731fe7cfe3c0f8f8

def z240 : W := mkw 0x0901fc00bb402d90 0x142407f002ed00b6 0x0001fc00ffc03fdc 0x380007f003ff00ff

def z241 : W := mkw 0xf4f40000dd290008 0xc3d3d0000374a400 0xf8f80000fe3e0003 0x57e3e00003f8f800

def z242 : W := mkw 0xe400000099000000 0x0390000002640000 0x4700000011c00000 0x011c000000470000

def z243 : W := mkw 0xe4b00000d9280000 0x4392c0000364a000 0xfff80000fffe0003 0xdfffe00003fff800

def z244 : W := mkw 0x3f4e9c000fc58598 0x84fd3a70003f1616 0x3f060c000fc1c1e4 0x8cfc1830003f0707

def z245 : W := mkw 0x0100161b00d6d6c0 0x080400586c035b5b 0x00003e3f11fffffc 0x380000f8fc47ffff

def z246 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z247 : W := mkw 0xc0b12368d03a1a02 0x7302c48da340e868 0x40f833f8103e0e08 0x4103e0cfe040f838

def z248 : W := mkw 0xf6ff6368fdbfba0a 0xf3dbfd8da3f6fee8 0xfffff3f8fffffe3b 0xffffffcfe3fffff8

def z249 : W := mkw 0x2d00dc002b402590 0x04b4037000ad0096 0xbf01cc00efc031d7 0xbefc073003bf00c7

def z250 : W := mkw 0x0800888400000000 0x0020022210000000 0x0001cfc700000000 0x2000073f1c000000

def z251 : W := mkw 0x030a141300c4c4c0 0x080c28504c031313 0x47063c0711c1fffe 0xb91c18f01c4707ff

def z252 : W := mkw 0xfffffdb6ffedad9c 0xf7fffff6dbffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z253 : W := mkw 0xe490000099080008 0xc392400002642000 0x0000000000000000 0x0000000000000000

def z254 : W := mkw 0x030b777b20d6fec2 0x380c2dddec835bfb 0x471fffff11fffffe 0xf91c7ffffc47ffff

def z255 : W := mkw 0xc0b16369f03a7a42 0x7302c58da7c0e9e9 0xc0fffffff03fffff 0xfb03ffffffc0ffff

def z256 : W := mkw 0xe79b353200000004 0xa79e6cd4c8000000 0x471e3e3f00000002 0xe11c78f8fc000000

def z257 : W := mkw 0xffdfbdb600848004 0xa7ff7ef6d8021200 0xffffffff11ffc023 0xfffffffffc47ff00

def z258 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x80e1f3f8e0003e19 0x220387cfe38000f8

def z259 : W := mkw 0xf7ff3532ddad800c 0xe7dffcd4cb76b600 0xfffe3038ffffc023 0xdffff8c0e3ffff00

def z260 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7c3c7ee31c021 0x46e39f0f1fb8c700

def z261 : W := mkw 0xfedfa9a400000004 0xa7fb7ea690000000 0xffffc1c000000003 0xc7ffff0700000000

def z262 : W := mkw 0x0800880000000000 0x0020022000000000 0xb801cc0000000003 0xa6e0073000000000

def z263 : W := mkw 0xc0b16369f63b7b43 0x7302c58da7d8eded 0xc0f9f3f8fe3fffff 0x7b03e7cfe3f8ffff

def z264 : W := mkw 0xe5913528994a0e92 0x779644d4a265283a 0x4718303811ce0e08 0x011c60c0e0473838

def z265 : W := mkw 0xe69a000000000000 0x839a680000000000 0x4718000000000000 0x011c600000000000

def z266 : W := mkw 0x18648ac546315141 0x0061922b1518c545 0x38e60fc70e31c1e4 0xcce3983f1c38c707

def z267 : W := mkw 0x09009c0002400590 0x0424027000090016 0x00000c00000001c4 0x0000003000000007

def z268 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x07063e3f01c1fffc 0xa81c18f8fc0707ff

def z269 : W := mkw 0xc091212090080802 0x7302448482402020 0x0000000000000000 0x0000000000000000

def z270 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x07060c0711fffffc 0x981c18301c47ffff

def z271 : W := mkw 0xfffffdf666212105 0xa7fffff7d9988484 0xffffffffee000003 0xe7ffffffffb80000

def z272 : W := mkw 0xf6fe021bddbfd248 0xcbdbf8086f76ff49 0xfffe023fffffc023 0xdffff808ffffff00

def z273 : W := mkw 0xe500140099400480 0x0394005002650012 0xff003c00ffc03fdf 0xbffc00f003ff00ff

def z274 : W := mkw 0xffffbdb644210004 0xa7fffef6d9108400 0xffffffffee31c023 0xffffffffffb8c700

def z275 : W := mkw 0xc30b761bb0d6fec0 0x1b0c2dd86ec35bfb 0xc71ffe3ff1ffffff 0xfb1c7ff8ffc7ffff

def z276 : W := mkw 0x1844888400000000 0x0061122210000000 0xb8e1c1c000000001 0x06e3870700000000

def z277 : W := mkw 0x0000020100105040 0x0000000804004141 0x000602070031c020 0x400018081c00c700

def z278 : W := mkw 0xfd65fec566317141 0x07f597fb1598c5c5 0xffe7ffc7ee31f1f7 0xffff9fff1fb8c7c7

def z279 : W := mkw 0xe401200099000810 0x1790048002640020 0x0000000000000000 0x0000000000000000

def z280 : W := mkw 0x1864c8c466212101 0x0061932311988484 0xb8e1cdc0ee0031d7 0xbee3873703b800c7

def z281 : W := mkw 0x0000000000848000 0x0000000000021200 0x0000000011ffc020 0x180000000047ff00

def z282 : W := mkw 0xf7df35b600000004 0xa7df7cd6d8000000 0x47fe33ff00000000 0x411ff8cffc000000

def z283 : W := mkw 0x36fe00004dad8008 0xc0dbf8000136b600 0x3ffe00000fffc020 0xccfff800003fff00

def z284 : W := mkw 0x00004000b0002800 0x1000010002c000a0 0x00000000f0003e18 0x1000000003c000f8

def z285 : W := mkw 0x0020000044210000 0x0000800001108400 0x00000000ee31c020 0x1800000003b8c700

def z286 : W := mkw 0x03ba177b40fed6c2 0x680ee85ded03fb5b 0x47fe3fff11fffffe 0xf91ff8fffc47ffff

def z287 : W := mkw 0xc991bdb600000004 0x272646f6d8000000 0xc0f9ffff00000003 0x6303e7fffc000000

def z288 : W := mkw 0xf6ff6368f03a3a02 0xf3dbfd8da3c0e8e8 0xfffff3f8f03e3e1b 0xf7ffffcfe3c0f8f8

def z289 : W := mkw 0xf4f56160fd29280a 0xf3d3d58583f4a4a0 0xb8e1c1c0ee000001 0x06e3870703b80000

def z290 : W := mkw 0xf6fe0000d0280000 0xc3dbf8000340a000 0xfffe0000f03e0003 0xd7fff80003c0f800

def z291 : W := mkw 0x030a141200c48480 0x080c285048031212 0x0700000001c00000 0x001c000000070000

def z292 : W := mkw 0xe79b353299400c94 0xb79e6cd4ca650032 0x4718303811c00e08 0x011c60c0e0470038

def z293 : W := mkw 0x0020424966f7f7c1 0x08008109259bdfdf 0x00000000fffffffc 0x1800000003ffffff

def z294 : W := mkw 0xfd65fcc4ff612d91 0x17f597f313fd84b6 0xffe1fdc0ffc03fdf 0xbfff87f703ff00ff

def z295 : W := mkw 0xc091212000000000 0x2302448480000000 0x80e1c1c000000001 0x0203870700000000

def z296 : W := mkw 0xef9bbdb600000004 0xa7be6ef6d8000000 0x4719ffff00000000 0x211c67fffc000000

def z297 : W := mkw 0x030a141200400480 0x000c285048010012 0x471e3e3f11c03fde 0xf91c78f8fc4700ff

def z298 : W := mkw 0xffdfbdb699400c94 0xb7ff7ef6da650032 0xffffffff11c00e0b 0xe7fffffffc470038

def z299 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x47183e3f11ce3fdc 0x211c60f8fc4738ff

def z300 : W := mkw 0xf6de00000d858008 0x83db780000361600 0xfffe00000fc1c023 0xcffff800003f0700

def z301 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000300010003e1a 0x310000c0004000f8

def z302 : W := mkw 0x01001413004044c0 0x080400504c010113 0x00000c07000001c4 0x000000301c000007

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0xb8000000ee000003 0x9ee0000003b80000

def z304 : W := mkw 0xf4f40000dd290008 0xc3d3d0000374a400 0xffe00000ffc00003 0x9fff800003ff0000

def z305 : W := mkw 0x3d449c850f4145d1 0x04f51272143d0517 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z306 : W := mkw 0x0100161b005256c0 0x080400586c01495b 0x00063e3f0031fffe 0xf80018f8fc00c7ff

def z307 : W := mkw 0x0100160900d6d6c0 0x0804005824035b5b 0x47003c0011fffffe 0xb91c00f00047ffff

def z308 : W := mkw 0xe69a0000998c8008 0xc39a680002663200 0x471e000011ffc022 0xd91c78000047ff00

def z309 : W := mkw 0x020a000000848000 0x0008280000021200 0x0706000001c1c020 0x881c180000070700

def z310 : W := mkw 0x1b4e9e9f00d6d6c0 0x086d3a7a7c035b5b 0xffffffff11ffffff 0xfffffffffc47ffff

def z311 : W := mkw 0xe6ba0000d9ac8008 0xc39ae8000366b200 0xc7f80000f1fe0003 0x531fe00003c7f800

def z312 : W := mkw 0xc0b00000ddad8008 0x4302c0000376b600 0xc0f80000ffffc023 0x5b03e00003ffff00

def z313 : W := mkw 0xc0b16368fdbfba0a 0x7302c58da3f6fee8 0xc0f9f3f8fffffe3b 0x7b03e7cfe3fffff8

def z314 : W := mkw 0x0020404060202000 0x0000810101808080 0x80e1c1c0e0000001 0x0203870703800000

def z315 : W := mkw 0x1864cacd66337341 0x0061932b3598cdcd 0xf8fffffffe3fffff 0xffe3fffffff8ffff

def z316 : W := mkw 0xfcf5ebe566317145 0xa7f3d7af9598c5c5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z317 : W := mkw 0x00204248f03a3a02 0x5000810923c0e8e8 0x80e1c3c0f03e3e1b 0x7203870f03c0f8f8

def z318 : W := mkw 0x0000000100004040 0x0000000004000101 0x00060c070001c1e4 0x880018301c000707

def z319 : W := mkw 0x3f4e9c9706014145 0x84fd3a725c180505 0x3f060c070e01c1e4 0x8cfc18301c380707

def z320 : W := mkw 0xd2df21b600000004 0xa34b7c86d8000000 0xc0fff3ff00000003 0x6303ffcffc000000

def z321 : W := mkw 0x0100140000400480 0x0004005000010012 0x07000c0001c001c4 0x881c003000070007

def z322 : W := mkw 0xf7fe1413ddedc4c8 0xcbdff8504f77b713 0xfffe0c07ffffc1e7 0xdffff8301fffff07

def z323 : W := mkw 0xed01fe09bbd6ffd0 0x1fb407f826ef5bff 0xff01fc00ffffffff 0xbffc07f003ffffff

def z324 : W := mkw 0x0020424060303000 0x000081090180c0c0 0x80e1c3c0e0303013 0x7203870f0380c0c0

def z325 : W := mkw 0xf6df212000000000 0xa3db7c8480000000 0xfffff3f800000003 0xe7ffffcfe0000000

def z326 : W := mkw 0xd8f5ebecf63b3b03 0x7363d7afb3d8ecec 0xf8f9f3f8fe3e3e1b 0x77e3e7cfe3f8f8f8

def z327 : W := mkw 0xfffffe1bffffffd8 0xdffffff86fffffff 0xfffffe3fffffffff 0xfffffff8ffffffff

def z328 : W := mkw 0xfdd5bdb600000004 0xa7f756f6d8000000 0xb8e1ffff00000001 0x26e387fffc000000

def z329 : W := mkw 0x030a161300105040 0x000c28584c004141 0x471e3e3f0031f1f6 0xf91c78f8fc00c7c7

def z330 : W := mkw 0xe79b353200000004 0xa79e6cd4c8000000 0x4718303800000000 0x011c60c0e0000000

def z331 : W := mkw 0x0000020800121200 0x0000000820004848 0x00000000103e3e18 0x100000000040f8f8

def z332 : W := mkw 0xed91fd28bb4a2f92 0x77b647f4a2ed28be 0xff19fc38ffce3fdf 0xbffc67f0e3ff38ff

def z333 : W := mkw 0xffdfbdb60b400594 0xa7ff7ef6d82d0016 0xffffffff0fc001c7 0xeffffffffc3f0007

def z334 : W := mkw 0x0000000800c68680 0x0800000020031a1a 0x0000000011ce0e08 0x0000000000473838

def z335 : W := mkw 0x00b0016040280002 0x6002c0058100a000 0x00e001c000000000 0x0003800700000000

def z336 : W := mkw 0x0020024040301000 0x000080090100c040 0x00e003c000300000 0x4003800f0000c000

def z337 : W := mkw 0x0000036800121202 0x2000000da0004848 0x000003f800000000 0x0000000fe0000000

def z338 : W := mkw 0x030a141300c4c4c0 0x080c28504c031313 0x471e0c0711ffc1e6 0xd91c78301c47ff07

def z339 : W := mkw 0x1864cac466313101 0x0061932b1198c4c4 0xb8e1c3c0ee303013 0x76e3870f03b8c0c0

def z340 : W := mkw 0xc3ba161bd0fed6c0 0x4b0ee8586f43fb5b 0xc7fe3e3ff1ffffff 0xfb1ff8f8ffc7ffff

def z341 : W := mkw 0x12fe03fe403a1206 0xe04bf80ff900e848 0x00fe03ff003e0000 0x4003f80ffc00f800

def z342 : W := mkw 0xc091232800121200 0x2302448ca0004848 0xc0f9f3f8103e3e1b 0x7303e7cfe040f8f8

def z343 : W := mkw 0x030a161a00d69680 0x080c285868035a5a 0x4718323811fe3e1a 0x711c60c8e047f8f8

def z344 : W := mkw 0xec00c800bb002100 0x03b0032002ec0084 0xff01cc00ffc031d7 0xbffc073003ff00c7

def z345 : W := mkw 0xffffff68ffffbf9a 0xf7fffffda3fffefe 0xfffffff8ffffffff 0xffffffffe3ffffff

def z346 : W := mkw 0xf6fe0209ddffd6c8 0xcbdbf8082777ff5b 0xfffe0000ffffffff 0xdffff80003ffffff

def z347 : W := mkw 0xe5b17768f97a3e92 0x7796c5dda3e5e8fa 0xc7f9f3f8f1fe3e1b 0x731fe7cfe3c7f8f8

def z348 : W := mkw 0xffdffdb6b0002804 0xb7ff7ff6dac000a0 0xfffffffff0003e1b 0xf7ffffffffc000f8

def z349 : W := mkw 0xed01ff68bb523f92 0x37b407fda2ed48fe 0xff01fff8ffc03fdf 0xbffc07ffe3ff00ff

def z350 : W := mkw 0xc0b16369f0fefec2 0x7b02c58da7c3fbfb 0xc0f9f3f8f1ffffff 0x7b03e7cfe3c7ffff

def z351 : W := mkw 0xf4f56368fd3b3a0a 0xf3d3d58da3f4ece8 0xf8f9f3f8fe3e3e1b 0x77e3e7cfe3f8f8f8

def z352 : W := mkw 0x0020024144315041 0x000080090510c541 0x000000000031c020 0x000000000000c700

def z353 : W := mkw 0xffdffff722107145 0xa7ff7fffdc8841c5 0xffffffff000031d7 0xe7fffffffc0000c7

def z354 : W := mkw 0x1844cac526117141 0x0061132b149845c5 0x3807cfc70e01f1f4 0xace01f3f1c3807c7

def z355 : W := mkw 0x0100161b005256c0 0x080400586c01495b 0x40183e3f103e3fde 0x710060f8fc40f8ff

def z356 : W := mkw 0xc0b00368d03a1202 0x6302c00da340e848 0xc0f803f8f03e0003 0x5303e00fe3c0f800

def z357 : W := mkw 0x020a000000848000 0x0008280000021200 0x4718000011ce0000 0x011c600000473800

def z358 : W := mkw 0xf6ff2120ddad8008 0xe3dbfc848376b600 0xfffff3f8ffffc023 0xffffffcfe3ffff00

def z359 : W := mkw 0x106442c566317141 0x0041910b1598c5c5 0x00e603c7ee31f1f4 0x5803980f1fb8c7c7

def z360 : W := mkw 0xed01bc009b400d90 0x17b406f0026d0036 0x7f003c001fc00fcc 0x8dfc00f0007f003f

def z361 : W := mkw 0xc801e800b2002900 0x132007a002c800a4 0xf801fc00fe003fdf 0xbfe007f003f800ff

def z362 : W := mkw 0x0901ff6822523f92 0x342407fda08948fe 0x0001fff800003fdc 0x200007ffe00000ff

def z363 : W := mkw 0x00b04368f03a3a02 0x7002c10da3c0e8e8 0x00f803f8f03e3e18 0x5003e00fe3c0f8f8

def z364 : W := mkw 0xf6fe4000ffedad98 0xd3dbf90003ffb6b6 0xfffe0000ffffffff 0xdffff80003ffffff

def z365 : W := mkw 0x0020424860323200 0x000081092180c8c8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z366 : W := mkw 0x1ade89b600000004 0xa06b7a26d8000000 0xb8ffcfff00000003 0xe6e3ff3ffc000000

def z367 : W := mkw 0x2f0a9c130bc4c5d0 0x0cbc2a704c2f1317 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z368 : W := mkw 0x029a013200000004 0xa00a6804c8000000 0x0018003800000000 0x00006000e0000000

def z369 : W := mkw 0xfcf5e9e466212105 0xa7f3d7a791988484 0xb8e1c1c0ee000001 0x06e3870703b80000

def z370 : W := mkw 0xc091636820123a02 0x3302458da08048e8 0xc0f9f3f800003e1b 0x6303e7cfe00000f8

def z371 : W := mkw 0xc0b04248f03a3a02 0x5302c10923c0e8e8 0xc0f80000f03e3e1b 0x5303e00003c0f8f8

def z372 : W := mkw 0x0100160800521680 0x000400582001485a 0x47183e3811fe3fde 0xf91c60f8e047f8ff

def z373 : W := mkw 0x1064424166317141 0x004191090598c5c5 0xb8e60000ee31f1f7 0xdee3980003b8c7c7

def z374 : W := mkw 0x0020000040200000 0x0000800001008000 0x80e00000e0300003 0x520380000380c000

def z375 : W := mkw 0x00204241ff717dd1 0x1000810907fdc5f7 0x00000000fff1fffc 0x1800000003ffc7ff

def z376 : W := mkw 0xc39b373b00d6d6c0 0x2b0e6cdcec035b5b 0xc7ffffff11ffffff 0xfb1ffffffc47ffff

def z377 : W := mkw 0x00b00368403a1202 0x6002c00da100e848 0x40f833f8103e3e1a 0x7103e0cfe040f8f8

def z378 : W := mkw 0xf4d4000000000000 0x83d3500000000000 0xb8e0000000000001 0x06e3800000000000

def z379 : W := mkw 0x0800c800bb402d90 0x1020032002ed00b6 0xb801cc00ffc03fdf 0xbee0073003ff00ff

def z380 : W := mkw 0x124e009600000004 0x8049380258000000 0x0006000700000000 0x000018001c000000

def z381 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff01f000ffc00e09 0x07fc07c003ff0038

def z382 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xb801fc00ee003fdd 0x26e007f003b800ff

def z383 : W := mkw 0x0801a9a400000004 0x242006a690000000 0x0001c1c000000000 0x0000070700000000

def z384 : W := mkw 0x1044000004010000 0x0041100000100400 0x380600000e01c020 0x8ce0180000380700

def z385 : W := mkw 0xf4640000dd210000 0x03d1900003748400 0xffe60000fff1c023 0xdfff980003ffc700

def z386 : W := mkw 0x00204249f0fefec2 0x5800810927c3fbfb 0x00000000f1fffffc 0x1800000003c7ffff

def z387 : W := mkw 0xed01bdb600000004 0x27b406f6d8000000 0xff01ffff00000003 0xa7fc07fffc000000

def z388 : W := mkw 0x00004209bbd6ffd0 0x1800010826ef5bff 0x00000000fffffffc 0x1800000003ffffff

def z389 : W := mkw 0x0800cac522107141 0x0020032b148841c5 0x0007cfc70031f1f6 0xf8001f3f1c00c7c7

def z390 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x4718303811fffffc 0x191c60c0e047ffff

def z391 : W := mkw 0xe70a161b99d6d6c0 0x0b9c28586e675b5b 0xff1e3e3fffffffff 0xfffc78f8ffffffff

def z392 : W := mkw 0x12fe000044ad8008 0xc04bf8000112b600 0x47fe000011ffc022 0xd91ff8000047ff00

def z393 : W := mkw 0xffdfbdbe900a0a06 0xf7ff7ef6fa402828 0xffffffff100e0e0b 0xe7fffffffc403838

def z394 : W := mkw 0x3e4e88850f85c149 0x80f93a22143e1705 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z395 : W := mkw 0xd8f4cac5f6397141 0x4363d32b17d8e5c5 0xf8ffcfc7fe3ff1f7 0xffe3ff3f1ff8ffc7

def z396 : W := mkw 0xf4f40000dd290008 0xc3d3d0000374a400 0xb8e60000ee31c023 0xdee3980003b8c700

def z397 : W := mkw 0xe79b353a00c68684 0xaf9e6cd4e8031a1a 0x4718303811ce0e08 0x011c60c0e0473838

def z398 : W := mkw 0x0001600020002800 0x10000580008000a0 0x0001f00000003e18 0x200007c0000000f8

def z399 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0x38060c07ee31f1f4 0x9ce018301fb8c7c7

def z400 : W := mkw 0xffde9c9600000004 0x87ff7a7258000000 0xfffe0c0700000003 0xc7fff8301c000000

def z401 : W := mkw 0xfefe8885dfadc149 0xc3fbfa22177eb705 0xfffe0c07ffffc1e7 0xdffff8301fffff07

def z402 : W := mkw 0x0000000099400c90 0x1000000002650032 0x0000000011c00e08 0x0000000000470038

def z403 : W := mkw 0x032a565bf0fefec2 0x580ca9596fc3fbfb 0x471e3e3ff1fffffe 0xf91c78f8ffc7ffff

def z404 : W := mkw 0xed01fdb6bb402d94 0x37b407f6daed00b6 0xff01ffffffc03fdf 0xbffc07ffffff00ff

def z405 : W := mkw 0x3d64dec56f7175d1 0x04f5937b15bdc5d7 0xbfe7cfc7eff1f1f7 0xfeff9f3f1fbfc7c7

def z406 : W := mkw 0xef0bbe1b00d6d6c0 0x0fbc2ef86c035b5b 0xff1ffe3f11ffffff 0xfffc7ff8fc47ffff

def z407 : W := mkw 0xc9b1fffef03a3a06 0x7726c7fffbc0e8e8 0xc0f9fffff03e3e1b 0x7303e7ffffc0f8f8

def z408 : W := mkw 0xef0bfc12bb402d90 0x17bc2ff04aed00b6 0xff1ffe3fffc03fdf 0xfffc7ff8ffff00ff

def z409 : W := mkw 0xfeffebedffbffb4b 0xf3fbffafb7feffed 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0x020a021b0096d240 0x080828086c025b49 0x001e0e3f003ff1f6 0xf8007838fc00ffc7

def z411 : W := mkw 0x0901fff722107145 0x242407ffdc8841c5 0x0001ffff000031d4 0x200007fffc0000c7

def z412 : W := mkw 0xd8f5ebe5f6397943 0x7363d7af97d8e5e5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z413 : W := mkw 0x0900dedf225277c1 0x0824037b7c8949df 0x0001ffff00003fdc 0x200007fffc0000ff

def z414 : W := mkw 0xfcd5a9a400000004 0xa7f356a690000000 0xf8f9f3f800000003 0x67e3e7cfe0000000

def z415 : W := mkw 0x0000000000000000 0x0000000000000000 0x80e1c3c000000003 0x6203870f00000000

def z416 : W := mkw 0x3f6eded766317145 0x84fdbb7b5d98c5c5 0xbfe7cfc7ee31f1f7 0xfeff9f3f1fb8c7c7

def z417 : W := mkw 0xc0b16160f0282802 0x7302c58583c0a0a0 0xc0e1f1c0f0003e1b 0x330387c703c000f8

def z418 : W := mkw 0x0020404066212101 0x0000810101988484 0x00000000ee000000 0x0000000003b80000

def z419 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xfff9f1f800000001 0x07ffe7c7e0000000

def z420 : W := mkw 0x01001601005054c0 0x0004005804014153 0x47063e0711f1fffe 0xf91c18f81c47c7ff

def z421 : W := mkw 0xe79b3532998c800c 0xe79e6cd4ca663200 0x4718303811ce0000 0x011c60c0e0473800

def z422 : W := mkw 0xffffbfbfddffd6cc 0xeffffefeff77ff5b 0xffffffffffffffff 0xffffffffffffffff

def z423 : W := mkw 0xf6de000000848000 0x83db780000021200 0xfffe000011ffc023 0xdffff8000047ff00

def z424 : W := mkw 0x0901fec522507dd1 0x142407fb148941f7 0x0001ffc700003fdc 0x200007ff1c0000ff

def z425 : W := mkw 0x032a565b66f7f7c1 0x080ca9596d9bdfdf 0x471e3e3ffffffffe 0xf91c78f8ffffffff

def z426 : W := mkw 0xff6ffedffff7ffd1 0x1ffdbffb7fffdfff 0xffffffffffffffff 0xffffffffffffffff

def z427 : W := mkw 0x030a141a00c68680 0x080c285068031a1a 0x471e3e3f11ce0e0a 0xe11c78f8fc473838

def z428 : W := mkw 0xf6fe000044ad8008 0xc3dbf8000112b600 0xfffe0000003fc023 0xc7fff8000000ff00

def z429 : W := mkw 0x0b0bbfbf00d6d6c4 0x2c2c2efefc035b5b 0x471fffff11fffffe 0xf91c7ffffc47ffff

def z430 : W := mkw 0x0020424060303000 0x000081090180c0c0 0x00000000e0303010 0x100000000380c0c0

def z431 : W := mkw 0x0001212800020a02 0x30000484a0000828 0x0000303800000e08 0x000000c0e0000038

def z432 : W := mkw 0x18f4cbed663b7343 0x6063d32fb598edcd 0xb8ffcfffee3ff1f7 0xfee3ff3fffb8ffc7

def z433 : W := mkw 0x09009c9600000004 0x0424027258000000 0x00000c0700000000 0x000000301c000000

def z434 : W := mkw 0x1844cac522107141 0x0061132b148841c5 0xb8e7cfc7000031d7 0xe6e39f3f1c0000c7

def z435 : W := mkw 0xe79a141a99ce8688 0xcb9e68506a673a1a 0x4718303811ce0e08 0x011c60c0e0473838

def z436 : W := mkw 0xc0216240f0303800 0x1300858903c0c0e0 0xc0e1f3c0f0303e1b 0x730387cf03c0c0f8

def z437 : W := mkw 0xf6ff6000fdada808 0xd3dbfd8003f6b6a0 0xfffff000fffffe3b 0xffffffc003fffff8

def z438 : W := mkw 0xc39b353a90ce8e82 0x7b0e6cd4ea433a3a 0x4718303811ce0e08 0x011c60c0e0473838

def z439 : W := mkw 0xc3bb777af03a3a02 0x730eedddebc0e8e8 0xc7fffffff03e3e1b 0xf31fffffffc0f8f8

def z440 : W := mkw 0x2500140009400490 0x0494005000250012 0x0700000001c00000 0x001c000000070000

def z441 : W := mkw 0xc000000090000000 0x0300000002400000 0xc0000000f0000003 0x1300000003c00000

def z442 : W := mkw 0xe4016000b9002800 0x1390058002e400a0 0xff01f000ffc03e1b 0xbffc07c003ff00f8

def z443 : W := mkw 0xff4ffc96bb402d94 0x97fd3ff25aed00b6 0xff07fc07ffc03fdf 0xbffc1ff01fff00ff

def z444 : W := mkw 0x0090012000000000 0x2002400480000000 0x00f803f800000000 0x4003e00fe0000000

def z445 : W := mkw 0x3fde9db600000004 0xa4ff7a76d8000000 0x3ffe0fff00000000 0xc4fff83ffc000000

def z446 : W := mkw 0x030a161b0096d240 0x080c28586c025b49 0x471e3e3f003fc022 0xe11c78f8fc00ff00

def z447 : W := mkw 0xc8b1eb68f23a3b02 0x7322c7ada3c8e8ec 0xf8f9fff8fe3e3fdf 0xffe3e7ffe3f8f8ff

def z448 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0x4701fc0011c03fdc 0x211c07f0004700ff

def z449 : W := mkw 0xfd45fc84bb402d90 0x17f517f212ed00b6 0xffe7ffc7ffc03fdf 0xffff9fff1fff00ff

def z450 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0x00e7cfc70031f1f4 0x60039f3f1c00c7c7

def z451 : W := mkw 0xc0b16168f02a2a02 0x7302c585a3c0a8a8 0xc0f9f1f8f00e0e09 0x0303e7c7e3c03838

def z452 : W := mkw 0x10f403ed443b5243 0x6043d00fb510ed49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z453 : W := mkw 0x2d00dc00bb402d90 0x14b4037002ed00b6 0x3f000c00ffc03fdc 0x9cfc003003ff00ff

def z454 : W := mkw 0xe501340000000000 0x079404d000000000 0x4700300000000000 0x011c00c000000000

def z455 : W := mkw 0xc0b16000f0282800 0x5302c58003c0a0a0 0xc0f9f000f03e3e1b 0x7303e7c003c0f8f8

def z456 : W := mkw 0xe70b341a99c68e90 0x1f9c2cd06a671a3a 0x4718303811ce0e08 0x011c60c0e0473838

def z457 : W := mkw 0x2f0a9e1b0bd6d7d0 0x0cbc2a786c2f5b5f 0x7f1e3e3f1ffffffe 0xfdfc78f8fc7fffff

def z458 : W := mkw 0xffffffff66f7f7c5 0xaffffffffd9bdfdf 0xffffffffffffffff 0xffffffffffffffff

def z459 : W := mkw 0xf6fe4240fdbdb008 0xc3dbf90903f6f6c0 0xffffc3c0fffff033 0xffffff0f03ffffc0

def z460 : W := mkw 0x0b0adedf22d6f7c1 0x082c2b7b7c8b5bdf 0x471fffff11fffffe 0xf91c7ffffc47ffff

def z461 : W := mkw 0xe79a161b99ded6c8 0xcb9e68586e677b5b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z462 : W := mkw 0x374e161b0dd7d6c8 0x88dd38586c375f5b 0x7f1e3e3f1ffffffe 0xfdfc78f8fc7fffff

def z463 : W := mkw 0x1afecac566bdf149 0xc06bfb2b159af7c5 0xb8ffcfc7ee3ff1f7 0xfee3ff3f1fb8ffc7

def z464 : W := mkw 0x0000424020103000 0x00000109008040c0 0x0001c3c000003010 0x2000070f000000c0

def z465 : W := mkw 0x12fe000044ad8008 0xc04bf8000112b600 0xb8fe0000ee3fc023 0xdee3f80003b8ff00

def z466 : W := mkw 0xc2bb6368f0beba02 0x730aed8da3c2fae8 0xc7fff3f8f1fffe3b 0xfb1fffcfe3c7fff8

def z467 : W := mkw 0xf7fe1412ddad8008 0xc3dff8504b76b600 0xfffe3e3fffffc023 0xfffff8f8ffffff00

def z468 : W := mkw 0xfffe9c00dfed8598 0xc7fffa70037fb616 0xfffe0c00ffffc1e7 0xdffff83003ffff07

def z469 : W := mkw 0xfffffdf6f0282806 0xf7fffff7dbc0a0a0 0xffffffffe0000003 0xe7ffffffff800000

def z470 : W := mkw 0xc1b1777bf07a7ec2 0x7b06c5ddefc1e9fb 0xc0f9fffff03e3fdf 0x7303e7ffffc0f8ff

def z471 : W := mkw 0xc091212000000000 0x2302448480000000 0x4018303800000000 0x010060c0e0000000

def z472 : W := mkw 0xfede888400000000 0x83fb7a2210000000 0xffffcfc700000003 0xe7ffff3f1c000000

def z473 : W := mkw 0x1064000044210000 0x0041900001108400 0x00e600000031c020 0x400398000000c700

def z474 : W := mkw 0xe5017400bb402d90 0x179405d002ed00b6 0x47003000ffc03fdc 0x191c00c003ff00ff

def z475 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x001e3e3f003ffffc 0x600078f8fc00ffff

def z476 : W := mkw 0xfc64cac5ff317141 0x03f1932b17fcc5c5 0xffe7cfc7fff1f1f7 0xffff9f3f1fffc7c7

def z477 : W := mkw 0xfcf5e800ff292918 0xd7f3d7a003fca4a4 0xb8e1c000ee000001 0x06e3870003b80000

def z478 : W := mkw 0xef9bfd32bb402d94 0xb7be6ff4caed00b6 0xff19fc38ffc03fdf 0xbffc67f0e3ff00ff

def z479 : W := mkw 0x0000020100105040 0x0000000804004141 0x00000e07000031d4 0x200000381c0000c7

def z480 : W := mkw 0xd0f40000d4290000 0x4343d0000350a400 0xf8fe0000fe3fc023 0xdfe3f80003f8ff00

def z481 : W := mkw 0x00004000bb002910 0x1000010002ec00a4 0x00000000ee000000 0x0000000003b80000

def z482 : W := mkw 0xc0b12368403a1202 0x6302c48da100e848 0xc0f9f3f8003e0003 0x6303e7cfe000f800

def z483 : W := mkw 0xf6fe0208ddbf9208 0xc3dbf8082376fe48 0xfffe3238fffffe3b 0xfffff8c8e3fffff8

def z484 : W := mkw 0xfffffff660303004 0xa7ffffffd980c0c0 0xffffffffe0303013 0xf7ffffffff80c0c0

def z485 : W := mkw 0x1044008504014041 0x0041100214100501 0x000600070001c020 0x000018001c000700

def z486 : W := mkw 0xffdffffe20123a06 0xb7ff7ffff88048e8 0xffffffff00003e1b 0xe7fffffffc0000f8

def z487 : W := mkw 0xc8b1ebedf23a7b43 0x7322c7afb7c8e9ed 0xc0f9fffff03e3fdf 0x7303e7ffffc0f8ff

def z488 : W := mkw 0x0000020900d6d6c0 0x0800000824035b5b 0x00060e0711fffffe 0xf80018381c47ffff

def z489 : W := mkw 0xc0916120b0002800 0x3302458482c000a0 0xc0f9f3f8f0003e1b 0x7303e7cfe3c000f8

def z490 : W := mkw 0x1a6ecadf66b7f341 0x0869bb2b7d9adfcd 0xb8ffcfffee3ff1f7 0xfee3ff3fffb8ffc7

def z491 : W := mkw 0xed01bc0099000000 0x07b406f002640000 0xff01fc00ffc00003 0xbffc07f003ff0000

def z492 : W := mkw 0xc1017400b0402c80 0x130405d002c100b2 0xc701fc00f1c03fdf 0xbb1c07f003c700ff

def z493 : W := mkw 0x2d009c000b400590 0x04b40270002d0016 0x7f003c001fc03fde 0xbdfc00f0007f00ff

def z494 : W := mkw 0xef9bfc00bbccad98 0xd7be6ff002ef32b6 0xff19fc00ffce3fdf 0xbffc67f003ff38ff

def z495 : W := mkw 0xffdffdb622402d94 0xb7ff7ff6d88900b6 0xffffffff00003fdf 0xe7fffffffc0000ff

def z496 : W := mkw 0xe79b340099cc8c98 0xd79e6cd002673232 0x4718300011ce0e08 0x011c60c000473838

def z497 : W := mkw 0x0000021b00125240 0x080000086c004949 0x0000023f00000000 0x00000008fc000000

def z498 : W := mkw 0x0000400020002000 0x0000010000800080 0x8001c000e0003013 0x32000700038000c0

def z499 : W := mkw 0xf7df353200000004 0xa7df7cd4c8000000 0xfffe303800000003 0xc7fff8c0e0000000

def z500 : W := mkw 0xffffbc00ddad8008 0xc7fffef00376b600 0xfffffc00ffffc023 0xfffffff003ffff00

def z501 : W := mkw 0xc3bb777af0febe82 0x7b0eedddebc3fafa 0xc7f9f3f8f1fe3e1b 0x731fe7cfe3c7f8f8

def z502 : W := mkw 0xfedfa9b600000004 0xa7fb7ea6d8000000 0xb8ffc3ff00000001 0x46e3ff0ffc000000

def z503 : W := mkw 0x1b6eded766317141 0x006dbb7b5d98c5c5 0xffffffffee31f1f7 0xffffffffffb8c7c7

def z504 : W := mkw 0x0901fffe20123a06 0x342407fff88048e8 0x0001ffff00003e18 0x200007fffc0000f8

def z505 : W := mkw 0x1afecbf766317145 0xa06bfb2fdd98c5c5 0xb8ffcfffee31f1f7 0xfee3ff3fffb8c7c7

def z506 : W := mkw 0xf7ff777bfdfffeca 0xfbdffdddeff7fffb 0xffffffffffffffff 0xffffffffffffffff

def z507 : W := mkw 0x020a02010094d040 0x0008280804025341 0x471e0e0711fff1f6 0xf91c78381c47ffc7

def z508 : W := mkw 0xf6fe000044210000 0x83dbf80001108400 0xfffe0000ee31c023 0xdffff80003b8c700

def z509 : W := mkw 0x3f4e9c960b400594 0x84fd3a72582d0016 0x3f060c070fc001c4 0x8cfc18301c3f0007

def z510 : W := mkw 0xfcf5e9e4f0282806 0xf7f3d7a793c0a0a0 0xb8e1c1c0e0000001 0x06e3870703800000

def z511 : W := mkw 0x0000020000101000 0x0000000800004040 0x0000020000303012 0x700000080000c0c0

def z512 : W := mkw 0x1964dedf667377c1 0x0865937b7d99cddf 0xb8e7ffffee31ffff 0xfee39fffffb8c7ff

def z513 : W := mkw 0x10d401a400000004 0xa043500690000000 0x00e001c000000000 0x0003800700000000

def z514 : W := mkw 0x1864c8c466212101 0x0061932311988484 0xb8e7c1c0ee31c023 0xdee39f0703b8c700

def z515 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x80e1c1c0f03e3e19 0x1203870703c0f8f8

def z516 : W := mkw 0x0800ca0122107140 0x00200328048841c5 0xb807ce07ee31f1f7 0xfee01f381fb8c7c7

def z517 : W := mkw 0x020a000000848000 0x0008280000021200 0x001e0000003fc020 0x400078000000ff00

def z518 : W := mkw 0xc090000090080000 0x4302400002402000 0x40180000100e0000 0x0100600000403800

def z519 : W := mkw 0x1965fff766317145 0x246597ffdd98c5c5 0xb8e7ffffee31f1f7 0xfee39fffffb8c7c7

def z520 : W := mkw 0x020a021b0096d240 0x080828086c025b49 0x471e023f11ffc022 0xd91c7808fc47ff00

def z521 : W := mkw 0x0901fdb622402d94 0x342407f6d88900b6 0x0001ffff00003fdc 0x200007fffc0000ff

def z522 : W := mkw 0xfdf5fc00ff692d98 0xd7f7d7f003fda4b6 0xffe1fc00ffc03fdf 0xbfff87f003ff00ff

def z523 : W := mkw 0x0100141200000000 0x0004005048000000 0x00003e3f00000000 0x200000f8fc000000

def z524 : W := mkw 0xfdd5bda400000004 0xa7f756f690000000 0xffe1fdc000000003 0xa7ff87f700000000

def z525 : W := mkw 0xe69b2128998e8a0a 0xf39a6c84a2663a28 0x4718303811ce0e08 0x011c60c0e0473838

def z526 : W := mkw 0xc0b16360f0383802 0x7302c58d83c0e0e0 0x80e1c3c0e0303013 0x7203870f0380c0c0

def z527 : W := mkw 0xf7fe1400dded8488 0xc3dff8500377b612 0xfffe3c00ffffffff 0xfffff8f003ffffff

def z528 : W := mkw 0xe6ba0000ddad8008 0xc39ae8000376b600 0x47180000ffffc020 0x191c600003ffff00

def z529 : W := mkw 0xedb1fd60fb682d92 0x77b6c7f583eda0b6 0xffe1fdc0ffc03fdf 0xbfff87f703ff00ff

def z530 : W := mkw 0x106402c544315041 0x0041900b1510c541 0xb8e603c7ee31c023 0xdee3980f1fb8c700

def z531 : W := mkw 0x3f4e9c9600000004 0x84fd3a7258000000 0xbfe7cfc700000003 0xe6ff9f3f1c000000

def z532 : W := mkw 0x344400000d010008 0x80d1100000340400 0x380000000e000000 0x04e0000000380000

def z533 : W := mkw 0x0901fc0022402d90 0x142407f0008900b6 0x4701fc0011c03fde 0xb91c07f0004700ff

def z534 : W := mkw 0xfd65fc00ff612d90 0x17f597f003fd84b6 0xffe7fc00fff1ffff 0xffff9ff003ffc7ff

def z535 : W := mkw 0x106442c564317041 0x0041910b1590c5c1 0x80e7c3c7e031f033 0x72039f0f1f80c7c0

def z536 : W := mkw 0x0000000099000000 0x0000000002640000 0x00000000ffc00000 0x1800000003ff0000

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000c00000031d6 0xb8000030000000c7

def z538 : W := mkw 0x106402c544315041 0x0041900b1510c541 0x00e60fc70031f1f6 0xf803983f1c00c7c7

def z539 : W := mkw 0xd8f5ebecf03a3a02 0x7363d7afb3c0e8e8 0xf8fffffff03e3e1b 0xf7e3ffffffc0f8f8

def z540 : W := mkw 0xec01e800bb002910 0x17b007a002ec00a4 0xb801cc00ee0031d7 0xbee0073003b800c7

def z541 : W := mkw 0xc0912328901a1a02 0x7302448ca2406868 0x40183238103e3e1a 0x710060c8e040f8f8

def z542 : W := mkw 0xec01e800bb002910 0x17b007a002ec00a4 0xff01c000ffc00003 0x9ffc070003ff0000

def z543 : W := mkw 0xd2fe0000d4ad8008 0xc34bf8000352b600 0xc0fe0000f03fc023 0x5303f80003c0ff00

def z544 : W := mkw 0x0020424166317141 0x000081090598c5c5 0x80e1c3c0ee31f1f7 0x7a03870f03b8c7c7

def z545 : W := mkw 0xf7de161b00d6d6c0 0x8bdf78586c035b5b 0xfffe3e3f11ffffff 0xfffff8f8fc47ffff

def z546 : W := mkw 0x030a141200848000 0x000c285048021200 0x471e3e3f11ffc022 0xf91c78f8fc47ff00

def z547 : W := mkw 0x0800c80022002100 0x0020032000880084 0xb801c000ee000001 0x06e0070003b80000

def z548 : W := mkw 0x18448a8506115141 0x0061122a14184545 0x38060e070e31f1f6 0xfce018381c38c7c7

def z549 : W := mkw 0xef0bfc00bbc4ad90 0x17bc2ff002ef12b6 0xff1ffc00ffffffff 0xfffc7ff003ffffff

def z550 : W := mkw 0xed01fc00bb002910 0x17b407f002ec00a4 0xff01fc00ee000003 0xa7fc07f003b80000

def z551 : W := mkw 0xc0016000bb402d90 0x1300058002ed00b6 0xc001f000ffc03fdf 0x3b0007c003ff00ff

def z552 : W := mkw 0x020a021b00d6d6c0 0x080828086c035b5b 0x001e023f11fffffc 0x58007808fc47ffff

def z553 : W := mkw 0x030a141200000000 0x000c285048000000 0x07060c0700000000 0x801c18301c000000

def z554 : W := mkw 0x0800880002000100 0x0020022000080004 0x38000c000e0001c4 0x8ce0003000380007

def z555 : W := mkw 0xffffbdb6d0280004 0xe7fffef6db40a000 0xfffffffff03e0003 0xf7ffffffffc0f800

def z556 : W := mkw 0xe69a0000998c8008 0xc39a680002663200 0xff180000ffce0003 0x9ffc600003ff3800

def z557 : W := mkw 0x00b04368603a3202 0x6002c10da180e8c8 0x80f9c3f8e03e3013 0x7203e70fe380f8c0

def z558 : W := mkw 0x1844888506014141 0x0061122214180505 0xb8e7cfc70e01c1e7 0xeee39f3f1c380707

def z559 : W := mkw 0x3f4e9e9f00d6d6c4 0x8cfd3a7a7c035b5b 0x7f1e3e3f11fffffe 0xfdfc78f8fc47ffff

def z560 : W := mkw 0x0001616020002802 0x30000585808000a0 0x0001c1c000000000 0x0000070700000000

def z561 : W := mkw 0x12fe0000ddad8008 0xc04bf8000376b600 0x00fe0000ffffc020 0x5803f80003ffff00

def z562 : W := mkw 0xc0b16160f0282802 0x7302c58583c0a0a0 0xc0f9f3f8e0000003 0x6303e7cfe3800000

def z563 : W := mkw 0x13de17bf00d6d6c4 0xa84f785efc035b5b 0x47fe3fff11fffffe 0xf91ff8fffc47ffff

def z564 : W := mkw 0xffdfbfbe00121204 0xa7ff7efef8004848 0xffffffff103e3e1b 0xf7fffffffc40f8f8

def z565 : W := mkw 0xf6ff6160fdada80a 0xf3dbfd8583f6b6a0 0xffffc1c0ffffc023 0xdfffff0703ffff00

def z566 : W := mkw 0xffffbff744315045 0xa7fffeffdd10c541 0xffffffff0031c023 0xe7fffffffc00c700

def z567 : W := mkw 0xed21fe41ff717dd1 0x17b487f907fdc5f7 0xff01fc00fff1ffff 0xbffc07f003ffc7ff

def z568 : W := mkw 0xdbfffffff6ffffc3 0x7b6fffffffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z569 : W := mkw 0xc001200000000000 0x0300048000000000 0xc001f00000000003 0x230007c000000000

def z570 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xbfe60000efc1c021 0x8eff980003bf0700

def z571 : W := mkw 0xefbbff7bfbfeffd2 0x7fbeeffdefeffbff 0xffffffffffffffff 0xffffffffffffffff

def z572 : W := mkw 0x00216368f03a3a02 0x7000858da3c0e8e8 0x0001f3f8f03e3e18 0x300007cfe3c0f8f8

def z573 : W := mkw 0x0800c8c422002101 0x0020032310880084 0x0001c1c000000000 0x0000070700000000

def z574 : W := mkw 0xec01e800bb002910 0x17b007a002ec00a4 0xf801f000fe003e1b 0x37e007c003f800f8

def z575 : W := mkw 0x00204249f63b7b43 0x5000810927d8eded 0x00000000fe3ffffc 0x1800000003f8ffff

def z576 : W := mkw 0x00200209ddffd6c8 0x480080082777ff5b 0x00000000fffffffc 0x1800000003ffffff

def z577 : W := mkw 0xc0016000b0002800 0x1300058002c000a0 0x8001c000e0000001 0x0200070003800000

def z578 : W := mkw 0x000002c500105041 0x0000000b14004141 0x000003c700000000 0x0000000f1c000000

def z579 : W := mkw 0x0000020900d6d6c0 0x0800000824035b5b 0x4018323811fffffe 0x790060c8e047ffff

def z580 : W := mkw 0xc1b17768f07a3e82 0x7306c5dda3c1e8fa 0xc7f9fff8f1fe3fdf 0xfb1fe7ffe3c7f8ff

def z581 : W := mkw 0x0100140000000000 0x0004005000000000 0x47003c0000000002 0xa11c00f000000000

def z582 : W := mkw 0xf6ff2128ddaf8a0a 0xf3dbfc84a376be28 0xfffe3038ffffce2b 0xdffff8c0e3ffff38

def z583 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0x47fe000011ffc020 0x411ff8000047ff00

def z584 : W := mkw 0xfffffff7ffbdf14d 0xe7ffffffdffef7c5 0xfffffffffffff1f7 0xffffffffffffffc7

def z585 : W := mkw 0x030a161a00121200 0x000c285868004848 0x471e3e3f103e3e1a 0xf11c78f8fc40f8f8

def z586 : W := mkw 0x00000209005256c0 0x080000082401495b 0x0000000000003fdc 0x00000000000000ff

def z587 : W := mkw 0xe79b373b00d6d6c4 0xaf9e6cdcec035b5b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z588 : W := mkw 0x1a6ecac566b5f141 0x0069bb2b159ad7c5 0xffffcfc7fffff1f7 0xffffff3f1fffffc7

def z589 : W := mkw 0x0001636820123a02 0x3000058da08048e8 0x4019f3f8103e3e1a 0x710067cfe040f8f8

def z590 : W := mkw 0x032a565b60f6f6c0 0x080ca9596d83dbdb 0xc7fffffff1ffffff 0xfb1fffffffc7ffff

def z591 : W := mkw 0xc0b04240f0383000 0x4302c10903c0e0c0 0xc0f9c3c0f03e3013 0x7303e70f03c0f8c0

def z592 : W := mkw 0xe6bb6368f9beba0a 0xf39aed8da3e6fae8 0xc7f9f3f8f1fe3e1b 0x731fe7cfe3c7f8f8

def z593 : W := mkw 0xed01bc0099400c90 0x17b406f002650032 0xff01fc0011c00e0b 0xa7fc07f000470038

def z594 : W := mkw 0x1064424064313000 0x004191090190c4c0 0xb8e7c3c0ee31f033 0xfee39f0f03b8c7c0

def z595 : W := mkw 0x1864888546214141 0x0061922215188505 0xb8e60c07ee31c1e7 0xdee398301fb8c707

def z596 : W := mkw 0x0b0ade1b22d6f7c0 0x082c2b786c8b5bdf 0xff1ffe3fffffffff 0xfffc7ff8ffffffff

def z597 : W := mkw 0x12fe03f744315045 0xa04bf80fdd10c541 0x00fe03ff0031c020 0x4003f80ffc00c700

def z598 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfff80000ffce0001 0x07ffe00003ff3800

def z599 : W := mkw 0x1044008400000000 0x0041100210000000 0x00e603c700000000 0x4003980f1c000000

def z600 : W := mkw 0x0020000044ad8008 0x400080000112b600 0x00000000003fc020 0x000000000000ff00

def z601 : W := mkw 0xfcd5e9a4bb002914 0xb7f357a692ec00a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z602 : W := mkw 0xffdfbdbe00c68684 0xafff7ef6f8031a1a 0xffffffff11ce0e0b 0xe7fffffffc473838

def z603 : W := mkw 0x01005400bb402d90 0x1004015002ed00b6 0x47003c00ffc03fde 0xb91c00f003ff00ff

def z604 : W := mkw 0x270a141200000004 0x849c285048000000 0x0700000000000000 0x001c000000000000

def z605 : W := mkw 0xfefecac566317141 0x83fbfb2b1598c5c5 0xffffcfc7ee31f1f7 0xffffff3f1fb8c7c7

def z606 : W := mkw 0xff4ffc00bfc5ad98 0x97fd3ff002ff16b6 0xff07fc00ffc1ffff 0xbffc1ff003ff07ff

def z607 : W := mkw 0xc0b12120d0280000 0x6302c4848340a000 0xc0f9f3f8f03e0003 0x7303e7cfe3c0f800

def z608 : W := mkw 0xf6fe4241ffbdf149 0xc3dbf90907fef7c5 0xfffe0000fffff1f7 0xdffff80003ffffc7

def z609 : W := mkw 0x020a020900d6d6c0 0x0808280824035b5b 0x471e000011fffffe 0xd91c78000047ffff

def z610 : W := mkw 0x1964dec5667175c1 0x0065937b1599c5d7 0xffe7ffc7fff1ffff 0xffff9fff1fffc7ff

def z611 : W := mkw 0xf6de01b600000004 0xa3db7806d8000000 0xfffe03ff00000003 0xc7fff80ffc000000

def z612 : W := mkw 0x0100140000400480 0x0004005000010012 0x00003c0000003fdc 0x200000f0000000ff

def z613 : W := mkw 0x12de03bf0096d244 0xa84b780efc025b49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z614 : W := mkw 0x1044000000000000 0x0041100000000000 0xb8e6000000000003 0xc6e3980000000000

def z615 : W := mkw 0xffdfbdb706014145 0xa7ff7ef6dc180505 0xffffffff0e01c1e7 0xeffffffffc380707

def z616 : W := mkw 0x1864cac5ffbdf149 0x4061932b17fef7c5 0xb8e7cfc7fffff1f7 0xfee39f3f1fffffc7

def z617 : W := mkw 0x0b0bbdb600000004 0x242c2ef6d8000000 0x471fffff00000002 0xe11c7ffffc000000

def z618 : W := mkw 0xf6fe0368ddbf920a 0xe3dbf80da376fe48 0xfffe03f8ffffc023 0xdffff80fe3ffff00

def z619 : W := mkw 0xe400000000000000 0x0390000000000000 0xff00000000000003 0x87fc000000000000

def z620 : W := mkw 0x0100161b005256c0 0x080400586c01495b 0x47003e3f11c03fde 0xb91c00f8fc4700ff

def z621 : W := mkw 0x030a161300d4d4c0 0x080c28584c035353 0x07060e0701f1f1f6 0xf81c18381c07c7c7

def z622 : W := mkw 0x00204000ffedad98 0x5000810003ffb6b6 0x00000000fffffffc 0x1800000003ffffff

def z623 : W := mkw 0x0901bc0000000000 0x042406f000000000 0x0001fc0000000000 0x200007f000000000

def z624 : W := mkw 0x030a141b00c6c6c0 0x080c28506c031b1b 0x471e3c3f11cfcfec 0x891c78f0fc473f3f

def z625 : W := mkw 0x0101353200000004 0x240404d4c8000000 0x0000303800000000 0x000000c0e0000000

def z626 : W := mkw 0xfffffff7ff717dd5 0xb7ffffffdffdc5f7 0xfffffffffff1ffff 0xffffffffffffc7ff

def z627 : W := mkw 0x136e16df44f7d6c1 0x084db85b7d13df5b 0x47fe3fff11fffffe 0xf91ff8fffc47ffff

def z628 : W := mkw 0x0901fc0022402d90 0x142407f0008900b6 0xb801fc00ee003fdf 0xbee007f003b800ff

def z629 : W := mkw 0xc39b373b90dedec2 0x7b0e6cdcee437b7b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z630 : W := mkw 0xffdfbc0000000000 0x87ff7ef000000000 0xfffffc0000000003 0xe7fffff000000000

def z631 : W := mkw 0x0100141a00420680 0x080400506801081a 0x0000303800000e08 0x000000c0e0000038

def z632 : W := mkw 0x3e6ecac56fb5f149 0x80f9bb2b15bed7c5 0xbfe7cfc7eff1f1f7 0xfeff9f3f1fbfc7c7

def z633 : W := mkw 0x18648ac544315041 0x0061922b1510c541 0xb8e7cfc70031c023 0xe6e39f3f1c00c700

def z634 : W := mkw 0xc901fc00b2402d90 0x172407f002c900b6 0xc001fc00f0003fdf 0x330007f003c000ff

def z635 : W := mkw 0xed01fc00b0002800 0x17b407f002c000a0 0xff01fc00f0003e1b 0xb7fc07f003c000f8

def z636 : W := mkw 0x030a140000c48480 0x000c285000031212 0x471e3c0011fffffe 0xf91c78f00047ffff

def z637 : W := mkw 0xc0016368b0123a02 0x3300058da2c048e8 0xc001f3f8f0003e1b 0x330007cfe3c000f8

def z638 : W := mkw 0x0020424160307040 0x000081090580c1c1 0x80e7cfc7e031f1f7 0xfa039f3f1f80c7c7

def z639 : W := mkw 0x1844888400000000 0x0061122210000000 0x38060c0700000000 0x84e018301c000000

def z640 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0x7f1e3c3f00000000 0x85fc78f0fc000000

def z641 : W := mkw 0x00000008900a0a02 0x5000000022402828 0x00000000100e0e08 0x0000000000403838

def z642 : W := mkw 0x0820cac566317141 0x0020832b1598c5c5 0x0001cfc7ee31f1f4 0x3800073f1fb8c7c7

def z643 : W := mkw 0x0b0bfe1b22d6ffd0 0x1c2c2ff86c8b5bff 0x471ffe3f11fffffe 0xf91c7ff8fc47ffff

def z644 : W := mkw 0x030a141200000000 0x000c285048000000 0x4718303800000000 0x011c60c0e0000000

def z645 : W := mkw 0xfffffffff0fefec6 0xffffffffffc3fbfb 0xfffffffff1ffffff 0xffffffffffc7ffff

def z646 : W := mkw 0x030a141a00c68680 0x080c285068031a1a 0x471e303811ffce2a 0xd91c78c0e047ff38

def z647 : W := mkw 0x0820ca4166317141 0x002083290598c5c5 0xb801cc00ee31f1f7 0xbee0073003b8c7c7

def z648 : W := mkw 0xe70b361b99d6ded0 0x1f9c2cd86e675b7b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z649 : W := mkw 0x1864c80066212100 0x0061932001988484 0xb8e7cc00ee31f1f7 0xfee39f3003b8c7c7

def z650 : W := mkw 0x364e00000d858008 0x80d9380000361600 0x7f1e00001fffc022 0xddfc7800007fff00

def z651 : W := mkw 0x0000000000000000 0x0000000000000000 0x4700000011c00002 0x991c000000470000

def z652 : W := mkw 0xf6fe02c5ddbdd049 0xc3dbf80b1776f741 0xfffe03c7ffffc023 0xdffff80f1fffff00

def z653 : W := mkw 0x2400000009000000 0x0090000000240000 0x3f0000000fc00000 0x8cfc0000003f0000

def z654 : W := mkw 0x0001212000000000 0x2000048480000000 0x0001f3f800000000 0x200007cfe0000000

def z655 : W := mkw 0xc2ba0000d0ac8000 0x430ae8000342b200 0xc7fe0000f1ffc023 0xdb1ff80003c7ff00

def z656 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x80f9c3f8e03e0001 0x4203e70fe380f800

def z657 : W := mkw 0x0800888502004141 0x0020022214080105 0x00000c07000001c4 0x000000301c000007

def z658 : W := mkw 0x260a000009848008 0x8098280000261200 0x0700000001c00000 0x001c000000070000

def z659 : W := mkw 0xffffbdb644ad800c 0xe7fffef6d912b600 0xffffffff003fc023 0xe7fffffffc00ff00

def z660 : W := mkw 0xe79b353200000004 0xa79e6cd4c8000000 0xc7f9f3f800000003 0x631fe7cfe0000000

def z661 : W := mkw 0x1844c88526016141 0x0061132214980585 0xb807cc07ee01f1f7 0xbee01f301fb807c7

def z662 : W := mkw 0xed01bc000b400590 0x07b406f0002d0016 0xff01fc000fc001c7 0xaffc07f0003f0007

def z663 : W := mkw 0x030a561bbbd6ffd0 0x180c29586eef5bff 0x471e3e3ffffffffe 0xf91c78f8ffffffff

def z664 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e1c1c0ee31f1f5 0x1ee3870703b8c7c7

def z665 : W := mkw 0xecb1eb68fb3a3b12 0x77b2c7ada3ece8ec 0xf8f9f3f8fe3e3e1b 0x77e3e7cfe3f8f8f8

def z666 : W := mkw 0xed21fc00ffedad98 0x57b487f003ffb6b6 0xff01fc00ffffffff 0xbffc07f003ffffff

def z667 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xb8fe0000ee3fc021 0x46e3f80003b8ff00

def z668 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x40183038f03e3e18 0x110060c0e3c0f8f8

def z669 : W := mkw 0x0000000800020200 0x0000000020000808 0x40183038100e0e08 0x010060c0e0403838

def z670 : W := mkw 0x1064020144315040 0x004190080510c541 0xb8e60e07ee31f1f7 0xfee398381fb8c7c7

def z671 : W := mkw 0x00000000998c8008 0x4000000002663200 0x0000000011ce0000 0x0000000000473800

def z672 : W := mkw 0xed01fe01bb507dd0 0x17b407f806ed41f7 0xff07fe07fff1ffff 0xfffc1ff81fffc7ff

def z673 : W := mkw 0xef0bfc1abbc6af90 0x1fbc2ff06aef1abe 0xff19fc38ffce3fdf 0xbffc67f0e3ff38ff

def z674 : W := mkw 0xfeffa9a4ddad800c 0xe7fbfea69376b600 0xffffc1c0ffffc023 0xdfffff0703ffff00

def z675 : W := mkw 0x366e00004da58008 0x80d9b80001369600 0xbfe60000eff1c023 0xdeff980003bfc700

def z676 : W := mkw 0x0101777b20527ec2 0x380405ddec8149fb 0x0001ffff00003fdc 0x200007fffc0000ff

def z677 : W := mkw 0x00200000dd290008 0x400080000374a400 0x00000000ee000000 0x0000000003b80000

def z678 : W := mkw 0xffdffdb6bb002914 0xb7ff7ff6daec00a4 0xffffffffee000003 0xe7ffffffffb80000

def z679 : W := mkw 0xfffededffffff7c9 0xcbfffb7b7fffffdf 0xffffffffffffffff 0xffffffffffffffff

def z680 : W := mkw 0x0000000000400480 0x0000000000010012 0x0000000011c03fdc 0x18000000004700ff

def z681 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e1cfc7ee0031d5 0x26e3873f1fb800c7

def z682 : W := mkw 0x00204248fdbfba0a 0x5000810923f6fee8 0x00000000fffffe38 0x1800000003fffff8

def z683 : W := mkw 0x124e000004858008 0x8049380000121600 0x000600000001c020 0x0000180000000700

def z684 : W := mkw 0xffffbffe403a1206 0xe7fffefff900e848 0xffffffff003e0003 0xe7fffffffc00f800

def z685 : W := mkw 0x2d009c0000000000 0x04b4027000000000 0x3f000c0000000000 0x84fc003000000000

def z686 : W := mkw 0x1965fec566717dd1 0x146597fb1599c5f7 0xb8e7ffc7ee31ffff 0xfee39fff1fb8c7ff

def z687 : W := mkw 0xf7de141200000000 0x83df785048000000 0xfffe3e3f00000003 0xe7fff8f8fc000000

def z688 : W := mkw 0xed009c009b400590 0x07b40270026d0016 0xff000c00ffc001c7 0x9ffc003003ff0007

def z689 : W := mkw 0xc0b16368fb7a3f92 0x7302c58da3ede8fe 0xc0f9f3f8fffe3fdf 0x7b03e7cfe3fff8ff

def z690 : W := mkw 0x1864c8c466212101 0x0061932311988484 0xb8e7cfc7ee000003 0xe6e39f3f1fb80000

def z691 : W := mkw 0x1864cac460303000 0x0061932b1180c0c0 0xb8e7cfc7e0303013 0xf6e39f3f1f80c0c0

def z692 : W := mkw 0xf6fe4248fdbfba0a 0xd3dbf90923f6fee8 0xfffe0000fffffe3b 0xdffff80003fffff8

def z693 : W := mkw 0x0000000106014141 0x0000000004180505 0x000000000e01c1e4 0x0800000000380707

def z694 : W := mkw 0xc0b00000d0280000 0x4302c0000340a000 0x80e00000e0000001 0x0203800003800000

def z695 : W := mkw 0x3f4e9c9600000004 0x84fd3a7258000000 0x7f1e3e3f00000002 0xe5fc78f8fc000000

def z696 : W := mkw 0xf7fe141addef8688 0xcbdff8506b77be1a 0xfffe3038ffffce2b 0xdffff8c0e3ffff38

def z697 : W := mkw 0x2c0088000b000110 0x04b00220002c0004 0x380000000e000000 0x04e0000000380000

def z698 : W := mkw 0xfdf5ffedff7b7fd3 0x77f7d7ffb7fdedff 0xffffffffffffffff 0xffffffffffffffff

def z699 : W := mkw 0xffdffdb622002104 0xa7ff7ff6d8880084 0xffffffffee0031d7 0xffffffffffb800c7

def z700 : W := mkw 0x022a0000ddad8008 0x4008a8000376b600 0x471e0000ffffc022 0xd91c780003ffff00

def z701 : W := mkw 0xed01fc0022002100 0x07b407f000880084 0xff01fc00ee0031d7 0xbffc07f003b800c7

def z702 : W := mkw 0xed91bd2000000000 0x27b646f480000000 0xfff9fff800000003 0xe7ffe7ffe0000000

def z703 : W := mkw 0x0000020100105040 0x0000000804004141 0x000000000031f1f4 0x180000000000c7c7

def z704 : W := mkw 0xecb1e960fb282912 0x77b2c7a583eca0a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z705 : W := mkw 0x0000000100c4c4c0 0x0800000004031313 0x0000000001c1c1e4 0x0800000000070707

def z706 : W := mkw 0xe5017400b9402c90 0x179405d002e500b2 0xc701f000f1c03e1b 0x331c07c003c700f8

def z707 : W := mkw 0xe4b16368f93a3a12 0x7792c58da3e4e8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z708 : W := mkw 0x1945bdb600000004 0x246516f6d8000000 0xb8e1ffff00000001 0x26e387fffc000000

def z709 : W := mkw 0x3f4e9c970dc5c4cc 0x8cfd3a725c371713 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z710 : W := mkw 0xf5f4161bdd7b56c8 0xcbd7d0586f75ed5b 0xb8e03e3fee003fdd 0x26e380f8ffb800ff

def z711 : W := mkw 0xffdfbdb602000104 0xa7ff7ef6d8080004 0xffffffff0e0001c7 0xeffffffffc380007

def z712 : W := mkw 0xf6ff21b6ddad800c 0xe3dbfc86db76b600 0xfffff3ffffffc023 0xffffffcfffffff00

def z713 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff103e0003 0xf7fffffffc40f800

def z714 : W := mkw 0x36fe0000ddad8008 0xc0dbf8000376b600 0x3ffe0000ffffc020 0xdcfff80003ffff00

def z715 : W := mkw 0x0901ff7b22527fd2 0x3c2407fdec8949ff 0x0001ffff00003fdc 0x200007fffc0000ff

def z716 : W := mkw 0x2d01fc002b402d90 0x14b407f000ad00b6 0xbf01fc00efc03fdf 0xbefc07f003bf00ff

def z717 : W := mkw 0x0991bdb600000004 0x242646f6d8000000 0x00f9ffff00000000 0x6003e7fffc000000

def z718 : W := mkw 0x364f63682d97ba0a 0xb0d93d8da0b65ee8 0x3f07f3f80fc1fe38 0xacfc1fcfe03f07f8

def z719 : W := mkw 0x00204249f6ffffc3 0x5800810927dbffff 0x00000000fffffffc 0x1800000003ffffff

def z720 : W := mkw 0xe4b16368f93a3a02 0x7392c58da3e4e8e8 0xf8f9f3f8fe3e3e1b 0x77e3e7cfe3f8f8f8

def z721 : W := mkw 0x1b6edcde66e7a781 0x086dbb73799b9e9e 0xfff9f1f8ffce0e09 0x07ffe7c7e3ff3838

def z722 : W := mkw 0xfedfa9b600000004 0xa7fb7ea6d8000000 0xffffc3ff00000003 0xc7ffff0ffc000000

def z723 : W := mkw 0xee9acac5bb9cf149 0xc3ba6b2b16ee73c5 0x4719cfc711ce31d4 0x211c673f1c4738c7

def z724 : W := mkw 0xc0b16368f93a3a02 0x7302c58da3e4e8e8 0xc0f9f3f8fffe3e1b 0x7b03e7cfe3fff8f8

def z725 : W := mkw 0x12fe03ff44bfd243 0x684bf80ffd12ff49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z726 : W := mkw 0xe4b16368f93a3a02 0x7392c58da3e4e8e8 0xc7f9f3f8f1fe3e1b 0x731fe7cfe3c7f8f8

def z727 : W := mkw 0xe79b353a99ce8e8a 0xfb9e6cd4ea673a3a 0x4718303811ce0e08 0x011c60c0e0473838

def z728 : W := mkw 0x12de41b6bb402d94 0xb04b7906daed00b6 0x00fe03ffffc03fdc 0x5803f80fffff00ff

def z729 : W := mkw 0xf6ff2000ddad8008 0xc3dbfc800376b600 0xfffff000ffffc023 0xffffffc003ffff00

def z730 : W := mkw 0x3f6ededef03a3a06 0xd4fdbb7b7bc0e8e8 0x3f060c07f03e3e18 0x94fc18301fc0f8f8

def z731 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0f9f3f8f03e0e09 0x4303e7cfe3c0f838

def z732 : W := mkw 0xef9bbd3200000000 0x27be6ef4c8000000 0xffffffff00000003 0xe7fffffffc000000

def z733 : W := mkw 0x00204249fdfffeca 0x5800810927f7fffb 0x00000000fffffffc 0x1800000003ffffff

def z734 : W := mkw 0x1bfffc0066edad98 0xd46ffff0019bb6b6 0x00fffc00003ffffc 0x6003fff00000ffff

def z735 : W := mkw 0xf56536c5dd715cd1 0x17d594db1775c573 0x47e633c711f1ce28 0x411f98cf1c47c738

def z736 : W := mkw 0xffdfbdb609400494 0xa7ff7ef6d8250012 0xffffffff01c00003 0xe7fffffffc070000

def z737 : W := mkw 0xffdfbdb699000004 0xa7ff7ef6da640000 0xffffffff11c00003 0xe7fffffffc470000

def z738 : W := mkw 0xff4fbc9600000000 0x07fd3ef258000000 0xffffffff00000003 0xe7fffffffc000000

def z739 : W := mkw 0xffdfbdb69b400594 0xa7ff7ef6da6d0016 0xffffffffffc001c7 0xffffffffffff0007

def z740 : W := mkw 0xc3bb7573f0ececc2 0x7b0eedd5cfc3b3b3 0x87e7cdc7e1c1c1e5 0x8a1f9f371f870707

def z741 : W := mkw 0x24200000ddad8008 0x409080000376b600 0x3f000000ffffc020 0x9cfc000003ffff00

def z742 : W := mkw 0xed91fc00bb482d98 0xd7b647f002ed20b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z743 : W := mkw 0xffdfbdb699400484 0xa7ff7ef6da650012 0xffffffffffc03fdf 0xffffffffffff00ff

def z744 : W := mkw 0x1adfa9b600000004 0xa46b7ea6d8000000 0x00ffc3ff00000000 0x4003ff0ffc000000

def z745 : W := mkw 0xf66e0000ddad8008 0xc3d9b8000376b600 0xff060000ffffc023 0x9ffc180003ffff00

def z746 : W := mkw 0x1bde9db600000004 0xa06f7a76d8000000 0xffffffff00000003 0xe7fffffffc000000

def z747 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x80f9f3f8e03e3e19 0x6203e7cfe380f8f8

def z748 : W := mkw 0xc29b213200000000 0x230a6c84c8000000 0xc0fff3ff00000003 0x6303ffcffc000000

def z749 : W := mkw 0x2db09f684b7a1792 0x64b6c27da12de85e 0x3ff80ff80ffe01c4 0xccffe03fe03ff807

def z750 : W := mkw 0x0921bdb6ddad800c 0x642486f6db76b600 0x0001ffffffffc020 0x380007ffffffff00

def z751 : W := mkw 0xe501340099400c90 0x179404d002650032 0xff003c00ffc03fdf 0xbffc00f003ff00ff

def z752 : W := mkw 0xee0bea1bbb96fb50 0x1fb82fa86eee5bed 0xb81fc23fee3fc021 0x46e07f08ffb8ff00

def z753 : W := mkw 0x1845a9a400000000 0x206116a690000000 0xb8e7ffff00000003 0xe6e39ffffc000000

def z754 : W := mkw 0xc09121b600000004 0x23024486d8000000 0xc0f9f3ff00000003 0x6303e7cffc000000

def z755 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xf8e7ffc7fe31ffff 0xffe39fff1ff8c7ff

def z756 : W := mkw 0xf6fe0132ddad800c 0xe3dbf804cb76b600 0xfffe0038ffffc023 0xdffff800e3ffff00

def z757 : W := mkw 0xed91bdb600000004 0x27b646f6d8000000 0xfff9ffff00000003 0xe7ffe7fffc000000

def z758 : W := mkw 0xc0b16368fb3a3b12 0x7302c58da3ece8ec 0xc0f9f3f8fe3e3e1b 0x7303e7cfe3f8f8f8

def z759 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xfffff3ff00000001 0x47ffffcffc000000

def z760 : W := mkw 0xed01fc84bb402d90 0x17b407f212ed00b6 0xff01ffc7ffc03fdf 0xbffc07ff1fff00ff

def z761 : W := mkw 0xffdfbdb699848004 0xa7ff7ef6da661200 0xffffffffffffc023 0xffffffffffffff00

def z762 : W := mkw 0xc0b12368403a1202 0x6302c48da100e848 0xc0f9f3f8103e3e1b 0x7303e7cfe040f8f8

def z763 : W := mkw 0xe4b16368f03a3a06 0xf792c58da3c0e8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z764 : W := mkw 0xfcf5e9e4ff292913 0x77f3d7a793fca4a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z765 : W := mkw 0xfcd5abad00d6d6c4 0xaff356aeb4035b5b 0xb8e1c1c011fffffd 0x1ee387070047ffff

def z766 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x471e3c3f11fffffc 0x991c78f0fc47ffff

def z767 : W := mkw 0xdbdfbdb600000000 0x236f7ef6d8000000 0xffffffff00000003 0xe7fffffffc000000

def z768 : W := mkw 0x032a565360f4f4c0 0x080ca9594d83d3d3 0x87e7cfc7e1f1f1f7 0xfa1f9f3f1f87c7c7

def z769 : W := mkw 0x0900dc00bb402d90 0x1024037002ed00b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z770 : W := mkw 0xe6ba0000ddad8008 0xc39ae8000376b600 0xff180000ffffc023 0x9ffc600003ffff00

def z771 : W := mkw 0xe7bb777366317145 0xa79eedddcd98c5c5 0x47183038ee31f1f4 0x191c60c0e3b8c7c7

def z772 : W := mkw 0xf6ff2120ddad800c 0xe7dbfc848376b600 0xfffe0000ffffc023 0xdffff80003ffff00

def z773 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff07fc00fff1ffff 0xfffc1ff003ffc7ff

def z774 : W := mkw 0xffdfbdb69908000c 0xe7ff7ef6da642000 0xffffffff00000003 0xe7fffffffc000000

def z775 : W := mkw 0x3f4e9c970bc4c5d4 0x8cfd3a725c2f1317 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z776 : W := mkw 0x01001609005256c0 0x000400582401495b 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z777 : W := mkw 0x00204249ffbffb4b 0x5000810927feffed 0x00000000fffffffc 0x1800000003ffffff

def z778 : W := mkw 0xf6fe00c4ddad8009 0xc3dbf8031376b600 0xfffe01c0ffffc023 0xdffff80703ffff00

def z779 : W := mkw 0xfede89b600000004 0xa3fb7a26d8000000 0xffffcfff00000003 0xe7ffff3ffc000000

def z780 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xf8ffcfc7fe3ff1f7 0xffe3ff3f1ff8ffc7

def z781 : W := mkw 0xf6de000099848000 0x83db780002661200 0xfffe0000ffffc023 0xdffff80003ffff00

def z782 : W := mkw 0xffdfbdb606010105 0xa7ff7ef6d8180404 0xffffffff0e000003 0xe7fffffffc380000

def z783 : W := mkw 0xc0b16368fd3b3a0a 0x7302c58da3f4ece8 0xc0f9f3f8fe3e3e1b 0x7303e7cfe3f8f8f8

def z784 : W := mkw 0x18d489a400000000 0x2063522690000000 0xb8ffcfff00000003 0xe6e3ff3ffc000000

def z785 : W := mkw 0x0901ffff22527fc3 0x382407fffc8949ff 0x0001ffff00003fdc 0x200007fffc0000ff

def z786 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xbf01cc00ffc03fdd 0x9efc073003ff00ff

def z787 : W := mkw 0x184489b600000004 0x20611226d8000000 0xb8e7cfff00000003 0xe6e39f3ffc000000

def z788 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0x7f003c00ffc03fdc 0x9dfc00f003ff00ff

def z789 : W := mkw 0x0020424960f6f6c0 0x080081092583dbdb 0x00000000f1fffffc 0x1800000003c7ffff

def z790 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0f9f3f8f00e3e19 0x2303e7cfe3c038f8

def z791 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7cfc7ee31f1f5 0x66e39f3f1fb8c7c7

def z792 : W := mkw 0x24004000bb402d90 0x1090010002ed00b6 0x3f000000ffc03fdc 0x9cfc000003ff00ff

def z793 : W := mkw 0xffdfbdb690080806 0xf7ff7ef6da402020 0xffffffff00000003 0xe7fffffffc000000

def z794 : W := mkw 0x00204248f03a3a02 0x5000810923c0e8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z795 : W := mkw 0xf6ff2120ddad8008 0xe3dbfc848376b600 0xfffe3038ffffc023 0xdffff8c0e3ffff00

def z796 : W := mkw 0xfdd5bdb600000004 0xa7f756f6d8000000 0xf8f9ffff00000003 0x67e3e7fffc000000

def z797 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff0031c023 0xfffffffffc00c700

def z798 : W := mkw 0x0900de1b225277c0 0x082403786c8949df 0x0001fe3f00003fdc 0x200007f8fc0000ff

def z799 : W := mkw 0xe79b353a99ce8e92 0x7f9e6cd4ea673a3a 0x4718303811ce0e08 0x011c60c0e0473838

def z800 : W := mkw 0x0000020800121200 0x0000000820004848 0xc0f9f3f8103e3e1b 0x7303e7cfe040f8f8

def z801 : W := mkw 0xed91fdb6bb402d94 0x37b647f6daed00b6 0xfff9ffffffc03fdf 0xffffe7ffffff00ff

def z802 : W := mkw 0xed01fd20bb402d90 0x37b407f482ed00b6 0xff01fff8ffc03fdf 0xbffc07ffe3ff00ff

def z803 : W := mkw 0xed00dc00bb402d90 0x17b4037002ed00b6 0xff000c00ffc03fdf 0x9ffc003003ff00ff

def z804 : W := mkw 0xd8d5a9ad960b4b43 0x736356a6b6582d2d 0x781e3c3f1e0fcfec 0x8de078f0fc783f3f

def z805 : W := mkw 0xed91fc00bb482d90 0x57b647f002ed20b6 0xff19fc00ffce3fdf 0xbffc67f003ff38ff

def z806 : W := mkw 0x3f4e9c970fc5c5c9 0x88fd3a725c3f1717 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z807 : W := mkw 0x0020424966337b43 0x100081092598cded 0x00000000ee31fffc 0x1800000003b8c7ff

def z808 : W := mkw 0x18448a8d06135341 0x0061122a34184d4d 0x781e3e3f1e3ffffe 0xfde078f8fc78ffff

def z809 : W := mkw 0xffdfbdb69d85800c 0xa7ff7ef6da761600 0xffffffffffc1c023 0xffffffffffff0700

def z810 : W := mkw 0xed01fd60bb402d92 0x37b407f582ed00b6 0xff01fdc0ffc03fdf 0xbffc07f703ff00ff

def z811 : W := mkw 0x030a141200c48480 0x000c285048031212 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z812 : W := mkw 0xf7df353200000000 0xa3df7cd4c8000000 0xffffffff00000003 0xe7fffffffc000000

def z813 : W := mkw 0x1844888400000000 0x0061122210000000 0xf8ffffff00000003 0xe7e3fffffc000000

def z814 : W := mkw 0xc0b16168f02a2a02 0x7302c585a3c0a8a8 0xc0f9f3f8f00e0e0b 0x6303e7cfe3c03838

def z815 : W := mkw 0xffdfbdb609000004 0xa7ff7ef6d8240000 0xffffffff0fc00003 0xeffffffffc3f0000

def z816 : W := mkw 0x12df21b600000004 0xa04b7c86d8000000 0x00fff3ff00000000 0x6003ffcffc000000

def z817 : W := mkw 0x1864cacd663b7343 0x4061932b3598edcd 0xb8e7cfc7ee3ff1f7 0xfee39f3f1fb8ffc7

def z818 : W := mkw 0x00b04368603a3202 0x6002c10da180e8c8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z819 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe0c00fffff1f7 0xfffff83003ffffc7

def z820 : W := mkw 0xc901fc00b2402d80 0x132407f002c900b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z821 : W := mkw 0xed01fcc4bb402d91 0x17b407f312ed00b6 0xff01fdc0ffc03fdf 0xbffc07f703ff00ff

def z822 : W := mkw 0xe62a0000ddad8008 0x4398a8000376b600 0xff1e0000ffffc023 0xdffc780003ffff00

def z823 : W := mkw 0xdadfa9b600000004 0xa36b7ea6d8000000 0xf8ffffff00000003 0xe7e3fffffc000000

def z824 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0fff3f8f03ffe3b 0xfb03ffcfe3c0fff8

def z825 : W := mkw 0xc0b1636860323200 0x2302c58da180c8c8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z826 : W := mkw 0x12fe037b44bfd24a 0xe84bf80ded12ff49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z827 : W := mkw 0xc0b16369f63b7b43 0x7302c58da7d8eded 0xc0fffffffe3fffff 0xfb03fffffff8ffff

def z828 : W := mkw 0xc0b16368f43b3a02 0x7302c58da3d0ece8 0xc0f9f3f8fe3ffe3b 0x7b03e7cfe3f8fff8

def z829 : W := mkw 0x0901fedf22527fd1 0x1c2407fb7c8949ff 0x0001ffff00003fdc 0x200007fffc0000ff

def z830 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0xff1e3e3fffffffff 0xfffc78f8ffffffff

def z831 : W := mkw 0xfdd5bdb600000004 0xa7f756f6d8000000 0xffe1ffff00000003 0xa7ff87fffc000000

def z832 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff19fe38ffc03fdf 0xfffc67f8e3ff00ff

def z833 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xbf01fc00efc03fdd 0xaefc07f003bf00ff

def z834 : W := mkw 0xf64e00009d858008 0x83d9380002761600 0xff1e0000ffffc023 0xdffc780003ffff00

def z835 : W := mkw 0xfedfa9a400000000 0xa3fb7ea690000000 0xffffffff00000003 0xe7fffffffc000000

def z836 : W := mkw 0x12fe03ff44b7d245 0xa84bf80ffd12df49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z837 : W := mkw 0xf7df35b600000004 0xa7df7cd6d8000000 0xc7fff3ff00000003 0x631fffcffc000000

def z838 : W := mkw 0x19d5bdb600000004 0xa46756f6d8000000 0x00e1ffff00000000 0x200387fffc000000

def z839 : W := mkw 0x2d00dc00bb402d90 0x14b4037002ed00b6 0x7f003c00ffc03fde 0xbdfc00f003ff00ff

def z840 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xffe1ffc0ffc03fdf 0xffff87ff03ff00ff

def z841 : W := mkw 0xed01fc0022402580 0x07b407f000890096 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z842 : W := mkw 0xf4640000ddad8008 0x43d190000376b600 0xffe60000ffffc023 0xdfff980003ffff00

def z843 : W := mkw 0xc0b16369f23a7b43 0x7302c58da7c8e9ed 0xc0f9f3f8f03e3fdf 0x7303e7cfe3c0f8ff

def z844 : W := mkw 0xc091212000000000 0x2302448480000000 0xc0ffffff00000003 0xe303fffffc000000

def z845 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0f9fff8f03e3fdf 0xfb03e7ffe3c0f8ff

def z846 : W := mkw 0xfedfa9b600000004 0xa7fb7ea6d8000000 0xf8fff3ff00000003 0x67e3ffcffc000000

def z847 : W := mkw 0xffdfbdb604010004 0xa7ff7ef6d8100400 0xffffffff0e01c023 0xeffffffffc380700

def z848 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xf8f9f3f8fe3e3e1b 0xffe3e7cfe3f8f8f8

def z849 : W := mkw 0xed91fd20bb402d94 0xb7b647f482ed00b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z850 : W := mkw 0xe4b16368f03a3a02 0x7392c58da3c0e8e8 0xfff9f3f8f03e3e1b 0xf7ffe7cfe3c0f8f8

def z851 : W := mkw 0xc0b12328d03a1200 0x6302c48ca340e848 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z852 : W := mkw 0xed01fda4bb402d94 0x37b407f692ed00b6 0xff01fdc0ffc03fdf 0xbffc07f703ff00ff

def z853 : W := mkw 0xc091636820123a02 0x3302458da08048e8 0xc0f9f3f8103e3e1b 0x7303e7cfe040f8f8

def z854 : W := mkw 0xf6fe0084ddad8008 0xc3dbf8021376b600 0xfffe03c7ffffc023 0xdffff80f1fffff00

def z855 : W := mkw 0xc0b16368603a3a02 0x7302c58da180e8e8 0xc0f9f3f8003e3e1b 0x6303e7cfe000f8f8

def z856 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xbfffcfff00000001 0xc6ffff3ffc000000

def z857 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0fffffff03e3e1b 0xf303ffffffc0f8f8

def z858 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfff80000ffffc021 0x1fffe00003ffff00

def z859 : W := mkw 0xffdfbdb6998c800c 0xe7ff7ef6da663200 0xffffffff11ffc023 0xfffffffffc47ff00

def z860 : W := mkw 0x0901bdb600000004 0x242406f6d8000000 0x80e1ffff00000003 0x620387fffc000000

def z861 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc0f9f1f8f03e3e19 0x1303e7c7e3c0f8f8

def z862 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff01f000ffc03fdd 0x1ffc07c003ff00ff

def z863 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0xc7f9f3f8f1fe3e1b 0xfb1fe7cfe3c7f8f8

def z864 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xfff9ffff00000001 0x27ffe7fffc000000

def z865 : W := mkw 0x3f4e9c960fc5859c 0x84fd3a72583f1616 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z866 : W := mkw 0xf6ff2120ddad8008 0xe3dbfc848376b600 0xffffc1c0ffffc023 0xdfffff0703ffff00

def z867 : W := mkw 0xffdfbdb690000804 0xb7ff7ef6da400020 0xffffffff10000e0b 0xe7fffffffc400038

def z868 : W := mkw 0xffdfbdb600400c94 0xb7ff7ef6d8010032 0xffffffff00000e0b 0xe7fffffffc000038

def z869 : W := mkw 0x00b16368603a3a02 0x7002c58da180e8e8 0x40f9f3f8103e3e1a 0x7103e7cfe040f8f8

def z870 : W := mkw 0xffde9c9600000000 0x83ff7a7258000000 0xffffffff00000003 0xe7fffffffc000000

def z871 : W := mkw 0xcb9bbdb600000004 0x272e6ef6d8000000 0xc7ffffff00000003 0xe31ffffffc000000

def z872 : W := mkw 0x1b4e9c9700c4c4c0 0x086d3a725c031313 0x3f060c0701c1c1e4 0x8cfc18301c070707

def z873 : W := mkw 0xd9d5bdb600000004 0x276756f6d8000000 0xf8ffffff00000003 0xe7e3fffffc000000

def z874 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe3238ffffc023 0xfffff8c8e3ffff00

def z875 : W := mkw 0xd0d521a400000000 0x2343548690000000 0xc0fff3ff00000003 0x6303ffcffc000000

def z876 : W := mkw 0x0901fe0922527fd0 0x1c2407f8248949ff 0x0001fc0000003fdc 0x200007f0000000ff

def z877 : W := mkw 0xc0b16120f0282800 0x7302c58483c0a0a0 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z878 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe0e07ffffc023 0xfffff8381fffff00

def z879 : W := mkw 0xc0912328901a1a02 0x7302448ca2406868 0xc0f9f3f8103e3e1b 0x7303e7cfe040f8f8

def z880 : W := mkw 0x1b4fbdb600000004 0x246d3ef6d8000000 0xffffffff00000003 0xe7fffffffc000000

def z881 : W := mkw 0x36fe00004dad8008 0xc0dbf8000136b600 0xbffe0000efffc023 0xdefff80003bfff00

def z882 : W := mkw 0x0820ca4162307140 0x002083290588c1c5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z883 : W := mkw 0x030a141200000000 0x000c285048000000 0xc7ffffff00000003 0xe31ffffffc000000

def z884 : W := mkw 0xc0b16168f02a2a02 0x7302c585a3c0a8a8 0xc0f9f1f8f03e0e0b 0x5303e7c7e3c0f838

def z885 : W := mkw 0x1864c8c566216141 0x0061932315988585 0xb8e7cdc7ee01f1f7 0xbee39f371fb807c7

def z886 : W := mkw 0xfcd5a9a400000004 0xa7f356a690000000 0xf8ffffff00000003 0xe7e3fffffc000000

def z887 : W := mkw 0xffdfbdb600848004 0xa7ff7ef6d8021200 0xffffffff01c1c023 0xeffffffffc070700

def z888 : W := mkw 0x00204249f03a7a42 0x5000810927c0e9e9 0x00000000f03ffffc 0x1800000003c0ffff

def z889 : W := mkw 0x12fe000044ad8008 0xc04bf8000112b600 0xfffe0000ffffc023 0xdffff80003ffff00

def z890 : W := mkw 0x1ade89b600000004 0xa06b7a26d8000000 0xb8ffc3ff00000001 0x46e3ff0ffc000000

def z891 : W := mkw 0x020a000000848000 0x0008280000021200 0xff1e0000ffffc023 0xdffc780003ffff00

def z892 : W := mkw 0xfcf5e9e4ff29290b 0xf3f3d7a793fca4a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z893 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0x47ffffff00000000 0x611ffffffc000000

def z894 : W := mkw 0xffdfbdb699000814 0xb7ff7ef6da640020 0xffffffff00000003 0xe7fffffffc000000

def z895 : W := mkw 0xffdfbdb699400c94 0xb7ff7ef6da650032 0xffffffff11c03fdf 0xfffffffffc4700ff

def z896 : W := mkw 0x0100140000400480 0x0004005000010012 0xff003c00ffc03fdf 0xbffc00f003ff00ff

def z897 : W := mkw 0xffdfbdb600848004 0xa7ff7ef6d8021200 0xffffffff11ce0003 0xe7fffffffc473800

def z898 : W := mkw 0xc991bdb600000004 0x272646f6d8000000 0x80e1ffff00000001 0x220387fffc000000

def z899 : W := mkw 0xffdfbdb60fc5859c 0xa7ff7ef6d83f1616 0xffffffff0fc1c1e7 0xeffffffffc3f0707

def z900 : W := mkw 0x00204249fbfeffd2 0x5800810927effbff 0x00000000fffffffc 0x1800000003ffffff

def z901 : W := mkw 0xe4b16368f93a3a0a 0xf392c58da3e4e8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z902 : W := mkw 0x00204249f0befa42 0x5800810927c2fbe9 0x00000000f03ffe38 0x1000000003c0fff8

def z903 : W := mkw 0xffdfbdb690000004 0xa7ff7ef6da400000 0xfffffffff0000003 0xf7ffffffffc00000

def z904 : W := mkw 0x2d01fc00bb402d90 0x14b407f002ed00b6 0x3f01fc00ffc03fdc 0xbcfc07f003ff00ff

def z905 : W := mkw 0xf6fe01a4ddad800c 0xe3dbf8069376b600 0xfffe01c0ffffc023 0xdffff80703ffff00

def z906 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff000031d7 0xfffffffffc0000c7

def z907 : W := mkw 0x0020424966337341 0x000081092598cdcd 0x00000000fe3ffffc 0x1800000003f8ffff

def z908 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff07fe07ffc03fdf 0xfffc1ff81fff00ff

def z909 : W := mkw 0xd3df35b600000004 0xa34f7cd6d8000000 0xc7ffffff00000003 0xe31ffffffc000000

def z910 : W := mkw 0xffdfbdb69d8d800c 0xe7ff7ef6da763600 0xffffffff1fcfc023 0xeffffffffc7f3f00

def z911 : W := mkw 0xc0b16369f43b7a43 0x7302c58da7d0ede9 0xc0f9f3f8f03ffe3b 0x7303e7cfe3c0fff8

def z912 : W := mkw 0xf4f40000ddad8008 0xc3d3d0000376b600 0xffe00000ffffc023 0x9fff800003ffff00

def z913 : W := mkw 0xfd45bdb600000004 0x27f516f6d8000000 0xffe7ffff00000003 0xe7ff9ffffc000000

def z914 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xbffe0000efffc021 0xcefff80003bfff00

def z915 : W := mkw 0xe5017400bb402d90 0x179405d002ed00b6 0xff003000ffc03fdf 0x9ffc00c003ff00ff

def z916 : W := mkw 0x1864c88466212100 0x0061932211988484 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z917 : W := mkw 0xc0216248f0323a00 0x1300858923c0c8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z918 : W := mkw 0xed01fc12bb402d90 0x17b407f04aed00b6 0xff01fe3fffc03fdf 0xbffc07f8ffff00ff

def z919 : W := mkw 0x1ade89b600000004 0xa06b7a26d8000000 0x00ffcfff00000000 0x6003ff3ffc000000

def z920 : W := mkw 0xf6fe0120ddad8008 0xe3dbf8048376b600 0xfffe03f8ffffc023 0xdffff80fe3ffff00

def z921 : W := mkw 0xffdfbdb600c48484 0xafff7ef6d8031212 0xffffffff01c00003 0xe7fffffffc070000

def z922 : W := mkw 0xc091212800020200 0x23024484a0000808 0xc0f9f3f8100e0e0b 0x6303e7cfe0403838

def z923 : W := mkw 0xffdfbdb600400484 0xa7ff7ef6d8010012 0xffffffff00003fdf 0xe7fffffffc0000ff

def z924 : W := mkw 0x00b16368603a3a02 0x7002c58da180e8e8 0x80f9f3f8e03e3e1b 0x7203e7cfe380f8f8

def z925 : W := mkw 0x0901ffff225277c5 0x2c2407fffc8949df 0x0001ffff00003fdc 0x200007fffc0000ff

def z926 : W := mkw 0x00204249f07a7ec2 0x5800810927c1e9fb 0x00000000f03e3fdc 0x1000000003c0f8ff

def z927 : W := mkw 0x0901ffbf22527fd4 0x3c2407fefc8949ff 0x0001ffff00003fdc 0x200007fffc0000ff

def z928 : W := mkw 0xec01e800bb402d90 0x17b007a002ed00b6 0xff01c000ffc03fdf 0x9ffc070003ff00ff

def z929 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe0000ffffc021 0x47fff80003ffff00

def z930 : W := mkw 0xffdfbdb699cc8c9c 0xf7ff7ef6da673232 0xffffffff11ce0e0b 0xe7fffffffc473838

def z931 : W := mkw 0xfcd5a9b600000004 0xa7f356a6d8000000 0xb8e1c3ff00000001 0x06e3870ffc000000

def z932 : W := mkw 0xed00dc00bb402580 0x03b4037002ed0096 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z933 : W := mkw 0xf6fe000044a58000 0x83dbf80001129600 0xfffe0000ffffc023 0xdffff80003ffff00

def z934 : W := mkw 0xc0b16369f03a7a42 0x7302c58da7c0e9e9 0xc0f9f3f8f03fffff 0x7b03e7cfe3c0ffff

def z935 : W := mkw 0xffdfbdb60b000114 0xa7ff7ef6d82c0004 0xffffffff0e000003 0xe7fffffffc380000

def z936 : W := mkw 0xffdfbdb60b400594 0xa7ff7ef6d82d0016 0xffffffff1fc03fdf 0xfffffffffc7f00ff

def z937 : W := mkw 0xf4f40000dd290000 0x43d3d0000374a400 0xfffe0000ffffc023 0xdffff80003ffff00

def z938 : W := mkw 0x00204249ff7b7fd3 0x5000810927fdedff 0x00000000fffffffc 0x1800000003ffffff

def z939 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0x471e3e3f11fffffc 0x611c78f8fc47ffff

def z940 : W := mkw 0xe5005400bb402d90 0x1394015002ed00b6 0xff003c00ffc03fdf 0xbffc00f003ff00ff

def z941 : W := mkw 0xffdfbdb6008c800c 0xe7ff7ef6d8023200 0xffffffff000e0003 0xe7fffffffc003800

def z942 : W := mkw 0xf6ff2000ddad8818 0xd7dbfc800376b620 0xfffe0000ffffc023 0xdffff80003ffff00

def z943 : W := mkw 0x00204249f43b7a43 0x5000810927d0ede9 0x00000000f03ffe38 0x1000000003c0fff8

def z944 : W := mkw 0xe79b353200000004 0xa79e6cd4c8000000 0xc7ffffff00000003 0xe31ffffffc000000

def z945 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff19fc00fffe3fdf 0xfffc67f003fff8ff

def z946 : W := mkw 0x19449c9600000000 0x0065127258000000 0xb8e7ffff00000003 0xe6e39ffffc000000

def z947 : W := mkw 0x2d00dc002b402590 0x04b4037000ad0096 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z948 : W := mkw 0x12fe02df44bfd249 0xc84bf80b7d12ff49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z949 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xffffc3c0ffffc023 0xffffff0f03ffff00

def z950 : W := mkw 0x3f4fbdb600000004 0xa4fd3ef6d8000000 0xbfe7ffff00000003 0xe6ff9ffffc000000

def z951 : W := mkw 0xc0b16369f03a7a42 0x7302c58da7c0e9e9 0xc0fff3fff03ffe3b 0x7303ffcfffc0fff8

def z952 : W := mkw 0x00204249fffff7c9 0x4800810927ffffdf 0x00000000fffffffc 0x1800000003ffffff

def z953 : W := mkw 0xfedfa9b600000004 0xa7fb7ea6d8000000 0xb8ffcfff00000003 0xe6e3ff3ffc000000

def z954 : W := mkw 0xc891a9a400000000 0x232246a690000000 0xc0f9ffff00000003 0x6303e7fffc000000

def z955 : W := mkw 0xf6fe0096ddad800c 0xc3dbf8025b76b600 0xfffe0007ffffc023 0xdffff8001fffff00

def z956 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7cdc7ee31f1f5 0x9ee39f371fb8c7c7

def z957 : W := mkw 0xc0916328b0123a00 0x3302458ca2c048e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z958 : W := mkw 0xc0912128900a0a02 0x73024484a2402828 0xc0f9f1f8100e0e09 0x0303e7c7e0403838

def z959 : W := mkw 0xfdd5bdb600000004 0xa7f756f6d8000000 0xb8e7ffff00000003 0xe6e39ffffc000000

def z960 : W := mkw 0xe79b353a99c68e94 0xbf9e6cd4ea671a3a 0x4718303811ce0e08 0x011c60c0e0473838

def z961 : W := mkw 0xef9bbdb600000004 0xa7be6ef6d8000000 0xc7f9ffff00000003 0x631fe7fffc000000

def z962 : W := mkw 0x1864cacd66337341 0x0061932b3598cdcd 0xb8e7ffffee31ffff 0xfee39fffffb8c7ff

def z963 : W := mkw 0x1864888546214141 0x0061922215188505 0xb8e7cfc7ee31c1e7 0xfee39f3f1fb8c707

def z964 : W := mkw 0x00204249fff7ffd1 0x1800810927ffdfff 0x00000000fffffffc 0x1800000003ffffff

def z965 : W := mkw 0x0901fc0022402d90 0x142407f0008900b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z966 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7cfc7ee01f1f5 0xaee39f3f1fb807c7

def z967 : W := mkw 0x0901ffed22527fd3 0x342407ffb48949ff 0x0001ffff00003fdc 0x200007fffc0000ff

def z968 : W := mkw 0xed91fd20bb402d90 0x37b647f482ed00b6 0xff19fc38ffc03fdf 0xbffc67f0e3ff00ff

def z969 : W := mkw 0x3f4e9c9600c48484 0x8cfd3a7258031212 0x3f060c0701c00000 0x84fc18301c070000

def z970 : W := mkw 0xffdfbdb600400484 0xa7ff7ef6d8010012 0xffffffff01c001c7 0xeffffffffc070007

def z971 : W := mkw 0xe4b00000ddad8008 0x4392c0000376b600 0xfff80000ffffc023 0xdfffe00003ffff00

def z972 : W := mkw 0xc0b16369f03a7a42 0x7302c58da7c0e9e9 0xc0f9fffff03e3fdf 0x7303e7ffffc0f8ff

def z973 : W := mkw 0xed91fd20bb402d90 0x37b647f482ed00b6 0xffe1fdc0ffc03fdf 0xbfff87f703ff00ff

def z974 : W := mkw 0xf6fe0012ddad8008 0xc3dbf8004b76b600 0xfffe023fffffc023 0xdffff808ffffff00

def z975 : W := mkw 0x00204249f23a7b43 0x5000810927c8e9ed 0x00000000f03e3fdc 0x1000000003c0f8ff

def z976 : W := mkw 0xed01fc96bb402d94 0x17b407f25aed00b6 0xff01fc07ffc03fdf 0xbffc07f01fff00ff

def z977 : W := mkw 0xed91fd20bb482d92 0x77b647f482ed20b6 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z978 : W := mkw 0x2d00dc00bb402d90 0x14b4037002ed00b6 0xbf01cc00ffc03fdf 0xbefc073003ff00ff

def z979 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xfffe3000fffffe3b 0xfffff8c003fffff8

def z980 : W := mkw 0xc0b04248f03a3200 0x4302c10923c0e8c8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z981 : W := mkw 0xf66e0000dda58000 0x03d9b80003769600 0xfffe0000ffffc023 0xdffff80003ffff00

def z982 : W := mkw 0xffdfbdb699400c94 0xb7ff7ef6da650032 0xffffffffffc00e0b 0xffffffffffff0038

def z983 : W := mkw 0x3f4e9c970fc5c5d1 0x0cfd3a725c3f1717 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z984 : W := mkw 0x1064424164317040 0x004191090590c5c1 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z985 : W := mkw 0x366e0000ddad8008 0xc0d9b8000376b600 0x7f1e0000ffffc022 0xddfc780003ffff00

def z986 : W := mkw 0x3fdfbdb600000004 0xa4ff7ef6d8000000 0x3fffffff00000000 0xe4fffffffc000000

def z987 : W := mkw 0x18648a8544315040 0x0061922a1510c541 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z988 : W := mkw 0x12fe03ed44bfd24b 0xe04bf80fb512ff49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z989 : W := mkw 0xffdfbdb60d85800c 0xa7ff7ef6d8361600 0xffffffff1fffc023 0xfffffffffc7fff00

def z990 : W := mkw 0x1a4e889600000000 0x00693a2258000000 0xb8ffcfff00000003 0xe6e3ff3ffc000000

def z991 : W := mkw 0x00204249667377c1 0x080081092599cddf 0x00000000ee31fffc 0x1800000003b8c7ff

def z992 : W := mkw 0x1864c8c566216141 0x0061932315988585 0xb8e7cdc7ee31c1e7 0xdee39f371fb8c707

def z993 : W := mkw 0x020a02090096d240 0x0008280824025b49 0x471e3e3f11fffffe 0xf91c78f8fc47ffff

def z994 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xb8ffffff00000001 0x66e3fffffc000000

def z995 : W := mkw 0xe79b353a99ce868c 0xef9e6cd4ea673a1a 0x4718303811ce0e08 0x011c60c0e0473838

def z996 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffffee000003 0xffffffffffb80000

def z997 : W := mkw 0xffdfbdb602400594 0xa7ff7ef6d8090016 0xffffffff000001c7 0xe7fffffffc000007

def z998 : W := mkw 0x1864cacd66337341 0x0061932b3598cdcd 0xb8ffcfffee3ff1f7 0xfee3ff3fffb8ffc7

def z999 : W := mkw 0x1844ca8522107140 0x0061132a148841c5 0xb8e7cfc7ee31f1f7 0xfee39f3f1fb8c7c7

def z1000 : W := mkw 0xffdfbdb60d01000c 0xa7ff7ef6d8340400 0xffffffff0e000003 0xe7fffffffc380000

def z1001 : W := mkw 0x1864c8c566216141 0x0061932315988585 0xb8e7cfc7ee01c1e7 0xeee39f3f1fb80707

def z1002 : W := mkw 0x00b16368f03a3a02 0x7002c58da3c0e8e8 0x00f9f3f8f03e3e18 0x7003e7cfe3c0f8f8

def z1003 : W := mkw 0xc191353200000000 0x230644d4c8000000 0xc0f9ffff00000003 0x6303e7fffc000000

def z1004 : W := mkw 0xe400000099400480 0x0390000002650012 0xff000000ffc03fdf 0x9ffc000003ff00ff

def z1005 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0xbfe60000ffffc021 0x9eff980003ffff00

def z1006 : W := mkw 0xe69a0000998c8008 0xc39a680002663200 0xff1e0000ffffc023 0xdffc780003ffff00

def z1007 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xf8ffffffee31f1f7 0xffe3ffffffb8c7c7

def z1008 : W := mkw 0x12fe020944bfd248 0xc84bf8082512ff49 0x00fe0000003fc020 0x4003f8000000ff00

def z1009 : W := mkw 0xec01e800bb002900 0x13b007a002ec00a4 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z1010 : W := mkw 0xe5017400b9402c80 0x139405d002e500b2 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z1011 : W := mkw 0xffdfbdb690080004 0xe7ff7ef6da402000 0xffffffff100e0003 0xe7fffffffc403800

def z1012 : W := mkw 0xed91fc00bb402d90 0x17b647f002ed00b6 0xfff9fc00ffc03fdf 0xffffe7f003ff00ff

def z1013 : W := mkw 0x0021636860323a02 0x3000858da180c8e8 0xc0f9f3f8f03e3e1b 0x7303e7cfe3c0f8f8

def z1014 : W := mkw 0xc0b16368f63b3b03 0x7302c58da3d8ecec 0xc0f9f3f8fe3e3e1b 0x7303e7cfe3f8f8f8

def z1015 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff10003e1b 0xf7fffffffc4000f8

def z1016 : W := mkw 0xe400000099848000 0x0390000002661200 0xff000000ffffc023 0x9ffc000003ffff00

def z1017 : W := mkw 0x1864cacd66337341 0x0061932b3598cdcd 0xb8e7cfc7fe3fffff 0xfee39f3f1ff8ffff

def z1018 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xffe7cfc7fff1f1f7 0xffff9f3f1fffc7c7

def z1019 : W := mkw 0xffdfbdb600848004 0xa7ff7ef6d8021200 0xffffffff003fc023 0xe7fffffffc00ff00

def z1020 : W := mkw 0xfdd5bda400000000 0x27f756f690000000 0xffffffff00000003 0xe7fffffffc000000

def z1021 : W := mkw 0xffdfbdb600c48484 0xa7ff7ef6d8031212 0xffffffff11ffffff 0xfffffffffc47ffff

def z1022 : W := mkw 0xd2df21b600000004 0xa34b7c86d8000000 0x80ffc3ff00000001 0x4203ff0ffc000000

def z1023 : W := mkw 0xed01bc0099400480 0x07b406f002650012 0xff01fc00ffc03fdf 0xbffc07f003ff00ff

def z1024 : W := mkw 0x12de01b600000004 0xa04b7806d8000000 0x80ffc3ff00000003 0x6203ff0ffc000000

def z1025 : W := mkw 0xe79b353299cc8c9c 0xf79e6cd4ca673232 0x4718303811ce0e08 0x011c60c0e0473838

def z1026 : W := mkw 0x126e0000ddad8008 0x4049b8000376b600 0xfffe0000ffffc023 0xdffff80003ffff00

def z1027 : W := mkw 0xf6ff2120ddad880a 0xf3dbfc848376b620 0xfffe0000ffffc023 0xdffff80003ffff00

def z1028 : W := mkw 0xf6ff2000ddad8808 0xd3dbfc800376b620 0xfffe3000ffffce2b 0xdffff8c003ffff38

def z1029 : W := mkw 0x3f4e9c9600000004 0x84fd3a7258000000 0xffffffff00000003 0xe7fffffffc000000

def z1030 : W := mkw 0x1bdfbdb600000004 0xa46f7ef6d8000000 0x47ffffff00000002 0xe11ffffffc000000

def z1031 : W := mkw 0xed01fd32bb402d94 0x37b407f4caed00b6 0xff01fc38ffc03fdf 0xbffc07f0e3ff00ff

def z1032 : W := mkw 0x1945bdb600000004 0x246516f6d8000000 0x00e7ffff00000000 0x60039ffffc000000

def z1033 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xbfe7ffff00000001 0xa6ff9ffffc000000

def z1034 : W := mkw 0xd2fe0000d4ad8000 0x434bf8000352b600 0xfffe0000ffffc023 0xdffff80003ffff00

def z1035 : W := mkw 0xc0916128b00a2a02 0x73024584a2c028a8 0xc0f9f3f8f00e3e1b 0x7303e7cfe3c038f8

def z1036 : W := mkw 0xe6ba0000d9ac8000 0x439ae8000366b200 0xfffe0000ffffc023 0xdffff80003ffff00

def z1037 : W := mkw 0x3f4e9c9706c5c5c5 0x8cfd3a725c1b1717 0x3f060c070fc1c1e4 0x8cfc18301c3f0707

def z1038 : W := mkw 0xc0b16368f23a3b02 0x7302c58da3c8e8ec 0xc0f9f3f8fe3e3fdf 0x7b03e7cfe3f8f8ff

def z1039 : W := mkw 0xc0b12128d02a0a02 0x7302c484a340a828 0xc0f9f3f8f03e0e0b 0x7303e7cfe3c0f838

def z1040 : W := mkw 0xffdfbdb699000004 0xa7ff7ef6da640000 0xffffffffee000003 0xe7ffffffffb80000

def z1041 : W := mkw 0xffdfbdb60984800c 0xa7ff7ef6d8261200 0xffffffff01c00003 0xe7fffffffc070000

def z1042 : W := mkw 0x00204249663b7343 0x400081092598edcd 0x00000000ee3ff1f4 0x1800000003b8ffc7

def z1043 : W := mkw 0x1844c88526016141 0x0061132214980585 0xb8e7cfc7ee01f1f7 0xfee39f3f1fb807c7

def z1044 : W := mkw 0x126e021b44b7d240 0x0849b8086d12df49 0x00fe023f003fc020 0x4003f808fc00ff00

def z1045 : W := mkw 0xc0916368b01a3a02 0x7302458da2c068e8 0xc0f9f3f8100e3e1b 0x6303e7cfe04038f8

def z1046 : W := mkw 0xfcf5e9a4ff29291c 0xf7f3d7a693fca4a4 0xb8e1c1c0ee000001 0x06e3870703b80000

def z1047 : W := mkw 0x12fe03bf44bfd24c 0xe84bf80efd12ff49 0x00fe03ff003fc020 0x4003f80ffc00ff00

def z1048 : W := mkw 0x366e0000ddad8008 0xc0d9b8000376b600 0xbfe60000ffffc023 0xdeff980003ffff00

def z1049 : W := mkw 0xc0b12368d03a1a02 0x7302c48da340e868 0xc0f9f3f8103e0e0b 0x6303e7cfe040f838

def z1050 : W := mkw 0x1bdfbdb600000004 0xa46f7ef6d8000000 0xb8ffffff00000003 0xe6e3fffffc000000

def z1051 : W := mkw 0xec00c800bb402d90 0x13b0032002ed00b6 0xff01cc00ffc03fdf 0xbffc073003ff00ff

def z1052 : W := mkw 0x1864cacd66337b43 0x1061932b3598cded 0xb8e7cfc7ee31ffff 0xfee39f3f1fb8c7ff

def z1053 : W := mkw 0xed009c009b400590 0x07b40270026d0016 0xff003c00ffc03fdf 0xbffc00f003ff00ff

def z1054 : W := mkw 0xf6df21b600000004 0xa3db7c86d8000000 0xfffff3ff00000003 0xe7ffffcffc000000

def z1055 : W := mkw 0xdbdfbdb600000004 0xa76f7ef6d8000000 0xc0ffffff00000003 0x6303fffffc000000

def z1056 : W := mkw 0xc0b16168f02a2a02 0x7302c585a3c0a8a8 0xc0f9f1f8f00e3e1b 0x3303e7c7e3c038f8

def z1057 : W := mkw 0xc0b16368f03a3a02 0x7302c58da3c0e8e8 0x40f9f3f8103e3e18 0x6103e7cfe040f8f8

def z1058 : W := mkw 0xffdfbdb6998c800c 0xe7ff7ef6da663200 0xffffffffffce0003 0xffffffffffff3800

def z1059 : W := mkw 0xed01fc00bb402d90 0x17b407f002ed00b6 0xff01fc00ffc03fdd 0x27fc07f003ff00ff

def z1060 : W := mkw 0x3fde9db600000004 0xa4ff7a76d8000000 0xbfffcfff00000003 0xe6ffff3ffc000000

def z1061 : W := mkw 0xffdfbdb600000004 0xa7ff7ef6d8000000 0xffffffff11c00003 0xfffffffffc470000

def z1062 : W := mkw 0xf6fe0000ddad8008 0xc3dbf8000376b600 0x7f1e0000ffffc020 0x9dfc780003ffff00

def z1063 : W := mkw 0xf6fe0160ddad800a 0xe3dbf8058376b600 0xfffe01c0ffffc023 0xdffff80703ffff00

def z1064 : W := mkw 0x366e00004da58008 0x80d9b80001369600 0xfffe0000ffffc023 0xdffff80003ffff00

def z1065 : W := mkw 0x030a161b00d6d6c0 0x080c28586c035b5b 0xc7ffffff11ffffff 0xfb1ffffffc47ffff

def z1066 : W := mkw 0x0020424966b7f341 0x08008109259adfcd 0x00000000ee3ff1f4 0x1800000003b8ffc7

def z1067 : W := mkw 0xe4016000bb402d90 0x1390058002ed00b6 0xff01f000ffc03fdf 0xbffc07c003ff00ff

def z1068 : W := mkw 0x1864cac566317141 0x0061932b1598c5c5 0xb8e7cfc7ee31c1e5 0xcee39f3f1fb8c707

def z1069 : W := mkw 0xffdfbdb69b400d94 0xb7ff7ef6da6d0036 0xffffffff1fc00fcf 0xeffffffffc7f003f

def z1070 : W := mkw 0xffdfbdb60485800c 0xa7ff7ef6d8121600 0xffffffff0001c023 0xe7fffffffc000700

def z1071 : W := mkw 0xffdfbdb600400484 0xa7ff7ef6d8010012 0xffffffff11c00e0b 0xe7fffffffc470038

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z4,z5,z6]),(0,[z1,z8,z2,z3,z4,z5,z6])],[(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z10])],[(0,[z11,z1,z2,z3,z4,z5,z6]),(1,[z1,z12,z2,z3,z4,z6]),(0,[z1,z13,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z16,z5,z6])],[(0,[z1,z17,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z19,z6]),(0,[z1,z20,z2,z3,z4,z5,z6]),(1,[z1,z2,z21,z3,z4,z5]),(1,[z22,z1,z2,z4,z5,z6])],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z5,z6,z25]),(0,[z26,z1,z2,z3,z27,z5,z6]),(0,[z28,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z30,z4,z5,z6])],[(0,[z31,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z32,z5,z6]),(0,[z1,z33,z3,z4,z5,z6,z34]),(0,[z1,z2,z3,z4,z35,z5,z36]),(0,[z1,z2,z37,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z38,z5,z6]),(0,[z39,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z40,z4,z6])],[(0,[z41,z1,z2,z3,z42,z5,z6]),(1,[z43,z2,z3,z42,z5,z6]),(0,[z44,z45,z1,z2,z3,z4,z5]),(0,[z1,z46,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z47,z6])]],
   [[(0,[z1,z48,z3,z49,z4,z5,z6]),(0,[z11,z1,z50,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z52,z5,z6]),(0,[z1,z2,z29,z53,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z54,z6]),(0,[z1,z2,z55,z56,z4,z5,z6]),(1,[z1,z2,z3,z57,z4,z5]),(0,[z1,z58,z2,z3,z4,z47,z6]),(0,[z1,z2,z3,z59,z4,z5,z6])],[(0,[z1,z60,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z62,z3,z5,z6]),(1,[z1,z63,z64,z2,z3,z6])],[(0,[z1,z65,z2,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z1,z2,z3,z4,z5,z67,z6])],[(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z6])],[(0,[z43,z1,z2,z3,z4,z5,z6]),(1,[z1,z70,z2,z3,z4,z6])],[(1,[z1,z71,z3,z4,z5,z6]),(0,[z72,z1,z65,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z1,z2,z75,z3,z4,z5,z6])],[(0,[z76,z1,z50,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z1,z78,z2,z48,z3,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z4,z5,z6,z80])]],
   [[(0,[z1,z81,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z4,z83,z5,z6])],[(0,[z41,z2,z3,z4,z84,z5,z6]),(0,[z1,z85,z2,z3,z4,z5,z6]),(0,[z1,z3,z86,z4,z5,z87,z6]),(0,[z1,z58,z3,z4,z5,z47,z6]),(1,[z88,z1,z2,z89,z4,z5]),(0,[z1,z2,z3,z4,z5,z90,z6])],[(0,[z91,z1,z2,z15,z3,z4,z5]),(0,[z1,z2,z3,z57,z49,z4,z5]),(0,[z1,z92,z2,z3,z4,z5,z6]),(0,[z1,z93,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z94,z6]),(0,[z1,z2,z95,z3,z4,z5,z6]),(0,[z1,z2,z75,z3,z29,z4,z5]),(1,[z1,z2,z3,z96,z5,z6])],[(0,[z1,z2,z97,z3,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z99,z5,z6]),(1,[z1,z100,z3,z86,z5,z6])],[(0,[z101,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z102,z5,z6]),(0,[z103,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z104,z3,z4,z5,z6])],[(0,[z1,z105,z2,z3,z4,z5,z6]),(0,[z106,z1,z2,z3,z4,z5,z6])],[(0,[z76,z11,z2,z3,z4,z5,z6]),(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z1,z108,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z109,z5,z6])]],
   [[(0,[z1,z65,z48,z3,z4,z5,z6]),(1,[z1,z2,z110,z3,z4,z5]),(0,[z1,z2,z111,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z112,z6])],[(0,[z41,z1,z64,z2,z3,z5,z6]),(0,[z1,z2,z3,z27,z5,z6,z113])],[(0,[z11,z50,z2,z3,z4,z5,z6]),(0,[z1,z114,z2,z3,z4,z47,z6]),(1,[z1,z33,z3,z4,z5,z34]),(0,[z1,z115,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z84,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z36]),(0,[z1,z116,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z117,z4,z5,z6]),(0,[z1,z2,z3,z118,z4,z5,z113]),(1,[z1,z2,z3,z4,z67,z6])],[(0,[z1,z2,z3,z4,z5,z119,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z121,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z122,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z123]),(1,[z1,z2,z3,z4,z35,z36])],[(0,[z91,z44,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z124,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z125,z5,z6]),(1,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z3,z4,z127,z5,z6]),(0,[z1,z2,z128,z3,z4,z5,z6]),(0,[z129,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z130,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z131,z4,z5,z6]),(0,[z132,z1,z2,z133,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z135]),(0,[z1,z2,z136,z3,z4,z5,z6]),(0,[z1,z2,z137,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z138]),(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z1,z114,z2,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z4,z5,z6])],[(1,[z1,z78,z2,z3,z5,z6]),(0,[z1,z17,z33,z2,z3,z4,z5])],[(0,[z141,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z142,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z143]),(0,[z1,z2,z3,z29,z5,z6,z144])],[(0,[z1,z2,z3,z145,z4,z5,z6]),(1,[z132,z2,z56,z4,z5,z6]),(0,[z1,z2,z3,z42,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z146,z6]),(0,[z88,z1,z2,z3,z4,z5,z6])],[(0,[z1,z63,z2,z3,z4,z5,z6])],[(1,[z76,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z147,z4,z5,z6]),(0,[z1,z2,z148,z3,z4,z5,z6]),(0,[z1,z2,z3,z149,z4,z5,z6])],[(0,[z1,z2,z110,z48,z3,z4,z5]),(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z151]),(0,[z1,z2,z3,z4,z5,z152,z6]),(0,[z1,z2,z3,z153,z4,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z155]),(1,[z1,z156,z2,z3,z5,z6]),(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z158,z4,z5,z6]),(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z160])],[(0,[z91,z45,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z161]),(0,[z162,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z163,z4,z5,z47,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z167]),(0,[z1,z2,z3,z168,z4,z5,z6])],[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z170,z6]),(0,[z1,z2,z3,z56,z4,z5,z6]),(0,[z1,z2,z3,z4,z171,z5,z6]),(0,[z1,z2,z3,z172,z4,z5,z6]),(0,[z173,z1,z2,z174,z4,z5,z6])],[(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z176,z1,z2,z3,z4,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z6])],[(0,[z180,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z181,z5,z6]),(0,[z182,z1,z2,z3,z4,z5,z6]),(1,[z1,z58,z3,z4,z47,z6]),(0,[z1,z2,z3,z4,z5,z183,z6]),(0,[z1,z184,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z185,z6]),(0,[z1,z186,z2,z3,z4,z5,z6]),(0,[z1,z2,z187,z3,z4,z5,z6]),(0,[z45,z1,z33,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z188,z6]),(0,[z1,z2,z189,z3,z4,z5,z6]),(0,[z1,z2,z190,z3,z4,z5,z6])],[(1,[z28,z1,z191,z2,z3,z4])],[(1,[z1,z2,z192,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z193,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6])],[(0,[z72,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z29,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z6]),(0,[z197,z1,z2,z3,z4,z5,z6])],[(0,[z198,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z199,z4,z5,z6]),(0,[z1,z2,z200,z15,z3,z4,z6]),(0,[z201,z1,z2,z3,z4,z5,z6])],[(0,[z1,z156,z2,z3,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6])],[(0,[z1,z2,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z203])],[(0,[z204,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z206,z3,z4,z5,z6])],[(0,[z1,z2,z131,z48,z4,z5,z6]),(0,[z1,z50,z3,z49,z4,z5,z6]),(0,[z207,z1,z2,z3,z4,z5,z6]),(0,[z205,z1,z114,z2,z3,z4,z6]),(0,[z26,z1,z2,z62,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z1,z65,z50,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z209,z6]),(1,[z205,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z211,z5,z6]),(0,[z1,z114,z2,z3,z163,z4,z6]),(0,[z212,z1,z2,z3,z27,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z213])],[(0,[z1,z2,z3,z214,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z215,z6]),(0,[z216,z1,z2,z3,z4,z5,z6]),(1,[z212,z1,z17,z2,z3,z5])],[(0,[z1,z2,z3,z4,z5,z6,z217]),(0,[z91,z1,z2,z3,z4,z5,z18]),(0,[z44,z1,z2,z3,z4,z5,z6]),(0,[z1,z218,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z219,z4,z5,z6])],[(0,[z1,z2,z3,z220,z4,z5,z6]),(1,[z82,z2,z3,z4,z221,z6])],[],[(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z223,z2,z3,z4,z5,z6]),(0,[z224,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z163,z4,z5]),(0,[z1,z2,z3,z225,z4,z5,z6]),(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z113]),(0,[z1,z2,z3,z40,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z132,z2,z3,z56,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z227]),(0,[z1,z2,z3,z4,z5,z6,z228]),(0,[z229,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z230,z3,z4,z5,z6])]],
   [[(0,[z1,z231,z2,z3,z5,z87,z6])],[(0,[z1,z232,z2,z3,z4,z5,z6]),(0,[z72,z1,z2,z133,z4,z5,z6]),(0,[z43,z1,z231,z2,z3,z5,z6]),(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z234,z6]),(0,[z1,z2,z3,z4,z5,z6,z143]),(0,[z1,z235,z2,z3,z4,z5,z6])],[(0,[z1,z236,z2,z3,z5,z221,z6]),(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z1,z2,z238,z3,z4,z5,z6])],[(0,[z132,z1,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z239,z4,z5,z6]),(0,[z1,z240,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z241,z5,z6]),(0,[z1,z2,z3,z242,z4,z5,z6]),(0,[z44,z1,z2,z3,z4,z5,z34]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z36]),(0,[z245,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z163,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z35,z5])],[(0,[z246,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z247,z3,z4,z5,z6]),(0,[z26,z1,z2,z61,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z248,z6])],[(0,[z1,z2,z249,z3,z4,z5,z6]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z252])]],
   [[(0,[z1,z12,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z253,z4,z5,z6]),(0,[z1,z254,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z76,z1,z2,z255,z4,z5,z6]),(0,[z1,z2,z3,z256,z4,z5,z6]),(1,[z41,z2,z3,z84,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z257]),(0,[z1,z63,z2,z3,z29,z5,z6])],[(0,[z1,z2,z3,z220,z4,z84,z6]),(1,[z1,z2,z3,z4,z5,z25])],[(0,[z1,z2,z258,z3,z4,z5,z6]),(0,[z45,z2,z3,z4,z5,z6,z138]),(0,[z1,z2,z3,z4,z5,z259,z6]),(1,[z1,z2,z200,z3,z4,z6]),(1,[z1,z2,z53,z4,z5,z6]),(0,[z1,z64,z2,z3,z5,z6,z144])],[(0,[z1,z260,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z261,z6]),(0,[z1,z262,z2,z3,z4,z5,z6]),(1,[z1,z2,z263,z4,z5,z6]),(0,[z1,z2,z3,z264,z4,z5,z6])],[(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z1,z2,z3,z265,z4,z5,z6]),(0,[z1,z266,z2,z3,z4,z5,z6])],[(0,[z1,z267,z2,z3,z4,z5,z6]),(0,[z268,z1,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z269,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z6]),(0,[z1,z65,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z87,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z191,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z271]),(0,[z1,z2,z3,z4,z5,z272,z6]),(0,[z82,z1,z114,z2,z3,z4,z6]),(0,[z1,z63,z2,z3,z4,z6,z36])],[(1,[z1,z2,z3,z273,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z274]),(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z3,z4,z16,z5,z6])],[(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z4,z5,z6,z143])],[(0,[z277,z1,z2,z3,z4,z5,z6]),(0,[z1,z58,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z278,z6])],[(0,[z1,z2,z3,z279,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z280,z2,z3,z4,z5,z6]),(0,[z281,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z282,z6]),(0,[z1,z2,z283,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z6])],[(0,[z284,z1,z2,z3,z4,z5,z6])],[(0,[z205,z1,z2,z3,z4,z210,z6]),(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z1,z286,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z287,z4,z5])],[(0,[z1,z236,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z288,z6]),(0,[z1,z191,z2,z3,z96,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z289,z5,z6]),(0,[z1,z2,z3,z4,z290,z5,z6])],[(0,[z291,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z29,z5,z6]),(0,[z1,z2,z3,z292,z4,z5,z6])],[(0,[z293,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z294,z6]),(0,[z1,z2,z295,z3,z4,z5,z6]),(0,[z91,z1,z33,z2,z3,z4,z5]),(0,[z1,z100,z3,z86,z4,z5,z6]),(0,[z1,z2,z3,z4,z296,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z56,z49,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z298]),(0,[z299,z1,z2,z3,z4,z5,z6]),(0,[z28,z1,z2,z166,z3,z4,z6]),(0,[z1,z2,z3,z4,z300,z5,z6]),(0,[z88,z1,z17,z2,z3,z4,z5])],[(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z302,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z257]),(0,[z1,z2,z15,z55,z4,z5,z6]),(0,[z303,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z304,z5,z6]),(0,[z1,z2,z305,z3,z4,z5,z6]),(0,[z306,z1,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z166,z3,z287,z4,z5]),(0,[z307,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z308,z4,z5,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(1,[z1,z236,z2,z3,z5,z6]),(0,[z1,z2,z310,z3,z4,z5,z6])],[(0,[z1,z2,z3,z311,z4,z5,z6]),(0,[z1,z2,z312,z3,z4,z5,z6]),(0,[z1,z2,z3,z313,z4,z5,z6])]],
   [[(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z315,z3,z4,z5,z6]),(1,[z91,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z316,z6]),(0,[z1,z114,z3,z163,z4,z5,z6]),(0,[z317,z1,z2,z3,z4,z5,z6])],[(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z84,z5,z6]),(0,[z1,z2,z3,z57,z4,z5,z6]),(0,[z1,z2,z319,z3,z4,z5,z6]),(1,[z1,z2,z238,z4,z5,z6]),(0,[z1,z2,z61,z3,z320,z4,z5]),(0,[z212,z1,z17,z2,z3,z5,z6])],[(0,[z321,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z322,z6]),(0,[z1,z2,z3,z4,z323,z5,z6]),(0,[z324,z1,z3,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z325,z5,z6]),(0,[z1,z2,z3,z4,z35,z5,z6])],[(0,[z1,z2,z3,z326,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z327]),(0,[z1,z2,z3,z4,z5,z328,z6]),(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z3,z330,z4,z5]),(1,[z26,z1,z2,z61,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z6])],[(0,[z331,z1,z2,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z138]),(0,[z1,z2,z3,z4,z332,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z333])],[(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z335,z1,z2,z3,z4,z5,z6]),(0,[z336,z1,z2,z3,z4,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z338,z1,z2,z3,z4,z5,z6])],[(0,[z1,z339,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z341,z2,z3,z4,z5,z6])],[(1,[z1,z2,z342,z4,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z344,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z345])]],
   [[(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z1,z2,z3,z347,z4,z5,z6]),(0,[z44,z1,z2,z263,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z348]),(0,[z1,z2,z3,z4,z349,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z113])],[(0,[z1,z2,z3,z350,z4,z5,z6]),(0,[z1,z231,z2,z3,z86,z5,z6]),(0,[z1,z2,z166,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z351,z5,z6]),(0,[z352,z1,z2,z3,z4,z5,z6]),(0,[z1,z58,z2,z3,z163,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z353]),(0,[z1,z354,z2,z3,z4,z5,z6]),(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z356,z3,z4,z5,z6])],[(0,[z357,z1,z2,z3,z4,z5,z6]),(0,[z132,z1,z315,z3,z4,z5,z6]),(0,[z82,z1,z58,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z358,z6]),(0,[z1,z359,z2,z3,z4,z5,z6])],[(0,[z205,z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z3,z361,z4,z5,z6]),(0,[z1,z362,z2,z3,z4,z5,z6]),(0,[z363,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z364,z6])],[(0,[z1,z100,z2,z3,z86,z5,z6])],[(0,[z365,z1,z2,z3,z4,z5,z6]),(1,[z324,z1,z49,z4,z5,z6]),(0,[z1,z2,z366,z3,z86,z4,z5])],[(0,[z1,z2,z367,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z210,z6]),(0,[z368,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z369,z6]),(0,[z1,z17,z2,z3,z118,z4,z5]),(0,[z1,z2,z370,z3,z4,z5,z6]),(0,[z1,z2,z371,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z163,z4,z5,z25]),(0,[z44,z1,z33,z3,z4,z5,z6]),(0,[z372,z1,z2,z3,z4,z5,z6]),(0,[z1,z373,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z144])],[(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z91,z88,z1,z2,z3,z4,z5]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z375,z1,z2,z3,z4,z5,z6]),(0,[z44,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z376,z4,z5,z6]),(1,[z1,z2,z15,z4,z5,z143]),(0,[z212,z1,z2,z3,z29,z5,z6])],[(0,[z377,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z378,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6]),(0,[z1,z380,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z381,z4,z5,z6]),(0,[z1,z2,z3,z382,z4,z5,z6]),(0,[z1,z383,z2,z3,z4,z5,z6]),(0,[z1,z384,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z385,z5,z6]),(0,[z44,z1,z2,z15,z3,z4,z5])],[(1,[z386,z1,z2,z3,z4,z5]),(0,[z1,z33,z2,z3,z4,z5,z34]),(0,[z1,z2,z3,z387,z4,z5,z6])],[(0,[z1,z2,z55,z133,z4,z5,z6]),(0,[z388,z1,z2,z3,z4,z5,z6]),(0,[z1,z389,z2,z3,z4,z5,z6]),(0,[z390,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z391,z4,z5,z6])],[(0,[z1,z392,z2,z3,z4,z5,z6])]],
   [[(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z126]),(0,[z1,z114,z58,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z5,z6]),(1,[z1,z2,z75,z3,z4,z5])],[(1,[z1,z315,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z36]),(0,[z1,z2,z3,z4,z5,z6,z393]),(0,[z1,z2,z394,z3,z4,z5,z6]),(0,[z1,z2,z3,z395,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z6])],[(0,[z1,z2,z3,z4,z396,z5,z6]),(0,[z1,z2,z3,z397,z4,z5,z6]),(0,[z1,z55,z3,z49,z4,z5,z6]),(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z399,z2,z3,z4,z5,z6])],[(0,[z1,z2,z133,z49,z4,z5,z6]),(0,[z2,z3,z42,z4,z84,z5,z6]),(0,[z1,z2,z174,z3,z4,z248,z6])],[(0,[z1,z2,z3,z4,z5,z400,z6]),(1,[z1,z2,z3,z4,z358,z6]),(0,[z1,z2,z3,z4,z5,z6,z36])],[(0,[z1,z71,z2,z3,z4,z5,z6]),(0,[z324,z72,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z238,z4,z5,z6]),(0,[z1,z403,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z113]),(0,[z1,z2,z3,z4,z404,z5,z6])],[(0,[z1,z2,z405,z3,z4,z5,z6])],[(0,[z44,z1,z3,z330,z4,z5,z6]),(0,[z1,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z407,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z408,z5,z6]),(0,[z1,z2,z3,z4,z5,z409,z6]),(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z1,z411,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6])],[(1,[z1,z413,z2,z3,z4,z6]),(0,[z132,z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z6]),(0,[z1,z2,z342,z3,z4,z5,z6]),(0,[z415,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z416,z3,z4,z5,z6])],[(0,[z1,z2,z417,z3,z4,z5,z6]),(0,[z22,z1,z2,z29,z4,z5,z6])],[(0,[z418,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z419,z6]),(0,[z132,z324,z1,z2,z4,z5,z6]),(0,[z420,z1,z2,z3,z4,z5,z6]),(0,[z212,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z421,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z6,z422]),(0,[z1,z2,z3,z4,z423,z5,z6]),(0,[z1,z100,z2,z3,z5,z87,z6]),(0,[z1,z424,z2,z3,z4,z5,z6]),(0,[z1,z425,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z426,z6]),(0,[z427,z1,z2,z3,z4,z5,z6]),(0,[z1,z63,z2,z3,z4,z6,z144]),(0,[z1,z2,z3,z4,z428,z5,z6]),(0,[z1,z17,z2,z3,z40,z4,z6]),(0,[z1,z429,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z3,z84,z5,z6]),(0,[z430,z1,z2,z3,z4,z5,z6]),(0,[z431,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z432,z3,z4,z5,z6]),(0,[z1,z433,z2,z3,z4,z5,z6]),(0,[z1,z434,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z436,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z437,z6])],[(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z3,z439,z4,z5,z6]),(0,[z1,z2,z440,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z330,z4,z5,z6]),(0,[z1,z2,z441,z3,z4,z5,z6]),(0,[z1,z2,z3,z442,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z2,z3,z4,z35,z6,z36])],[(0,[z41,z43,z2,z3,z4,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z6,z36])],[]],
   [[(0,[z1,z2,z445,z3,z4,z5,z6])],[(0,[z1,z413,z2,z3,z4,z5,z6]),(0,[z1,z2,z62,z4,z27,z5,z6]),(0,[z1,z2,z61,z3,z4,z5,z333]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6])],[(0,[z1,z12,z2,z48,z3,z4,z6]),(0,[z1,z2,z3,z447,z4,z5,z6]),(0,[z1,z2,z3,z448,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z449,z6]),(0,[z1,z2,z15,z3,z4,z5,z113])],[(0,[z1,z450,z2,z3,z4,z5,z6]),(0,[z28,z1,z63,z2,z3,z4,z6]),(0,[z28,z1,z191,z2,z3,z4,z5])],[(1,[z1,z2,z451,z4,z5,z6]),(0,[z72,z2,z133,z3,z4,z5,z6]),(0,[z1,z2,z15,z49,z4,z5,z6]),(0,[z1,z452,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z330,z4,z5]),(0,[z1,z2,z62,z3,z27,z5,z6]),(0,[z1,z2,z166,z3,z4,z6,z36]),(1,[z1,z2,z453,z3,z5,z6])],[(0,[z205,z1,z58,z2,z3,z4,z6]),(0,[z1,z2,z3,z454,z4,z5,z6]),(0,[z88,z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z455,z3,z4,z5,z6])],[(0,[z1,z2,z3,z456,z4,z5,z6]),(0,[z1,z2,z192,z3,z4,z5,z6])],[(0,[z1,z2,z457,z3,z4,z5,z6]),(0,[z1,z17,z2,z15,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z458]),(0,[z1,z2,z3,z4,z5,z459,z6]),(0,[z1,z460,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z44,z1,z2,z3,z4,z5,z113]),(0,[z1,z2,z462,z3,z4,z5,z6]),(0,[z1,z2,z463,z3,z4,z5,z6])],[(0,[z1,z2,z110,z3,z4,z5,z6]),(0,[z464,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z366,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167])],[(0,[z1,z50,z2,z3,z4,z5,z6]),(0,[z386,z1,z2,z3,z56,z4,z5]),(0,[z1,z465,z2,z3,z4,z5,z6]),(0,[z1,z191,z17,z2,z3,z4,z5])],[(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z3,z4,z5,z6,z468])],[(0,[z1,z2,z3,z4,z5,z6,z469]),(0,[z43,z1,z2,z3,z42,z5,z6]),(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z1,z2,z471,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z472,z6]),(0,[z1,z191,z2,z15,z3,z4,z5])],[(0,[z1,z473,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z86,z4,z5,z298]),(0,[z1,z2,z3,z474,z4,z5,z6]),(0,[z475,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z1,z2,z3,z4,z5,z477,z6])],[(0,[z1,z156,z2,z48,z3,z5,z6]),(0,[z1,z2,z3,z4,z478,z5,z6]),(0,[z1,z17,z2,z3,z4,z67,z6]),(0,[z28,z1,z2,z3,z4,z35,z6])],[(0,[z479,z1,z2,z3,z4,z5,z6]),(0,[z82,z1,z63,z2,z3,z4,z6]),(0,[z1,z2,z3,z480,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z34])]],
   [[(0,[z481,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z6]),(0,[z1,z2,z3,z320,z4,z5,z6]),(0,[z1,z2,z482,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z483,z6]),(0,[z1,z2,z3,z4,z5,z6,z484]),(0,[z1,z485,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z6])],[(0,[z1,z2,z133,z3,z4,z5,z6]),(0,[z72,z1,z2,z89,z4,z5,z6]),(0,[z45,z1,z2,z15,z3,z4,z5]),(0,[z1,z2,z3,z487,z4,z5,z6]),(0,[z488,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z248,z6,z36]),(0,[z1,z2,z489,z3,z4,z5,z6])],[(0,[z1,z2,z490,z3,z4,z5,z6]),(0,[z1,z2,z3,z491,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z36])],[(0,[z1,z2,z3,z492,z4,z5,z6]),(0,[z1,z2,z493,z3,z4,z5,z6]),(0,[z324,z1,z65,z3,z4,z5,z6]),(0,[z1,z2,z3,z86,z4,z5,z6]),(0,[z1,z2,z3,z4,z494,z5,z6]),(0,[z26,z1,z2,z4,z5,z248,z6]),(0,[z212,z1,z2,z61,z3,z5,z6]),(0,[z1,z2,z3,z29,z4,z6,z36]),(0,[z1,z2,z3,z4,z5,z6,z495])],[(0,[z1,z78,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z15,z3,z4,z5]),(0,[z88,z1,z33,z2,z3,z4,z5]),(0,[z1,z64,z2,z3,z29,z4,z6]),(0,[z1,z2,z3,z29,z5,z6,z113]),(0,[z1,z2,z3,z496,z4,z5,z6])],[(0,[z497,z1,z2,z3,z4,z5,z6]),(0,[z498,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z499,z6]),(1,[z1,z2,z3,z29,z6,z144]),(0,[z1,z63,z64,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z500])],[(0,[z1,z2,z3,z501,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z502]),(0,[z1,z2,z503,z3,z4,z5,z6]),(0,[z1,z504,z2,z3,z4,z5,z6]),(0,[z1,z2,z505,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z506,z6]),(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z508,z5,z6])],[(0,[z324,z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z55,z3,z4,z5,z6]),(1,[z1,z2,z3,z16,z5,z6]),(0,[z1,z2,z509,z3,z4,z5,z6])],[(0,[z1,z2,z62,z3,z4,z5,z6]),(0,[z1,z2,z61,z4,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z510,z6])],[(0,[z511,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z512,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z4,z5,z138])],[(0,[z76,z1,z48,z3,z4,z5,z6]),(0,[z41,z1,z231,z2,z3,z5,z6]),(0,[z1,z513,z2,z3,z4,z5,z6]),(0,[z1,z514,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z515,z3,z4,z5,z6])],[(0,[z1,z516,z2,z3,z4,z5,z6]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z18,z6,z138]),(0,[z1,z2,z518,z3,z4,z5,z6])],[(0,[z365,z1,z2,z48,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z113,z36]),(0,[z1,z2,z519,z3,z4,z5,z6])],[(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z521,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z522,z6]),(0,[z1,z2,z166,z4,z5,z248,z6])],[(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z27,z5,z6]),(1,[z1,z2,z3,z4,z5,z160])],[(0,[z1,z2,z3,z4,z5,z524,z6]),(0,[z1,z2,z3,z525,z4,z5,z6])],[(0,[z1,z2,z526,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z91,z2,z3,z4,z5,z18,z6]),(1,[z1,z231,z3,z5,z87,z6]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z26,z1,z2,z61,z3,z5,z6]),(1,[z1,z2,z174,z4,z248,z6]),(0,[z1,z2,z3,z53,z4,z5,z6])],[(0,[z132,z1,z2,z56,z4,z5,z6]),(0,[z2,z133,z3,z56,z4,z5,z6]),(0,[z1,z2,z3,z273,z5,z221,z6])],[(0,[z1,z2,z3,z4,z529,z5,z6]),(0,[z1,z530,z2,z3,z4,z5,z6])],[(0,[z76,z2,z48,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z138,z113]),(0,[z1,z2,z531,z3,z4,z5,z6]),(0,[z88,z1,z191,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z532,z3,z4,z5,z6]),(0,[z1,z533,z2,z3,z4,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z534,z6]),(0,[z1,z535,z2,z3,z4,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6]),(1,[z11,z50,z3,z4,z5,z6]),(0,[z132,z1,z2,z15,z4,z5,z6]),(0,[z1,z538,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z539,z4,z5,z6])],[(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z1,z2,z541,z3,z4,z5,z6]),(0,[z1,z2,z3,z542,z4,z5,z6]),(0,[z1,z2,z3,z543,z4,z5,z6]),(0,[z544,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z545,z6]),(0,[z546,z1,z2,z3,z4,z5,z6])],[(0,[z1,z547,z2,z3,z4,z5,z6]),(0,[z1,z548,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z549,z5,z6]),(0,[z1,z2,z3,z550,z4,z5,z6]),(1,[z1,z2,z366,z3,z4,z5]),(0,[z1,z2,z551,z3,z4,z5,z6]),(0,[z552,z1,z2,z3,z4,z5,z6])],[(0,[z553,z1,z2,z3,z4,z5,z6]),(0,[z43,z1,z100,z2,z3,z5,z6]),(0,[z1,z554,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z555])],[(0,[z41,z1,z2,z3,z4,z5,z502]),(0,[z1,z2,z3,z556,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z320,z4,z5])],[(0,[z1,z231,z3,z4,z5,z87,z6]),(0,[z1,z558,z2,z3,z4,z5,z6]),(0,[z1,z2,z559,z3,z4,z5,z6])],[(0,[z560,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z55,z4,z5,z6]),(0,[z1,z2,z174,z4,z5,z248,z6]),(0,[z1,z2,z453,z15,z3,z5,z6]),(0,[z1,z2,z3,z118,z4,z5,z6]),(0,[z1,z561,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z562,z3,z4,z5,z6]),(0,[z1,z563,z2,z3,z4,z5,z6])],[(0,[z50,z2,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z564]),(0,[z1,z2,z3,z4,z5,z565,z6]),(0,[z1,z2,z3,z4,z5,z6,z566]),(0,[z1,z2,z166,z174,z3,z4,z6])],[(1,[z293,z1,z2,z3,z4,z5]),(0,[z82,z2,z3,z4,z5,z221,z6]),(0,[z1,z2,z3,z4,z567,z5,z6])],[(0,[z1,z2,z3,z568,z4,z5,z6]),(0,[z1,z2,z61,z3,z4,z5,z6]),(0,[z1,z2,z569,z3,z4,z5,z6]),(0,[z173,z1,z2,z4,z27,z5,z6])],[(0,[z1,z2,z3,z4,z570,z5,z6])],[(0,[z2,z3,z4,z210,z5,z221,z6]),(0,[z1,z191,z2,z3,z4,z5,z18]),(0,[z324,z1,z2,z3,z4,z5,z6])],[(0,[z76,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z571,z5,z6]),(0,[z1,z63,z64,z2,z3,z5,z6]),(0,[z572,z1,z2,z3,z4,z5,z6])],[(0,[z1,z573,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z574,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(1,[z575,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z27,z5,z248,z6]),(0,[z88,z1,z2,z3,z4,z5,z36])]],
   [[(0,[z576,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z160])],[(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z2,z3,z273,z4,z5,z6]),(0,[z205,z1,z63,z2,z3,z4,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z4,z5,z113]),(0,[z579,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z580,z4,z5,z6]),(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z49,z4,z5]),(0,[z1,z2,z3,z4,z5,z582,z6]),(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z584]),(0,[z585,z1,z2,z3,z4,z5,z6])],[(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z587,z4,z5,z6])],[(0,[z88,z1,z2,z15,z4,z5,z6])],[(0,[z1,z2,z588,z3,z4,z5,z6]),(0,[z589,z1,z2,z3,z4,z5,z6]),(0,[z1,z590,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z5,z6,z113]),(0,[z1,z17,z2,z3,z5,z6,z113])],[(0,[z1,z2,z591,z3,z4,z5,z6]),(0,[z1,z2,z3,z592,z4,z5,z6]),(0,[z1,z2,z3,z593,z4,z5,z6]),(0,[z44,z1,z191,z2,z3,z4,z5]),(0,[z1,z594,z2,z3,z4,z5,z6]),(0,[z1,z595,z2,z3,z4,z5,z6])],[(0,[z1,z596,z2,z3,z4,z5,z6]),(0,[z1,z597,z2,z3,z4,z5,z6]),(0,[z88,z1,z2,z3,z4,z5,z143])]],
   [[],[(0,[z1,z2,z3,z4,z598,z5,z6]),(0,[z1,z599,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z15,z3,z4,z5]),(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z601,z6])],[(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z604,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z298]),(0,[z1,z2,z3,z4,z5,z605,z6])],[(0,[z1,z2,z3,z4,z5,z6,z257]),(0,[z1,z65,z2,z55,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z606,z6]),(0,[z1,z2,z607,z3,z4,z5,z6])],[(0,[z72,z1,z2,z56,z4,z5,z6]),(1,[z1,z2,z3,z220,z4,z6]),(0,[z1,z2,z3,z4,z5,z608,z6]),(0,[z44,z88,z1,z2,z3,z4,z5]),(0,[z609,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z15,z3,z4,z358,z6]),(0,[z1,z2,z3,z4,z611,z5,z6]),(1,[z1,z2,z3,z404,z5,z6])],[(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6]),(0,[z1,z613,z2,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6]),(0,[z1,z614,z2,z3,z4,z5,z6]),(0,[z1,z191,z2,z3,z404,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z615]),(0,[z1,z2,z616,z3,z4,z5,z6])]],
   [[(0,[z1,z617,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z618,z6]),(0,[z1,z2,z3,z619,z4,z5,z6]),(0,[z620,z1,z2,z3,z4,z5,z6])],[(0,[z72,z1,z2,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z126]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z342,z4,z5,z6,z138]),(0,[z621,z1,z2,z3,z4,z5,z6]),(0,[z622,z1,z2,z3,z4,z5,z6]),(0,[z1,z623,z2,z3,z4,z5,z6])],[(0,[z205,z1,z2,z3,z4,z221,z6]),(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z625,z1,z2,z3,z4,z5,z6])],[(0,[z1,z413,z2,z48,z3,z4,z6]),(0,[z1,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z626]),(0,[z1,z627,z2,z3,z4,z5,z6]),(0,[z1,z628,z2,z3,z4,z5,z6]),(0,[z1,z3,z330,z4,z5,z6,z34]),(0,[z1,z2,z89,z3,z4,z5,z6])],[(0,[z386,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z6,z144]),(0,[z1,z2,z3,z4,z5,z630,z6])],[(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z632,z3,z4,z5,z6]),(0,[z1,z633,z2,z3,z4,z5,z6])],[(0,[z132,z72,z2,z3,z4,z5,z6]),(0,[z44,z1,z2,z3,z4,z5,z36]),(0,[z1,z2,z3,z634,z4,z5,z6]),(0,[z1,z2,z3,z635,z4,z5,z6])],[(0,[z173,z1,z2,z3,z4,z248,z6]),(1,[z1,z2,z3,z4,z5,z167]),(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z637,z3,z4,z5,z6])]],
   [[(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z639,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z96,z4,z5,z6])],[(1,[z1,z2,z3,z199,z4,z5]),(0,[z1,z2,z3,z4,z5,z640,z6]),(0,[z324,z1,z2,z49,z4,z5,z6]),(0,[z641,z1,z2,z3,z4,z5,z6]),(0,[z1,z642,z2,z3,z4,z5,z6])],[(1,[z1,z65,z55,z4,z5,z6]),(0,[z1,z643,z2,z3,z4,z5,z6])],[(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z82,z1,z2,z3,z4,z5,z328]),(1,[z1,z2,z62,z27,z5,z6]),(0,[z88,z1,z2,z89,z3,z4,z5]),(1,[z1,z2,z3,z118,z5,z113])],[(0,[z1,z2,z3,z4,z5,z6,z645]),(0,[z41,z1,z100,z2,z3,z5,z6]),(0,[z1,z191,z33,z2,z3,z4,z5]),(0,[z1,z2,z3,z287,z4,z5,z6])],[(1,[z1,z2,z255,z4,z5,z6])],[(0,[z1,z2,z3,z49,z4,z5,z6]),(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z1,z647,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z648,z4,z5,z6]),(0,[z1,z649,z2,z3,z4,z5,z6])]],
   [[(0,[z11,z1,z48,z3,z4,z5,z6]),(0,[z293,z1,z2,z48,z3,z4,z5]),(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z651,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z652,z6]),(0,[z1,z2,z653,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z655,z4,z5,z6]),(0,[z1,z2,z656,z3,z4,z5,z6]),(0,[z1,z70,z2,z3,z4,z84,z6]),(0,[z1,z17,z2,z3,z4,z5,z138]),(0,[z1,z657,z2,z3,z4,z5,z6]),(0,[z173,z26,z1,z2,z4,z5,z6])],[(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z173,z1,z2,z166,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z659])],[(0,[z1,z2,z3,z660,z4,z5,z6]),(0,[z1,z661,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z662,z4,z5,z6]),(0,[z1,z2,z3,z118,z5,z6,z113]),(0,[z1,z663,z2,z3,z4,z5,z6])],[(0,[z1,z664,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z1,z2,z192,z4,z5,z6,z138]),(1,[z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z666,z5,z6])],[(0,[z132,z1,z65,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z667,z5,z6]),(0,[z1,z2,z668,z3,z4,z5,z6])],[(0,[z669,z1,z2,z3,z4,z5,z6]),(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z1,z2,z61,z3,z5,z6,z113]),(0,[z1,z2,z15,z4,z5,z6,z143]),(0,[z212,z1,z64,z2,z3,z5,z6])]],
   [[(0,[z1,z670,z2,z3,z4,z5,z6]),(0,[z88,z45,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z18,z113]),(0,[z671,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z672,z5,z6]),(0,[z1,z2,z3,z4,z673,z5,z6]),(0,[z1,z2,z3,z199,z56,z4,z5]),(0,[z43,z1,z64,z2,z3,z5,z6]),(0,[z205,z2,z3,z4,z210,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6]),(0,[z1,z2,z675,z3,z4,z5,z6]),(1,[z173,z1,z2,z166,z4,z6])],[(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z43,z2,z3,z42,z4,z5,z6]),(0,[z677,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z678]),(0,[z82,z1,z2,z3,z4,z221,z6]),(0,[z1,z2,z3,z4,z5,z6,z113])],[(0,[z1,z2,z3,z4,z5,z6,z679]),(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z681,z2,z3,z4,z5,z6]),(0,[z45,z1,z2,z3,z4,z5,z138]),(0,[z682,z1,z2,z3,z4,z5,z6]),(0,[z173,z1,z2,z166,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z221,z6]),(0,[z1,z683,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z684]),(0,[z1,z2,z685,z3,z4,z5,z6]),(0,[z1,z2,z686,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z328]),(0,[z1,z2,z3,z4,z5,z687,z6]),(0,[z1,z2,z3,z688,z4,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6])],[(0,[z1,z2,z131,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z29,z4,z6]),(0,[z1,z690,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z49,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6]),(0,[z1,z691,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z692,z6])]],
   [[(0,[z76,z1,z2,z451,z4,z5,z6]),(0,[z693,z1,z2,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z118,z5,z6])],[(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z2,z695,z3,z4,z5,z6])],[(1,[z365,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z696,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z210,z5,z6]),(1,[z45,z2,z3,z4,z5,z138]),(0,[z1,z2,z3,z4,z5,z698,z6]),(0,[z1,z2,z3,z4,z5,z6,z699])],[(0,[z700,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z701,z4,z5,z6]),(0,[z1,z2,z3,z4,z702,z5,z6])],[(1,[z72,z2,z133,z4,z5,z6]),(0,[z1,z231,z100,z3,z4,z5,z6])],[(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z502,z6]),(0,[z1,z2,z3,z4,z5,z138,z36]),(1,[z44,z1,z3,z330,z4,z5]),(0,[z1,z2,z3,z704,z4,z5,z6])],[(0,[z705,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z706,z4,z5,z6]),(0,[z1,z100,z2,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z315,z56,z4,z5,z6]),(0,[z1,z65,z111,z4,z5,z6]),(0,[z1,z191,z2,z200,z3,z4]),(0,[z1,z2,z3,z4,z67,z6])],[(0,[z1,z2,z3,z29,z4,z257]),(0,[z1,z2,z3,z404,z5,z138])],[(0,[z76,z110,z48,z3,z4,z5]),(0,[z1,z2,z707,z4,z5,z6])],[(0,[z1,z2,z708,z3,z4,z5]),(0,[z1,z2,z709,z4,z5,z6]),(0,[z205,z2,z3,z4,z710,z6]),(0,[z1,z2,z3,z4,z5,z711]),(0,[z1,z2,z3,z320,z4,z712])],[(0,[z365,z1,z12,z2,z4,z6]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z1,z2,z714,z3,z4,z6])],[(0,[z1,z2,z131,z4,z5,z6]),(0,[z365,z1,z65,z4,z5,z6]),(0,[z1,z315,z15,z4,z5,z6]),(0,[z1,z715,z2,z3,z4,z6])],[(0,[z76,z12,z48,z3,z4,z6]),(0,[z1,z78,z2,z3,z5,z6]),(0,[z1,z2,z716,z3,z5,z6]),(0,[z1,z717,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z167]),(0,[z1,z2,z718,z4,z5,z6])],[(0,[z719,z1,z2,z3,z4,z5]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z33,z519,z3,z4,z5]),(0,[z1,z2,z453,z15,z5,z143])]],
   [[(0,[z132,z2,z56,z4,z5,z6]),(0,[z1,z2,z3,z199,z4,z5]),(0,[z205,z1,z2,z3,z273,z6])],[(0,[z11,z721,z3,z4,z5,z6]),(0,[z1,z65,z55,z4,z5,z6]),(0,[z44,z1,z2,z3,z16,z5]),(0,[z1,z2,z718,z4,z248,z6])],[(0,[z76,z48,z3,z4,z5,z6]),(0,[z1,z413,z2,z110,z3,z4]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z3,z4,z723,z47,z6]),(0,[z1,z2,z3,z118,z5,z113]),(0,[z1,z17,z2,z3,z96,z5])],[(0,[z1,z521,z64,z2,z3,z6])],[(0,[z1,z156,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z2,z724,z4,z5,z6])],[(0,[z1,z725,z2,z3,z5,z6]),(0,[z1,z2,z726,z4,z5,z6])],[(0,[z1,z3,z727,z4,z5,z6]),(0,[z44,z1,z263,z330,z4,z5]),(0,[z1,z728,z2,z3,z5,z6])],[(0,[z82,z92,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z1,z2,z730,z4,z5,z6])]],
   [[(0,[z1,z58,z3,z4,z47,z6]),(0,[z1,z2,z718,z3,z4,z6])],[(0,[z1,z2,z731,z4,z5,z6]),(0,[z1,z2,z3,z4,z732,z5]),(0,[z733,z1,z2,z3,z4,z5]),(0,[z1,z2,z734,z3,z6,z144])],[(0,[z1,z50,z255,z4,z5,z6]),(0,[z76,z131,z48,z4,z5,z6]),(0,[z132,z1,z2,z199,z4,z5]),(0,[z1,z100,z3,z735,z5,z6]),(0,[z1,z2,z15,z3,z4,z67])],[(0,[z2,z3,z4,z710,z221,z6])],[(0,[z1,z2,z3,z4,z5,z736]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z26,z1,z2,z61,z5,z333])],[(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z3,z4,z5,z739])],[(0,[z1,z2,z89,z4,z5,z213]),(0,[z212,z1,z2,z75,z3,z5])]],
   [[(0,[z132,z2,z740,z4,z5,z6]),(0,[z1,z2,z741,z3,z320,z4]),(0,[z173,z1,z2,z166,z4,z6])],[(0,[z1,z2,z3,z742,z5,z6]),(0,[z1,z2,z3,z273,z5,z743]),(0,[z1,z2,z744,z3,z273,z5]),(0,[z1,z2,z3,z4,z745,z6]),(0,[z212,z1,z2,z3,z320,z5])],[(0,[z1,z2,z746,z3,z4,z5]),(0,[z1,z548,z55,z4,z5,z6]),(0,[z205,z643,z2,z3,z4,z6])],[(0,[z1,z2,z747,z4,z5,z6]),(0,[z1,z2,z3,z748,z4,z5]),(0,[z1,z2,z3,z404,z5,z18]),(0,[z1,z2,z749,z62,z5,z6]),(1,[z1,z750,z2,z3,z4]),(0,[z1,z750,z2,z3,z4,z5])],[(0,[z82,z236,z2,z3,z221,z6]),(0,[z1,z2,z200,z3,z287,z4])],[(0,[z1,z2,z3,z751,z5,z6]),(1,[z2,z3,z752,z5,z6]),(0,[z1,z753,z2,z3,z4,z5]),(0,[z1,z2,z754,z3,z4,z5])],[(0,[z293,z1,z156,z2,z3,z5]),(0,[z1,z755,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z756,z6]),(0,[z44,z1,z2,z3,z4,z67])],[(0,[z132,z315,z56,z4,z5,z6]),(0,[z1,z2,z3,z4,z757,z5])]],
   [[(0,[z1,z2,z758,z4,z5,z6]),(0,[z82,z2,z3,z4,z221,z6])],[(0,[z365,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z759]),(0,[z1,z2,z75,z3,z29,z144]),(0,[z1,z2,z3,z96,z6,z36])],[(0,[z1,z2,z3,z760,z5,z6]),(0,[z44,z1,z238,z330,z4,z5])],[(0,[z1,z2,z3,z4,z5,z761]),(0,[z1,z2,z762,z4,z5,z6])],[(0,[z1,z2,z763,z4,z5,z6]),(0,[z2,z3,z4,z5,z764,z6]),(0,[z44,z1,z95,z3,z4,z5])],[(0,[z76,z78,z48,z3,z5,z6]),(0,[z45,z2,z342,z4,z5,z138])],[(0,[z293,z1,z413,z2,z3,z4]),(0,[z1,z2,z3,z29,z5,z126]),(1,[z2,z3,z4,z5,z765])]],
   [[(0,[z45,z1,z2,z342,z4,z5]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z1,z100,z366,z3,z86,z5]),(1,[z1,z2,z718,z4,z6]),(0,[z1,z728,z2,z3,z5,z113])],[(0,[z1,z12,z2,z3,z4,z6]),(0,[z1,z2,z3,z767,z4,z5]),(0,[z1,z64,z2,z3,z272,z6]),(0,[z1,z3,z86,z735,z5,z6])],[(0,[z1,z768,z2,z4,z5,z6]),(0,[z1,z2,z21,z3,z4,z5]),(0,[z1,z2,z15,z263,z4,z5]),(0,[z22,z1,z2,z4,z5,z6])],[(0,[z1,z769,z2,z3,z5,z6]),(0,[z1,z2,z3,z770,z4,z6]),(0,[z1,z2,z238,z4,z5,z36])],[(0,[z76,z156,z48,z3,z5,z6]),(0,[z2,z3,z4,z710,z5,z6]),(0,[z1,z2,z75,z3,z96,z5])],[(0,[z41,z2,z3,z84,z5,z6]),(0,[z41,z2,z3,z84,z5,z126]),(0,[z1,z33,z3,z771,z4,z5]),(0,[z1,z2,z3,z16,z358,z6]),(0,[z1,z2,z3,z40,z4,z6])],[(0,[z1,z2,z3,z4,z772,z6])],[(0,[z1,z2,z53,z4,z5,z6]),(0,[z173,z1,z2,z4,z52,z6])]],
   [[(0,[z1,z2,z3,z773,z5,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z1,z2,z263,z4,z5,z6])],[(0,[z1,z2,z342,z4,z5,z36]),(0,[z776,z2,z3,z4,z5,z6]),(0,[z26,z1,z2,z749,z5,z6]),(0,[z88,z1,z2,z37,z4,z5]),(0,[z1,z63,z64,z2,z3,z6])],[(0,[z777,z1,z2,z3,z4,z5]),(0,[z1,z3,z771,z4,z5,z6]),(0,[z1,z728,z2,z3,z4,z5]),(0,[z1,z2,z3,z40,z6,z113])],[(0,[z1,z78,z413,z2,z3,z6]),(0,[z1,z2,z3,z4,z778,z6]),(0,[z45,z1,z2,z238,z4,z5]),(0,[z1,z2,z3,z4,z5,z779])],[(0,[z1,z780,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z1,z100,z3,z86,z5,z298])],[(0,[z1,z71,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z2,z3,z29,z549,z6]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z36])],[(0,[z1,z2,z784,z3,z4,z5]),(0,[z1,z750,z2,z3,z4,z36])]],
   [[(0,[z41,z70,z2,z3,z84,z6]),(0,[z88,z1,z2,z89,z4,z5])],[(0,[z1,z785,z2,z3,z4,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z1,z2,z15,z3,z404,z5]),(0,[z1,z787,z2,z3,z4,z5])],[(0,[z1,z2,z3,z788,z5,z6])],[(0,[z789,z1,z2,z3,z4,z5]),(0,[z1,z100,z3,z86,z5,z6]),(0,[z1,z3,z771,z4,z5,z34]),(0,[z1,z2,z3,z771,z4,z5])],[(0,[z365,z1,z78,z2,z5,z6])],[(0,[z1,z2,z790,z4,z5,z6]),(0,[z1,z791,z3,z4,z5,z6]),(0,[z1,z2,z792,z3,z287,z5])],[(0,[z173,z1,z2,z718,z4,z6])],[(0,[z1,z2,z110,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z794,z1,z2,z4,z5,z6]),(0,[z43,z2,z3,z752,z5,z6]),(0,[z1,z2,z3,z4,z5,z298]),(0,[z1,z2,z749,z27,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z257]),(0,[z82,z2,z3,z4,z710,z6]),(0,[z45,z2,z3,z4,z5,z765]),(0,[z1,z2,z3,z4,z795,z6])],[(0,[z2,z3,z740,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z796]),(1,[z2,z3,z4,z710,z6]),(0,[z1,z33,z3,z4,z5,z34])],[(0,[z1,z2,z3,z4,z5,z797]),(0,[z41,z2,z3,z220,z84,z6]),(0,[z1,z236,z2,z3,z5,z6]),(0,[z1,z798,z2,z3,z4,z6])],[(0,[z365,z1,z315,z4,z5,z6])],[(0,[z1,z3,z799,z4,z5,z6]),(0,[z91,z2,z3,z4,z5,z18]),(0,[z800,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z801,z5,z6]),(0,[z1,z2,z3,z4,z35,z36])],[(0,[z1,z65,z315,z4,z5,z6]),(0,[z43,z235,z2,z3,z5,z6]),(0,[z82,z1,z2,z3,z273,z6]),(0,[z1,z2,z744,z3,z4,z5]),(0,[z44,z1,z2,z3,z404,z5]),(0,[z1,z2,z3,z802,z5,z6]),(0,[z1,z2,z3,z803,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z126]),(0,[z1,z2,z804,z4,z5,z6]),(1,[z1,z2,z749,z5,z6])],[(0,[z575,z1,z2,z89,z4,z5]),(0,[z1,z2,z3,z805,z5,z6])]],
   [[(0,[z1,z2,z806,z4,z5,z6])],[(0,[z1,z114,z512,z3,z4,z6]),(0,[z1,z64,z2,z734,z3,z6])],[(0,[z807,z1,z2,z3,z4,z5]),(0,[z622,z1,z2,z3,z29,z6]),(1,[z1,z728,z2,z3,z5])],[(0,[z1,z808,z2,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z393]),(0,[z1,z2,z3,z593,z5,z113]),(0,[z1,z2,z3,z4,z5,z809])],[(0,[z1,z2,z3,z810,z5,z6]),(0,[z1,z3,z4,z735,z5,z6])],[(0,[z293,z1,z2,z131,z4,z5]),(0,[z1,z2,z75,z3,z40,z4]),(0,[z811,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z812]),(0,[z1,z399,z55,z4,z5,z6]),(0,[z212,z1,z2,z3,z40,z6])],[(0,[z1,z813,z2,z3,z4,z5]),(0,[z497,z1,z2,z3,z29,z6])]],
   [[(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z413,z2,z131,z4,z6]),(0,[z132,z2,z376,z4,z5,z6]),(0,[z1,z2,z61,z749,z5,z6]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z1,z816,z2,z3,z4,z5])],[(0,[z1,z804,z49,z4,z5,z6])],[(0,[z43,z627,z2,z3,z5,z6]),(0,[z82,z2,z3,z273,z221,z6]),(0,[z1,z817,z3,z4,z5,z6]),(0,[z212,z1,z17,z2,z3,z40])],[(0,[z76,z721,z3,z4,z5,z6]),(0,[z818,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z819,z6]),(0,[z1,z2,z3,z820,z5,z6]),(0,[z1,z2,z3,z821,z5,z6]),(0,[z1,z2,z3,z822,z4,z6]),(0,[z1,z3,z4,z723,z5,z6]),(0,[z88,z1,z2,z730,z4,z5]),(0,[z1,z2,z3,z96,z5,z113])],[(0,[z1,z2,z3,z823,z4,z5]),(0,[z28,z1,z191,z2,z3,z4])],[(0,[z1,z2,z824,z4,z5,z6]),(0,[z1,z78,z2,z110,z3,z5]),(0,[z1,z2,z825,z4,z5,z6]),(0,[z1,z826,z2,z3,z5,z6]),(0,[z1,z2,z192,z4,z5,z6]),(0,[z1,z2,z15,z4,z5,z143])],[(0,[z1,z2,z827,z4,z5,z6]),(0,[z1,z2,z828,z4,z5,z6]),(0,[z1,z2,z166,z718,z4,z6])]],
   [[(0,[z1,z829,z2,z3,z4,z6]),(0,[z830,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z831]),(0,[z297,z2,z3,z4,z5,z138])],[(0,[z1,z33,z2,z3,z4,z67]),(0,[z1,z2,z53,z4,z6,z36])],[(0,[z1,z2,z53,z5,z6,z113]),(0,[z1,z63,z2,z734,z3,z6]),(0,[z1,z2,z3,z4,z178,z36])],[(0,[z1,z156,z2,z110,z3,z5]),(0,[z1,z2,z3,z832,z5,z6])],[(0,[z1,z315,z3,z4,z5,z6]),(0,[z1,z2,z3,z833,z5,z6]),(0,[z82,z2,z3,z4,z221,z257])],[(0,[z1,z12,z156,z2,z3,z6]),(0,[z1,z2,z3,z4,z834,z6]),(0,[z1,z2,z3,z4,z5,z835])],[(0,[z1,z836,z2,z3,z5,z6]),(0,[z41,z2,z3,z391,z5,z6]),(0,[z205,z2,z3,z4,z210,z6]),(0,[z1,z590,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z837]),(1,[z1,z3,z771,z4,z5])]],
   [[(0,[z1,z2,z199,z49,z4,z5]),(0,[z1,z2,z838,z3,z4,z5]),(0,[z1,z2,z3,z29,z6,z252])],[(0,[z1,z2,z839,z3,z5,z6]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z212,z1,z17,z2,z3,z5])],[(0,[z1,z2,z3,z841,z5,z6]),(0,[z1,z2,z3,z4,z67,z18]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z1,z2,z843,z4,z5,z6])],[(0,[z1,z2,z844,z3,z4,z5]),(0,[z293,z1,z12,z2,z3,z4])],[(0,[z1,z2,z845,z4,z5,z6]),(0,[z1,z2,z3,z287,z801,z5])],[(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z2,z3,z4,z5,z847]),(0,[z44,z1,z3,z292,z4,z5]),(0,[z1,z2,z15,z219,z4,z5])],[],[]],
   [[(0,[z1,z2,z848,z4,z5,z6])],[(0,[z1,z2,z3,z849,z5,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z212,z1,z728,z2,z3,z5])],[(0,[z1,z2,z851,z4,z5,z6]),(0,[z1,z2,z3,z852,z5,z6]),(0,[z1,z2,z853,z4,z5,z6]),(0,[z45,z2,z3,z376,z4,z5]),(1,[z1,z804,z4,z5,z6])],[(0,[z1,z2,z3,z4,z854,z6]),(0,[z1,z2,z855,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z856])],[(0,[z1,z2,z857,z4,z5,z6]),(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z315,z133,z4,z5,z6]),(0,[z1,z860,z2,z3,z4,z5])],[(0,[z1,z2,z861,z4,z5,z6]),(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z2,z863,z4,z5,z6]),(1,[z1,z2,z730,z4,z5]),(0,[z22,z1,z2,z29,z6,z144])],[(0,[z1,z2,z3,z4,z5,z864]),(0,[z1,z2,z865,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z866,z6])],[(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z3,z4,z5,z25]),(0,[z1,z2,z489,z27,z5,z6])],[(0,[z869,z1,z2,z4,z5,z6]),(0,[z91,z425,z2,z3,z4,z5]),(0,[z1,z2,z200,z3,z4,z6]),(0,[z88,z1,z2,z3,z4,z67])],[(0,[z1,z2,z3,z16,z5,z36])],[],[(0,[z1,z2,z3,z4,z5,z870])],[(0,[z1,z2,z3,z871,z4,z5])],[(0,[z1,z2,z872,z4,z5,z6])]],
   [[(0,[z1,z2,z451,z4,z5,z6]),(0,[z638,z1,z49,z4,z5,z6]),(0,[z1,z2,z3,z273,z5,z6]),(0,[z44,z1,z97,z3,z4,z5]),(0,[z1,z2,z3,z873,z4,z5]),(0,[z1,z2,z453,z3,z5,z6]),(0,[z28,z1,z750,z2,z3,z4])],[(0,[z365,z293,z1,z2,z4,z5]),(0,[z1,z2,z3,z4,z874,z6]),(0,[z324,z1,z804,z4,z5,z6]),(0,[z28,z1,z2,z3,z287,z4]),(0,[z22,z1,z2,z4,z5,z160])],[],[],[(0,[z1,z2,z3,z875,z4,z5]),(0,[z1,z33,z505,z3,z4,z5])],[(0,[z72,z1,z2,z199,z4,z5]),(0,[z1,z876,z2,z3,z4,z6]),(0,[z1,z2,z3,z287,z4,z5]),(0,[z1,z2,z877,z4,z5,z6]),(0,[z1,z2,z3,z387,z5,z113])],[(0,[z1,z2,z3,z4,z878,z6]),(0,[z1,z2,z879,z4,z5,z6]),(0,[z2,z740,z56,z4,z5,z6]),(0,[z132,z386,z2,z56,z4,z5]),(0,[z1,z2,z53,z4,z5,z160])],[(0,[z76,z48,z451,z4,z5,z6]),(0,[z2,z721,z3,z4,z5,z6]),(0,[z1,z2,z880,z3,z4,z5]),(0,[z91,z1,z2,z238,z4,z5]),(0,[z1,z2,z881,z3,z4,z6]),(0,[z1,z3,z330,z771,z4,z5])]],
   [[(0,[z1,z882,z3,z4,z5,z6]),(0,[z883,z1,z2,z3,z4,z5])],[(0,[z1,z2,z884,z4,z5,z6]),(0,[z1,z885,z3,z4,z5,z6]),(0,[z1,z33,z2,z3,z404,z5]),(0,[z1,z17,z2,z3,z4,z358])],[(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z3,z4,z5,z887])],[(0,[z888,z1,z2,z3,z4,z5]),(0,[z1,z889,z2,z3,z4,z6]),(0,[z1,z2,z890,z3,z4,z5]),(0,[z72,z2,z740,z4,z5,z6]),(0,[z891,z1,z2,z3,z4,z6])],[(0,[z2,z3,z4,z5,z892,z6]),(0,[z1,z2,z730,z15,z4,z5])],[(0,[z365,z1,z413,z2,z4,z6]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z2,z3,z29,z364,z6])],[(0,[z76,z413,z48,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z4,z5,z895]),(0,[z896,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z897]),(0,[z1,z2,z3,z898,z4,z5]),(0,[z1,z231,z610,z3,z5,z6]),(0,[z2,z3,z4,z5,z18,z765]),(0,[z700,z1,z191,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z191,z2,z3,z40,z4])]],
   [[(0,[z900,z1,z2,z3,z4,z5]),(0,[z1,z2,z238,z4,z5,z6]),(0,[z1,z33,z2,z3,z16,z5])],[(0,[z1,z2,z901,z4,z5,z6]),(0,[z1,z2,z15,z439,z4,z5]),(0,[z28,z1,z2,z75,z3,z4])],[(0,[z1,z12,z2,z110,z3,z4]),(0,[z902,z1,z2,z3,z4,z5]),(0,[z44,z1,z3,z421,z4,z5]),(0,[z26,z1,z2,z61,z5,z6]),(0,[z1,z2,z3,z29,z6,z144])],[(0,[z1,z2,z3,z4,z5,z502]),(0,[z1,z2,z3,z4,z67,z138]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z26,z1,z2,z688,z5,z6]),(0,[z1,z2,z904,z3,z5,z6])],[(0,[z1,z2,z3,z4,z905,z6]),(0,[z91,z2,z3,z4,z5,z765])],[(0,[z1,z2,z3,z4,z5,z906]),(0,[z365,z1,z156,z2,z5,z6]),(0,[z907,z1,z2,z3,z4,z5]),(0,[z603,z1,z17,z2,z3,z5])],[(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z2,z342,z4,z5,z6]),(0,[z1,z2,z3,z909,z4,z5]),(0,[z1,z2,z453,z200,z3,z6]),(0,[z1,z2,z734,z3,z4,z6])],[(0,[z205,z460,z2,z3,z4,z6]),(0,[z44,z1,z2,z3,z4,z358])]],
   [[(0,[z1,z2,z3,z4,z5,z910]),(0,[z1,z2,z3,z491,z5,z113])],[(0,[z1,z2,z911,z4,z5,z6])],[(0,[z705,z1,z2,z15,z4,z5]),(0,[z1,z2,z453,z3,z5,z113])],[(0,[z1,z2,z15,z4,z5,z564]),(0,[z1,z2,z3,z4,z912,z6]),(0,[z1,z17,z2,z342,z4,z5]),(0,[z1,z2,z3,z4,z5,z913])],[(0,[z1,z65,z541,z4,z5,z6]),(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z2,z3,z915,z5,z6]),(0,[z1,z2,z3,z702,z5,z113]),(0,[z1,z916,z3,z4,z5,z6])],[(0,[z1,z2,z917,z4,z5,z6]),(0,[z1,z2,z3,z918,z5,z6]),(0,[z324,z1,z49,z4,z5,z6]),(0,[z1,z2,z919,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z160]),(0,[z1,z2,z75,z3,z5,z113]),(0,[z1,z2,z3,z29,z666,z6])],[(0,[z1,z2,z3,z4,z723,z6])],[(0,[z1,z231,z3,z5,z87,z6]),(0,[z1,z231,z3,z735,z5,z6]),(0,[z1,z2,z3,z4,z920,z6])]],
   [[(0,[z76,z293,z48,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z1,z2,z922,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z923]),(0,[z924,z1,z2,z4,z5,z6]),(0,[z1,z2,z749,z4,z5,z6])],[(0,[z1,z925,z2,z3,z4,z6]),(0,[z926,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z287,z4,z36]),(0,[z88,z1,z2,z3,z404,z5])],[(0,[z1,z927,z2,z3,z4,z6]),(0,[z1,z2,z3,z928,z5,z6]),(0,[z1,z191,z2,z3,z16,z5])],[(0,[z1,z2,z3,z4,z929,z6])],[(0,[z386,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z930])],[],[(0,[z1,z17,z2,z238,z4,z5]),(0,[z1,z2,z3,z4,z5,z931])],[(0,[z82,z2,z3,z391,z4,z6]),(0,[z1,z2,z741,z3,z4,z6]),(0,[z1,z2,z75,z3,z4,z5]),(0,[z28,z1,z2,z3,z96,z6])]],
   [[(0,[z1,z2,z730,z3,z4,z5])],[(0,[z1,z2,z3,z932,z5,z6]),(0,[z1,z2,z3,z4,z933,z6]),(0,[z2,z3,z4,z5,z765,z6]),(0,[z1,z2,z3,z4,z325,z36]),(0,[z1,z2,z3,z29,z160,z144])],[(0,[z1,z2,z934,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z2,z3,z4,z5,z936]),(0,[z1,z58,z588,z3,z4,z6]),(0,[z1,z2,z3,z4,z937,z6]),(0,[z938,z1,z2,z3,z4,z5]),(0,[z939,z2,z3,z4,z5,z6]),(0,[z1,z2,z238,z4,z5,z113])],[(0,[z132,z590,z2,z4,z5,z6]),(0,[z1,z2,z3,z940,z5,z6]),(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z3,z4,z358,z6])],[(0,[z1,z2,z3,z4,z942,z6]),(0,[z1,z100,z490,z3,z5,z6]),(0,[z544,z1,z49,z4,z5,z6]),(0,[z943,z1,z2,z3,z4,z5]),(0,[z1,z2,z792,z3,z5,z6]),(0,[z1,z2,z3,z662,z5,z113]),(0,[z1,z63,z179,z2,z3,z6])],[],[(0,[z293,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z944,z4,z5]),(0,[z91,z403,z2,z3,z4,z5]),(0,[z1,z55,z804,z4,z5,z6])],[(0,[z1,z2,z3,z945,z5,z6]),(0,[z1,z2,z946,z3,z4,z5])]],
   [[(0,[z365,z1,z2,z110,z4,z5]),(0,[z1,z2,z947,z3,z5,z6]),(0,[z1,z2,z342,z4,z5,z113])],[(0,[z721,z48,z3,z4,z5,z6]),(0,[z76,z365,z48,z4,z5,z6]),(0,[z1,z413,z2,z3,z4,z6]),(0,[z1,z948,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z949,z6])],[(0,[z1,z2,z950,z3,z4,z5]),(0,[z1,z58,z3,z4,z723,z6])],[(0,[z1,z2,z951,z4,z5,z6]),(0,[z1,z2,z166,z370,z4,z6])],[(0,[z952,z1,z2,z3,z4,z5]),(0,[z343,z50,z3,z4,z5,z6]),(0,[z621,z2,z133,z4,z5,z6])],[(0,[z1,z78,z2,z131,z5,z6])],[(0,[z1,z2,z3,z4,z423,z36]),(0,[z1,z2,z734,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z3,z954,z4,z5]),(0,[z1,z2,z3,z4,z955,z6]),(0,[z26,z1,z2,z61,z320,z5])]],
   [[(0,[z1,z956,z3,z4,z5,z6]),(0,[z1,z2,z957,z4,z5,z6]),(0,[z1,z2,z958,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z959]),(0,[z2,z3,z4,z752,z5,z6]),(0,[z1,z3,z960,z4,z5,z6]),(0,[z1,z2,z3,z4,z961,z5]),(0,[z1,z2,z15,z539,z4,z5])],[(0,[z1,z78,z12,z2,z3,z6]),(0,[z1,z962,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z220,z6]),(0,[z1,z963,z3,z4,z5,z6])],[(0,[z964,z1,z2,z3,z4,z5]),(0,[z546,z2,z3,z4,z5,z138]),(0,[z307,z2,z3,z4,z5,z18]),(0,[z1,z2,z15,z4,z358,z143])],[(0,[z182,z48,z3,z4,z5,z6]),(0,[z1,z813,z315,z3,z4,z5])],[(0,[z1,z965,z2,z3,z5,z6]),(0,[z1,z966,z3,z4,z5,z6]),(0,[z41,z2,z3,z84,z5,z502]),(0,[z1,z967,z2,z3,z4,z6]),(0,[z1,z2,z3,z968,z5,z6])],[(0,[z1,z2,z740,z4,z5,z6])],[(0,[z1,z2,z969,z4,z5,z6]),(0,[z91,z1,z2,z342,z4,z5])]],
   [[(0,[z1,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z2,z3,z971,z4,z6])],[(0,[z888,z1,z2,z255,z4,z5]),(0,[z1,z2,z972,z4,z5,z6]),(0,[z609,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z404,z5,z6])],[(0,[z1,z2,z3,z973,z5,z6]),(0,[z1,z2,z3,z4,z974,z6]),(0,[z975,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z2,z730,z4,z5,z143])],[(0,[z1,z2,z3,z977,z5,z6]),(0,[z1,z2,z75,z3,z4,z36]),(0,[z1,z750,z2,z3,z4,z35])],[(0,[z1,z2,z978,z3,z5,z6])],[(0,[z1,z2,z3,z4,z358,z113]),(0,[z1,z2,z89,z730,z4,z5]),(0,[z1,z2,z734,z3,z29,z6]),(0,[z1,z728,z2,z3,z118,z5])],[(0,[z1,z2,z3,z4,z979,z6]),(0,[z324,z575,z1,z49,z4,z5]),(0,[z1,z2,z200,z15,z4,z143])],[(0,[z1,z2,z980,z4,z5,z6]),(0,[z88,z1,z2,z350,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z981,z6]),(0,[z1,z2,z3,z4,z5,z982])],[(0,[z1,z2,z983,z4,z5,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z324,z1,z57,z49,z4,z5])],[(0,[z72,z2,z128,z4,z5,z6]),(0,[z1,z2,z985,z3,z4,z6]),(0,[z1,z2,z986,z3,z4,z5]),(0,[z1,z2,z749,z3,z5,z6]),(0,[z1,z2,z607,z4,z248,z6]),(0,[z173,z1,z2,z166,z287,z4])],[(0,[z1,z987,z3,z4,z5,z6]),(0,[z1,z988,z2,z3,z5,z6]),(0,[z1,z2,z243,z4,z248,z6])],[(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z2,z990,z3,z4,z5]),(0,[z991,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z73,z5,z113])],[(0,[z2,z3,z4,z210,z710,z6]),(0,[z1,z2,z75,z53,z4,z5])],[(0,[z1,z992,z3,z4,z5,z6]),(0,[z993,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z994]),(0,[z1,z3,z995,z4,z5,z6]),(0,[z1,z3,z804,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z996]),(0,[z1,z2,z62,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z997]),(0,[z22,z1,z2,z75,z4,z5]),(0,[z1,z2,z3,z29,z113,z36])]],
   [[(0,[z1,z998,z3,z4,z5,z6]),(0,[z1,z999,z3,z4,z5,z6])],[(0,[z1,z2,z255,z4,z5,z6]),(0,[z314,z1,z49,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1000])],[(0,[z1,z1001,z3,z4,z5,z6]),(0,[z2,z3,z42,z752,z5,z6]),(0,[z1,z33,z2,z3,z4,z358]),(0,[z1002,z1,z2,z4,z5,z6])],[(0,[z1,z2,z3,z29,z527,z6]),(0,[z1,z2,z3,z1003,z4,z5]),(0,[z1,z2,z3,z1004,z5,z6]),(0,[z28,z1,z191,z2,z3,z96])],[(0,[z293,z1,z78,z2,z3,z5]),(0,[z1,z2,z3,z4,z1005,z6]),(0,[z88,z1,z2,z263,z4,z5])],[(0,[z1,z2,z3,z1006,z4,z6]),(0,[z1,z315,z89,z4,z5,z6]),(0,[z1,z1007,z3,z4,z5,z6]),(0,[z45,z2,z310,z3,z4,z5]),(0,[z1,z1008,z2,z3,z5,z6]),(0,[z1,z2,z3,z735,z5,z6]),(0,[z1,z17,z728,z2,z3,z5])],[(0,[z132,z2,z199,z56,z4,z5]),(0,[z41,z596,z2,z3,z5,z6]),(0,[z1,z2,z3,z1009,z5,z6])]],
   [[(0,[z76,z48,z255,z4,z5,z6]),(0,[z1,z12,z2,z131,z4,z6]),(0,[z50,z721,z3,z4,z5,z6]),(0,[z1,z2,z3,z1010,z5,z6]),(0,[z72,z2,z559,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1011]),(0,[z1,z2,z3,z16,z5,z6]),(0,[z1,z2,z3,z40,z4,z36])],[(0,[z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z3,z1012,z5,z6])],[(0,[z575,z1,z2,z15,z4,z5]),(0,[z1,z2,z200,z3,z4,z36]),(0,[z88,z1,z2,z509,z4,z5])],[(0,[z1,z63,z2,z3,z4,z257])],[(0,[z1013,z1,z2,z4,z5,z6]),(0,[z1,z2,z1014,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z1016,z4,z6])],[(0,[z1,z1017,z3,z4,z5,z6]),(0,[z1,z1018,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z453,z3,z358,z6]),(0,[z1,z2,z3,z4,z5,z1021])],[(0,[z2,z133,z740,z4,z5,z6])],[(0,[z1,z2,z3,z1022,z4,z5]),(0,[z212,z1,z2,z53,z5,z6]),(0,[z1,z750,z2,z3,z4,z6])]],
   [[(0,[z1,z2,z3,z1023,z5,z6]),(0,[z1,z63,z2,z3,z150,z6]),(0,[z1,z1024,z2,z3,z4,z5]),(0,[z173,z1,z2,z166,z4,z167]),(0,[z1,z3,z1025,z4,z5,z6])],[(0,[z1,z1026,z2,z3,z4,z6]),(0,[z1,z2,z3,z220,z4,z761]),(0,[z1,z33,z503,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1027,z6]),(0,[z1,z2,z3,z4,z5,z328]),(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z3,z320,z5,z113]),(0,[z1,z2,z174,z4,z248,z6])],[(0,[z1,z2,z1029,z3,z4,z5])],[(0,[z1,z2,z844,z255,z4,z5]),(0,[z324,z1,z315,z4,z5,z6]),(0,[z1,z2,z1030,z3,z4,z5]),(0,[z575,z1,z2,z263,z4,z5]),(0,[z1,z2,z3,z1031,z5,z6])],[(0,[z1,z2,z1032,z3,z4,z5])],[(0,[z1,z413,z156,z2,z3,z6]),(0,[z45,z2,z3,z4,z5,z138])],[(0,[z1,z2,z3,z4,z5,z1033])]],
   [[(0,[z11,z50,z3,z4,z5,z6]),(0,[z72,z2,z133,z4,z5,z6]),(0,[z1,z2,z453,z3,z320,z5]),(0,[z1,z2,z61,z482,z5,z6]),(0,[z1,z2,z15,z16,z5,z143])],[(0,[z44,z1,z3,z330,z4,z5])],[(0,[z1,z2,z3,z1034,z4,z6]),(0,[z1,z65,z804,z4,z5,z6]),(0,[z1,z2,z366,z3,z4,z5]),(0,[z1,z2,z1035,z4,z5,z6])],[(0,[z1,z2,z3,z1036,z4,z6])],[(0,[z1,z2,z1037,z4,z5,z6]),(0,[z1,z2,z3,z320,z4,z5])],[(0,[z1,z2,z1038,z4,z5,z6]),(0,[z1,z2,z1039,z4,z5,z6])],[(0,[z1,z2,z110,z131,z4,z5]),(0,[z1,z2,z3,z752,z5,z6])],[(0,[z1,z64,z2,z3,z5,z126]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z2,z3,z4,z5,z743]),(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1042,z1,z2,z3,z4,z5]),(0,[z1,z1043,z3,z4,z5,z6])]],
   [[(0,[z1,z1044,z2,z3,z5,z6]),(0,[z28,z1,z191,z2,z3,z404])],[(0,[z2,z3,z752,z84,z5,z6]),(0,[z2,z3,z4,z5,z765,z138]),(0,[z1,z2,z1045,z4,z5,z6]),(0,[z585,z1,z2,z15,z4,z5])],[(0,[z1,z2,z718,z174,z4,z6]),(0,[z2,z3,z4,z5,z1046,z6])],[(0,[z182,z2,z56,z4,z5,z6]),(0,[z43,z2,z3,z42,z5,z6]),(0,[z1,z1047,z2,z3,z5,z6]),(0,[z1,z2,z29,z53,z6,z144])],[(0,[z1,z2,z55,z199,z4,z5]),(0,[z1,z2,z1048,z3,z4,z6]),(0,[z1,z2,z1049,z4,z5,z6]),(0,[z1,z2,z1050,z3,z4,z5]),(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z1052,z3,z4,z5,z6])],[(1,[z2,z740,z4,z5,z6]),(0,[z1,z2,z3,z57,z4,z5])],[(0,[z1,z2,z3,z1053,z5,z6]),(0,[z45,z2,z192,z4,z5,z138]),(0,[z575,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1054,z5])],[(1,[z721,z3,z4,z5,z6]),(0,[z1,z191,z2,z342,z4,z5]),(0,[z1,z33,z3,z59,z4,z5]),(0,[z1,z2,z3,z1055,z4,z5])]],
   [[(0,[z1,z2,z1056,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z765]),(0,[z1,z2,z1057,z4,z5,z6]),(0,[z1,z2,z200,z3,z16,z6])],[(0,[z1,z70,z2,z3,z4,z6]),(0,[z44,z1,z3,z771,z4,z5])],[(0,[z1,z48,z255,z4,z5,z6]),(0,[z907,z1,z315,z3,z4,z5]),(0,[z43,z1,z2,z3,z220,z6]),(0,[z1,z2,z838,z3,z220,z4]),(1,[z1,z3,z735,z5,z6]),(0,[z1,z2,z3,z4,z5,z1058])],[(0,[z1,z2,z3,z1059,z5,z6]),(0,[z1,z2,z1060,z3,z4,z5]),(0,[z1,z2,z442,z27,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1061]),(0,[z1,z2,z3,z4,z1062,z6]),(0,[z1,z191,z2,z3,z528,z4]),(1,[z1,z2,z734,z3,z6]),(0,[z212,z1,z17,z2,z3,z67])],[(0,[z1,z2,z3,z4,z1063,z6]),(0,[z28,z1,z2,z53,z4,z6])],[(0,[z1,z156,z2,z131,z5,z6]),(0,[z1,z17,z2,z453,z3,z5])],[(0,[z1,z2,z1064,z3,z4,z6]),(0,[z132,z71,z56,z4,z5,z6]),(0,[z82,z2,z3,z4,z221,z328]),(0,[z1065,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z96,z5,z6]),(0,[z636,z1,z2,z3,z29,z6])]],
   [[(0,[z1066,z1,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z474,z5]),(0,[z1,z2,z3,z1067,z5,z6])],[],[(0,[z1,z1068,z3,z4,z5,z6]),(0,[z1,z191,z2,z238,z4,z5])],[(0,[z1,z2,z3,z220,z4,z6]),(0,[z1,z3,z735,z5,z87,z6]),(0,[z1,z191,z750,z2,z3,z4])],[(0,[z365,z1,z49,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1069]),(0,[z1,z2,z3,z4,z5,z1070])],[],[(0,[z1,z2,z15,z407,z4,z5]),(0,[z1,z2,z3,z4,z300,z36]),(0,[z1,z2,z3,z4,z611,z36])],[(0,[z1,z2,z3,z4,z5,z1071]),(0,[z41,z2,z3,z752,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 553) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 553).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1049)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [553, 496] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 179).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 179).take 77).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [179, 77] = true :=
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

end PEqualNP.Outside.L_meta_45650

theorem PEqualNP.Outside.L_meta_45650 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241384 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241384 * 2 ^ 32 + 4004030464) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45650.solve