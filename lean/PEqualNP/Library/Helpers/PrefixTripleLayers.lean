import PEqualNP.Library.Helpers.PrefixTripleExclusion

namespace PEqualNP.Library.PrefixTripleExclusion

open PEqualNP.Library.K4Parity

/- A key has bit m set exactly when five-row wire mask m is available. Stage j
   contains the banks reachable with at most j additional gates. The checks below
   verify every transition; the last check tests the excluded triples directly. -/
private def stage0 : Tree := (.node .nil 3506503681 .nil)

private def stage1 : Tree := (.node (.node (.node .nil 3506503681 .nil) 3506503683 .nil) 3506503689 (.node (.node .nil 3506503809 .nil) 3506536449 .nil))

private def stage2 : Tree := (.node
  (.node
    (.node (.node (.node .nil 3506503681 .nil) 3506503683 .nil) 3506503689 (.node (.node .nil 3506503691 .nil) 3506503693 .nil)) 3506503809
    (.node (.node (.node .nil 3506503811 .nil) 3506503817 .nil) 3506503825 (.node (.node .nil 3506503873 .nil) 3506536449 .nil))) 3506536451
  (.node
    (.node (.node (.node .nil 3506536457 .nil) 3506536577 .nil) 3506536705 (.node (.node .nil 3506540545 .nil) 3506552833 .nil)) 3506634755
    (.node (.node (.node .nil 3507027977 .nil) 3514892417 .nil) 3540058115 (.node (.node .nil 3640721417 .nil) 4043374595 .nil))))

private def stage3 : Tree := (.node
  (.node
    (.node
      (.node
        (.node (.node (.node .nil 3506503681 .nil) 3506503683 .nil) 3506503689 (.node (.node .nil 3506503691 .nil) 3506503693 .nil)) 3506503695
        (.node (.node (.node .nil 3506503809 .nil) 3506503811 .nil) 3506503817 (.node (.node .nil 3506503819 .nil) 3506503821 .nil))) 3506503825
      (.node
        (.node (.node (.node .nil 3506503827 .nil) 3506503833 .nil) 3506503873 (.node (.node .nil 3506503875 .nil) 3506503881 .nil)) 3506503889
        (.node (.node (.node .nil 3506536449 .nil) 3506536451 .nil) 3506536457 (.node (.node .nil 3506536459 .nil) 3506536461 .nil)))) 3506536577
    (.node
      (.node
        (.node (.node (.node .nil 3506536579 .nil) 3506536585 .nil) 3506536593 (.node (.node .nil 3506536641 .nil) 3506536705 .nil)) 3506536707
        (.node (.node (.node .nil 3506536713 .nil) 3506536833 .nil) 3506540545 (.node (.node .nil 3506540547 .nil) 3506540553 .nil))) 3506540673
      (.node
        (.node (.node (.node .nil 3506540801 .nil) 3506552833 .nil) 3506552835 (.node (.node .nil 3506552841 .nil) 3506552961 .nil)) 3506553089
        (.node (.node (.node .nil 3506556929 .nil) 3506634755 .nil) 3506634763 (.node (.node .nil 3506634883 .nil) 3506651139 .nil))))) 3506667523
  (.node
    (.node
      (.node
        (.node (.node (.node .nil 3506683905 .nil) 3506765837 .nil) 3507027977 (.node (.node .nil 3507027979 .nil) 3507027981 .nil)) 3507028105
        (.node (.node (.node .nil 3507032073 .nil) 3507060745 .nil) 3507064833 (.node (.node .nil 3507290121 .nil) 3507552401 .nil))) 3510698177
      (.node
        (.node (.node (.node .nil 3514892417 .nil) 3514892419 .nil) 3514892425 (.node (.node .nil 3514892433 .nil) 3514892481 .nil)) 3514892673
        (.node (.node (.node .nil 3514925185 .nil) 3514925313 .nil) 3515940993 (.node (.node .nil 3519086721 .nil) 3540058115 .nil)))) 3540058123
    (.node
      (.node
        (.node (.node (.node .nil 3540058179 .nil) 3540058243 .nil) 3540058305 (.node (.node .nil 3540090883 .nil) 3540189187 .nil)) 3573612557
        (.node (.node (.node .nil 3640721417 .nil) 3640721419 .nil) 3640721421 (.node (.node .nil 3640721433 .nil) 3640721545 .nil))) 3640721553
      (.node
        (.node (.node (.node .nil 3640754185 .nil) 3641245705 .nil) 3707830281 (.node (.node .nil 4043374595 .nil) 4043374599 .nil)) 4043374603
        (.node (.node (.node .nil 4043374605 .nil) 4043374723 .nil) 4043407363 (.node (.node .nil 4043505667 .nil) 4076929027 .nil))))))

private def stage4 : Tree := (.node
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3506503681 .nil) 3506503683 .nil) 3506503689 (.node (.node .nil 3506503691 .nil) 3506503693 .nil)) 3506503695
            (.node (.node (.node .nil 3506503809 .nil) 3506503811 .nil) 3506503817 (.node (.node .nil 3506503819 .nil) 3506503821 .nil))) 3506503823
          (.node
            (.node (.node (.node .nil 3506503825 .nil) 3506503827 .nil) 3506503833 (.node (.node .nil 3506503835 .nil) 3506503837 .nil)) 3506503859
            (.node (.node (.node .nil 3506503873 .nil) 3506503875 .nil) 3506503881 (.node .nil 3506503883 .nil)))) 3506503885
        (.node
          (.node
            (.node (.node (.node .nil 3506503889 .nil) 3506503891 .nil) 3506503897 (.node (.node .nil 3506536449 .nil) 3506536451 .nil)) 3506536457
            (.node (.node (.node .nil 3506536459 .nil) 3506536461 .nil) 3506536463 (.node .nil 3506536577 .nil))) 3506536579
          (.node
            (.node (.node (.node .nil 3506536585 .nil) 3506536587 .nil) 3506536589 (.node (.node .nil 3506536593 .nil) 3506536595 .nil)) 3506536601
            (.node (.node (.node .nil 3506536641 .nil) 3506536643 .nil) 3506536649 (.node .nil 3506536657 .nil))))) 3506536705
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3506536707 .nil) 3506536713 .nil) 3506536715 (.node (.node .nil 3506536717 .nil) 3506536833 .nil)) 3506536835
            (.node (.node (.node .nil 3506536841 .nil) 3506536849 .nil) 3506536897 (.node .nil 3506537219 .nil))) 3506538761
          (.node
            (.node (.node (.node .nil 3506540545 .nil) 3506540547 .nil) 3506540553 (.node (.node .nil 3506540555 .nil) 3506540557 .nil)) 3506540673
            (.node (.node (.node .nil 3506540675 .nil) 3506540681 .nil) 3506540689 (.node .nil 3506540737 .nil)))) 3506540801
        (.node
          (.node
            (.node (.node (.node .nil 3506540803 .nil) 3506540809 .nil) 3506540929 (.node (.node .nil 3506548739 .nil) 3506552833 .nil)) 3506552835
            (.node (.node (.node .nil 3506552841 .nil) 3506552843 .nil) 3506552845 (.node .nil 3506552961 .nil))) 3506552963
          (.node
            (.node (.node (.node .nil 3506552969 .nil) 3506552977 .nil) 3506553025 (.node (.node .nil 3506553089 .nil) 3506553091 .nil)) 3506553097
            (.node (.node (.node .nil 3506553217 .nil) 3506556929 .nil) 3506556931 (.node .nil 3506556937 .nil)))))) 3506557057
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3506557185 .nil) 3506634755 .nil) 3506634763 (.node (.node .nil 3506634767 .nil) 3506634883 .nil)) 3506634891
            (.node (.node (.node .nil 3506634899 .nil) 3506634947 .nil) 3506651139 (.node (.node .nil 3506651147 .nil) 3506651267 .nil))) 3506651395
          (.node
            (.node (.node (.node .nil 3506655235 .nil) 3506667523 .nil) 3506667531 (.node (.node .nil 3506667651 .nil) 3506667779 .nil)) 3506671619
            (.node (.node (.node .nil 3506683905 .nil) 3506683907 .nil) 3506683913 (.node .nil 3506684033 .nil)))) 3506684161
        (.node
          (.node
            (.node (.node (.node .nil 3506688001 .nil) 3506765837 .nil) 3506765839 (.node (.node .nil 3506765965 .nil) 3506774029 .nil)) 3506798605
            (.node (.node (.node .nil 3507027977 .nil) 3507027979 .nil) 3507027981 (.node .nil 3507027983 .nil))) 3507028105
          (.node
            (.node (.node (.node .nil 3507028107 .nil) 3507028109 .nil) 3507028121 (.node (.node .nil 3507028169 .nil) 3507032073 .nil)) 3507032075
            (.node (.node (.node .nil 3507032077 .nil) 3507032201 .nil) 3507032329 (.node .nil 3507060745 .nil))))) 3507060747
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3507060749 .nil) 3507060873 .nil) 3507061001 (.node (.node .nil 3507064833 .nil) 3507064835 .nil)) 3507064841
            (.node (.node (.node .nil 3507064961 .nil) 3507065089 .nil) 3507077129 (.node .nil 3507081217 .nil))) 3507159051
          (.node
            (.node (.node (.node .nil 3507290121 .nil) 3507290123 .nil) 3507290125 (.node (.node .nil 3507290249 .nil) 3507294217 .nil)) 3507298313
            (.node (.node (.node .nil 3507322889 .nil) 3507326977 .nil) 3507552401 (.node .nil 3507552403 .nil)))) 3507552409
        (.node
          (.node
            (.node (.node (.node .nil 3507552465 .nil) 3507554449 .nil) 3507585169 (.node (.node .nil 3510698177 .nil) 3510698179 .nil)) 3510698185
            (.node (.node (.node .nil 3510698193 .nil) 3510698689 .nil) 3510730945 (.node .nil 3511746753 .nil))) 3514892417
          (.node
            (.node (.node (.node .nil 3514892419 .nil) 3514892425 .nil) 3514892427 (.node (.node .nil 3514892429 .nil) 3514892433 .nil)) 3514892435
            (.node (.node (.node .nil 3514892441 .nil) 3514892481 .nil) 3514892483 (.node .nil 3514892489 .nil))))))) 3514892497
  (.node
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3514892673 .nil) 3514892675 .nil) 3514892681 (.node (.node .nil 3514892689 .nil) 3514892737 .nil)) 3514925185
            (.node (.node (.node .nil 3514925187 .nil) 3514925193 .nil) 3514925201 (.node (.node .nil 3514925249 .nil) 3514925313 .nil))) 3514925315
          (.node
            (.node (.node (.node .nil 3514925321 .nil) 3514925441 .nil) 3514929281 (.node (.node .nil 3514929409 .nil) 3514941569 .nil)) 3514941697
            (.node (.node (.node .nil 3515023491 .nil) 3515416713 .nil) 3515940993 (.node .nil 3515940995 .nil)))) 3515941001
        (.node
          (.node
            (.node (.node (.node .nil 3515941009 .nil) 3515941057 .nil) 3515941249 (.node (.node .nil 3515943041 .nil) 3515973761 .nil)) 3515973889
            (.node (.node (.node .nil 3519086721 .nil) 3519086723 .nil) 3519086729 (.node .nil 3519086737 .nil))) 3519086785
          (.node
            (.node (.node (.node .nil 3519086977 .nil) 3519087233 .nil) 3519119489 (.node (.node .nil 3519119617 .nil) 3520135297 .nil)) 3540058115
            (.node (.node (.node .nil 3540058123 .nil) 3540058127 .nil) 3540058179 (.node .nil 3540058187 .nil))))) 3540058195
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3540058243 .nil) 3540058251 .nil) 3540058259 (.node (.node .nil 3540058305 .nil) 3540058307 .nil)) 3540058313
            (.node (.node (.node .nil 3540058321 .nil) 3540090883 .nil) 3540090891 (.node .nil 3540090947 .nil))) 3540091011
          (.node
            (.node (.node (.node .nil 3540091073 .nil) 3540091139 .nil) 3540091395 (.node (.node .nil 3540094979 .nil) 3540107267 .nil)) 3540189187
            (.node (.node (.node .nil 3540189195 .nil) 3540189251 .nil) 3540189315 (.node .nil 3540205571 .nil)))) 3540221955
        (.node
          (.node
            (.node (.node (.node .nil 3540238337 .nil) 3540582411 .nil) 3544252483 (.node (.node .nil 3544252609 .nil) 3548446851 .nil)) 3548446913
            (.node (.node (.node .nil 3573612557 .nil) 3573612559 .nil) 3573612589 (.node .nil 3573612685 .nil))) 3573645325
          (.node
            (.node (.node (.node .nil 3573874701 .nil) 3574136845 .nil) 3574398985 (.node (.node .nil 3640721417 .nil) 3640721419 .nil)) 3640721421
            (.node (.node (.node .nil 3640721423 .nil) 3640721433 .nil) 3640721435 (.node .nil 3640721437 .nil)))))) 3640721545
    (.node
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 3640721547 .nil) 3640721549 .nil) 3640721553 (.node (.node .nil 3640721555 .nil) 3640721561 .nil)) 3640721609
            (.node (.node (.node .nil 3640721617 .nil) 3640754185 .nil) 3640754187 (.node .nil 3640754189 .nil))) 3640754201
          (.node
            (.node (.node (.node .nil 3640754313 .nil) 3640754321 .nil) 3640754441 (.node (.node .nil 3640756233 .nil) 3640758281 .nil)) 3640770569
            (.node (.node (.node .nil 3640852491 .nil) 3640983565 .nil) 3641245705 (.node .nil 3641245707 .nil)))) 3641245709
        (.node
          (.node
            (.node (.node (.node .nil 3641245721 .nil) 3641245833 .nil) 3641249801 (.node (.node .nil 3641278473 .nil) 3641282561 .nil)) 3641507849
            (.node (.node (.node .nil 3641770009 .nil) 3641770129 .nil) 3649110153 (.node .nil 3649110161 .nil))) 3674275851
          (.node
            (.node (.node (.node .nil 3707830281 .nil) 3707830283 .nil) 3707830285 (.node (.node .nil 3707830297 .nil) 3707830313 .nil)) 3707830409
            (.node (.node (.node .nil 3707830417 .nil) 3707863049 .nil) 3708354569 (.node .nil 4043374595 .nil))))) 4043374599
      (.node
        (.node
          (.node
            (.node (.node (.node .nil 4043374603 .nil) 4043374605 .nil) 4043374607 (.node (.node .nil 4043374723 .nil) 4043374727 .nil)) 4043374731
            (.node (.node (.node .nil 4043374733 .nil) 4043374739 .nil) 4043374755 (.node .nil 4043374787 .nil))) 4043407363
          (.node
            (.node (.node (.node .nil 4043407367 .nil) 4043407371 .nil) 4043407373 (.node (.node .nil 4043407491 .nil) 4043407619 .nil)) 4043411459
            (.node (.node (.node .nil 4043415555 .nil) 4043423747 .nil) 4043505667 (.node .nil 4043505671 .nil)))) 4043505675
        (.node
          (.node
            (.node (.node (.node .nil 4043505795 .nil) 4043522051 .nil) 4043538435 (.node (.node .nil 4043554817 .nil) 4043636743 .nil)) 4043636749
            (.node (.node (.node .nil 4043898891 .nil) 4043898893 .nil) 4051763331 (.node .nil 4076929027 .nil))) 4076929031
          (.node
            (.node (.node (.node .nil 4076929035 .nil) 4076929091 .nil) 4076929155 (.node (.node .nil 4076929217 .nil) 4076961795 .nil)) 4077060099
            (.node (.node (.node .nil 4110483463 .nil) 4110483469 .nil) 4177592331 (.node .nil 4177592333 .nil))))))))

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem tested0 : stage0.every (fun s => !hit s && transitions stage1.has s) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem tested1 : stage1.every (fun s => !hit s && transitions stage2.has s) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem tested2 : stage2.every (fun s => !hit s && transitions stage3.has s) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem tested3 : stage3.every (fun s => !hit s && transitions stage4.has s) = true := by decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem tested4 : stage4.every (fun s => !hit s && transitions (fun s => !hit s) s) = true := by decide +kernel

theorem excludes (gs : List PEqualNP.CircuitLowerBounds.Gate) (h : gs.length ≤ 5) :
    ¬ targets (run gs initial) := by
  have h4 := transferLayer _ _ _ tested4 bottom
  have h3 := transferLayer _ _ _ tested3 h4
  have h2 := transferLayer _ _ _ tested2 h3
  have h1 := transferLayer _ _ _ tested1 h2
  have h0 := transferLayer _ _ _ tested0 h1
  apply h0 3506503681 (by decide) initial _ (by decide) (by decide) gs h
  intro m hm
  simp only [initial, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end PEqualNP.Library.PrefixTripleExclusion
