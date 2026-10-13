import APPTSubunit.NegativeState

open scoped BigOperators
namespace APPTSubunit
open APPTReview
set_option maxHeartbeats 3000000

/-- Exact rational polynomial used in the half-order head comparison. -/
def halfHeadPolynomial (r t : ℝ) : ℝ := 12*r^5*t^2+8*r^4*t^3+24*r^4*t^2-4*r^4*t^1+16*r^3*t^3+16*r^3*t^1-8*r^3+8*r^2*t^3-24*r^2*t^2-12*r^2*t^1-12*r^1*t^2+8*r^1*t^1-8*r^1-8*t^1+16
def halfHeadRemainder (r t : ℝ) : ℝ := -12*r^4*t^2-8*r^3*t^3-36*r^3*t^2+4*r^3*t^1-24*r^2*t^3-36*r^2*t^2-12*r^2*t^1+8*r^2-32*r^1*t^3-12*r^1*t^2+8*r^1-32*t^3-8*t^1+16

theorem half_polynomial_box_0 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial (0+(3/4)*x) (0+(1/2)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial (0+(3/4)*x) (0+(1/2)*y)=
      16*x^0*(1-x)^5*y^0*(1-y)^3+
      44*x^0*(1-x)^5*y^1*(1-y)^2+
      40*x^0*(1-x)^5*y^2*(1-y)^1+
      12*x^0*(1-x)^5*y^3*(1-y)^0+
      74*x^1*(1-x)^4*y^0*(1-y)^3+
      205*x^1*(1-x)^4*y^1*(1-y)^2+
      (743/4)*x^1*(1-x)^4*y^2*(1-y)^1+
      (219/4)*x^1*(1-x)^4*y^3*(1-y)^0+
      136*x^2*(1-x)^3*y^0*(1-y)^3+
      (3013/8)*x^2*(1-x)^3*y^1*(1-y)^2+
      (2663/8)*x^2*(1-x)^3*y^2*(1-y)^1+
      (1485/16)*x^2*(1-x)^3*y^3*(1-y)^0+
      (965/8)*x^3*(1-x)^2*y^0*(1-y)^3+
      (2665/8)*x^3*(1-x)^2*y^1*(1-y)^2+
      (1123/4)*x^3*(1-x)^2*y^2*(1-y)^1+
      (2265/32)*x^3*(1-x)^2*y^3*(1-y)^0+
      (197/4)*x^4*(1-x)^1*y^0*(1-y)^3+
      (17375/128)*x^4*(1-x)^1*y^1*(1-y)^2+
      (13633/128)*x^4*(1-x)^1*y^2*(1-y)^1+
      (6069/256)*x^4*(1-x)^1*y^3*(1-y)^0+
      (53/8)*x^5*(1-x)^0*y^0*(1-y)^3+
      (2335/128)*x^5*(1-x)^0*y^1*(1-y)^2+
      (13921/1024)*x^5*(1-x)^0*y^2*(1-y)^1+
      (3789/1024)*x^5*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_1 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial (0+(3/8)*x) ((1/2)+(1/2)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial (0+(3/8)*x) ((1/2)+(1/2)*y)=
      12*x^0*(1-x)^5*y^0*(1-y)^3+
      32*x^0*(1-x)^5*y^1*(1-y)^2+
      28*x^0*(1-x)^5*y^2*(1-y)^1+
      8*x^0*(1-x)^5*y^3*(1-y)^0+
      (459/8)*x^1*(1-x)^4*y^0*(1-y)^3+
      (1211/8)*x^1*(1-x)^4*y^1*(1-y)^2+
      (259/2)*x^1*(1-x)^4*y^2*(1-y)^1+
      (71/2)*x^1*(1-x)^4*y^3*(1-y)^0+
      (6909/64)*x^2*(1-x)^3*y^0*(1-y)^3+
      (1115/4)*x^2*(1-x)^3*y^1*(1-y)^2+
      (7319/32)*x^2*(1-x)^3*y^2*(1-y)^1+
      (929/16)*x^2*(1-x)^3*y^3*(1-y)^0+
      (25527/256)*x^3*(1-x)^2*y^0*(1-y)^3+
      (31879/128)*x^3*(1-x)^2*y^1*(1-y)^2+
      (12241/64)*x^3*(1-x)^2*y^2*(1-y)^1+
      (2717/64)*x^3*(1-x)^2*y^3*(1-y)^0+
      (185013/4096)*x^4*(1-x)^1*y^0*(1-y)^3+
      (110503/1024)*x^4*(1-x)^1*y^1*(1-y)^2+
      (154345/2048)*x^4*(1-x)^1*y^2*(1-y)^1+
      (13591/1024)*x^4*(1-x)^1*y^3*(1-y)^0+
      (263937/32768)*x^5*(1-x)^0*y^0*(1-y)^3+
      (601117/32768)*x^5*(1-x)^0*y^1*(1-y)^2+
      (47083/4096)*x^5*(1-x)^0*y^2*(1-y)^1+
      (12049/8192)*x^5*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_2 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial ((3/8)+(3/8)*x) ((1/2)+(1/4)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial ((3/8)+(3/8)*x) ((1/2)+(1/4)*y)=
      (263937/32768)*x^0*(1-x)^5*y^0*(1-y)^3+
      (43529/2048)*x^0*(1-x)^5*y^1*(1-y)^2+
      (2370709/131072)*x^0*(1-x)^5*y^2*(1-y)^1+
      (644957/131072)*x^0*(1-x)^5*y^3*(1-y)^0+
      (579633/16384)*x^1*(1-x)^4*y^0*(1-y)^3+
      (744109/8192)*x^1*(1-x)^4*y^1*(1-y)^2+
      (4862533/65536)*x^1*(1-x)^4*y^2*(1-y)^1+
      (1244627/65536)*x^1*(1-x)^4*y^3*(1-y)^0+
      (248013/4096)*x^2*(1-x)^3*y^0*(1-y)^3+
      (154207/1024)*x^2*(1-x)^3*y^1*(1-y)^2+
      (1920497/16384)*x^2*(1-x)^3*y^2*(1-y)^1+
      (457405/16384)*x^2*(1-x)^3*y^3*(1-y)^0+
      (103737/2048)*x^3*(1-x)^2*y^0*(1-y)^3+
      (125539/1024)*x^3*(1-x)^2*y^1*(1-y)^2+
      (753997/8192)*x^3*(1-x)^2*y^2*(1-y)^1+
      (173471/8192)*x^3*(1-x)^2*y^3*(1-y)^0+
      (43221/2048)*x^4*(1-x)^1*y^0*(1-y)^3+
      (13145/256)*x^4*(1-x)^1*y^1*(1-y)^2+
      (327353/8192)*x^4*(1-x)^1*y^2*(1-y)^1+
      (85897/8192)*x^4*(1-x)^1*y^3*(1-y)^0+
      (3789/1024)*x^5*(1-x)^0*y^0*(1-y)^3+
      (5045/512)*x^5*(1-x)^0*y^1*(1-y)^2+
      (37457/4096)*x^5*(1-x)^0*y^2*(1-y)^1+
      (13135/4096)*x^5*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_3 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial ((3/8)+(3/16)*x) ((3/4)+(1/4)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial ((3/8)+(3/16)*x) ((3/4)+(1/4)*y)=
      (644957/131072)*x^0*(1-x)^7*y^0*(1-y)^5+
      (2788947/131072)*x^0*(1-x)^7*y^1*(1-y)^4+
      (4685527/131072)*x^0*(1-x)^7*y^2*(1-y)^3+
      (3776825/131072)*x^0*(1-x)^7*y^3*(1-y)^2+
      (178509/16384)*x^0*(1-x)^7*y^4*(1-y)^1+
      (12049/8192)*x^0*(1-x)^7*y^5*(1-y)^0+
      (8293867/262144)*x^1*(1-x)^6*y^0*(1-y)^5+
      (35289489/262144)*x^1*(1-x)^6*y^1*(1-y)^4+
      (57956441/262144)*x^1*(1-x)^6*y^2*(1-y)^3+
      (45143131/262144)*x^1*(1-x)^6*y^3*(1-y)^2+
      (2013195/32768)*x^1*(1-x)^6*y^4*(1-y)^1+
      (120203/16384)*x^1*(1-x)^6*y^5*(1-y)^0+
      (22750905/262144)*x^2*(1-x)^5*y^0*(1-y)^5+
      (95122935/262144)*x^2*(1-x)^5*y^1*(1-y)^4+
      (152318571/262144)*x^2*(1-x)^5*y^2*(1-y)^3+
      (113981349/262144)*x^2*(1-x)^5*y^3*(1-y)^2+
      (4718025/32768)*x^2*(1-x)^5*y^4*(1-y)^1+
      (231837/16384)*x^2*(1-x)^5*y^5*(1-y)^0+
      (69128905/524288)*x^3*(1-x)^4*y^0*(1-y)^5+
      (283824675/524288)*x^3*(1-x)^4*y^1*(1-y)^4+
      (442382099/524288)*x^3*(1-x)^4*y^2*(1-y)^3+
      (316478449/524288)*x^3*(1-x)^4*y^3*(1-y)^2+
      (11933097/65536)*x^3*(1-x)^4*y^4*(1-y)^1+
      (417041/32768)*x^3*(1-x)^4*y^5*(1-y)^0+
      (251901649/2097152)*x^4*(1-x)^3*y^0*(1-y)^5+
      (1016263119/2097152)*x^4*(1-x)^3*y^1*(1-y)^4+
      (1542666899/2097152)*x^4*(1-x)^3*y^2*(1-y)^3+
      (1054053709/2097152)*x^4*(1-x)^3*y^3*(1-y)^2+
      (35706369/262144)*x^4*(1-x)^3*y^4*(1-y)^1+
      (618917/131072)*x^4*(1-x)^3*y^5*(1-y)^0+
      (276256839/4194304)*x^5*(1-x)^2*y^0*(1-y)^5+
      (1098396117/4194304)*x^5*(1-x)^2*y^1*(1-y)^4+
      (1631844141/4194304)*x^5*(1-x)^2*y^2*(1-y)^3+
      (1074141543/4194304)*x^5*(1-x)^2*y^3*(1-y)^2+
      (33131367/524288)*x^5*(1-x)^2*y^4*(1-y)^1+
      (38391/262144)*x^5*(1-x)^2*y^5*(1-y)^0+
      (10612151/524288)*x^6*(1-x)^1*y^0*(1-y)^5+
      (5231799/65536)*x^6*(1-x)^1*y^1*(1-y)^4+
      (61586083/524288)*x^6*(1-x)^1*y^2*(1-y)^3+
      (20030941/262144)*x^6*(1-x)^1*y^3*(1-y)^2+
      (1215291/65536)*x^6*(1-x)^1*y^4*(1-y)^1+
      (67/8192)*x^6*(1-x)^1*y^5*(1-y)^0+
      (11363659/4194304)*x^7*(1-x)^0*y^0*(1-y)^5+
      (44949297/4194304)*x^7*(1-x)^0*y^1*(1-y)^4+
      (66852473/4194304)*x^7*(1-x)^0*y^2*(1-y)^3+
      (44903227/4194304)*x^7*(1-x)^0*y^3*(1-y)^2+
      (1528491/524288)*x^7*(1-x)^0*y^4*(1-y)^1+
      (36971/262144)*x^7*(1-x)^0*y^5*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_4 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial ((9/16)+(3/16)*x) ((3/4)+(1/4)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial ((9/16)+(3/16)*x) ((3/4)+(1/4)*y)=
      (11363659/4194304)*x^0*(1-x)^5*y^0*(1-y)^3+
      (22221979/4194304)*x^0*(1-x)^5*y^1*(1-y)^2+
      (1380607/524288)*x^0*(1-x)^5*y^2*(1-y)^1+
      (36971/262144)*x^0*(1-x)^5*y^3*(1-y)^0+
      (12866675/1048576)*x^1*(1-x)^4*y^0*(1-y)^3+
      (25405757/1048576)*x^1*(1-x)^4*y^1*(1-y)^2+
      (1713383/131072)*x^1*(1-x)^4*y^2*(1-y)^1+
      (110377/65536)*x^1*(1-x)^4*y^3*(1-y)^0+
      (3054395/131072)*x^2*(1-x)^3*y^0*(1-y)^3+
      (6455375/131072)*x^2*(1-x)^3*y^1*(1-y)^2+
      (540503/16384)*x^2*(1-x)^3*y^2*(1-y)^1+
      (68695/8192)*x^2*(1-x)^3*y^3*(1-y)^0+
      (779759/32768)*x^3*(1-x)^2*y^0*(1-y)^3+
      (1866005/32768)*x^3*(1-x)^2*y^1*(1-y)^2+
      (200123/4096)*x^3*(1-x)^2*y^2*(1-y)^1+
      (35401/2048)*x^3*(1-x)^2*y^3*(1-y)^0+
      (217247/16384)*x^4*(1-x)^1*y^0*(1-y)^3+
      (601559/16384)*x^4*(1-x)^1*y^1*(1-y)^2+
      (77939/2048)*x^4*(1-x)^1*y^2*(1-y)^1+
      (15895/1024)*x^4*(1-x)^1*y^3*(1-y)^0+
      (13135/4096)*x^5*(1-x)^0*y^0*(1-y)^3+
      (41353/4096)*x^5*(1-x)^0*y^1*(1-y)^2+
      (6019/512)*x^5*(1-x)^0*y^2*(1-y)^1+
      (1301/256)*x^5*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_5 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadPolynomial ((3/4)+(1/4)*x) ((1/4)+(3/4)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadPolynomial ((3/4)+(1/4)*x) ((1/4)+(3/4)*y)=
      (21587/4096)*x^0*(1-x)^5*y^0*(1-y)^3+
      (44145/4096)*x^0*(1-x)^5*y^1*(1-y)^2+
      (2445/512)*x^0*(1-x)^5*y^2*(1-y)^1+
      (1301/256)*x^0*(1-x)^5*y^3*(1-y)^0+
      (45059/2048)*x^1*(1-x)^4*y^0*(1-y)^3+
      (46779/1024)*x^1*(1-x)^4*y^1*(1-y)^2+
      (7083/256)*x^1*(1-x)^4*y^2*(1-y)^1+
      (1235/32)*x^1*(1-x)^4*y^3*(1-y)^0+
      (8917/256)*x^2*(1-x)^3*y^0*(1-y)^3+
      (9879/128)*x^2*(1-x)^3*y^1*(1-y)^2+
      (1191/16)*x^2*(1-x)^3*y^2*(1-y)^1+
      (457/4)*x^2*(1-x)^3*y^3*(1-y)^0+
      (3229/128)*x^3*(1-x)^2*y^0*(1-y)^3+
      (2121/32)*x^3*(1-x)^2*y^1*(1-y)^2+
      (1737/16)*x^3*(1-x)^2*y^2*(1-y)^1+
      (659/4)*x^3*(1-x)^2*y^3*(1-y)^0+
      (61/8)*x^4*(1-x)^1*y^0*(1-y)^3+
      30*x^4*(1-x)^1*y^1*(1-y)^2+
      81*x^4*(1-x)^1*y^2*(1-y)^1+
      116*x^4*(1-x)^1*y^3*(1-y)^0+
      (1/2)*x^5*(1-x)^0*y^0*(1-y)^3+
      6*x^5*(1-x)^0*y^1*(1-y)^2+
      24*x^5*(1-x)^0*y^2*(1-y)^1+
      32*x^5*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadPolynomial
    ring
  rw [he]
  positivity

theorem half_polynomial_box_6 (x y : ℝ) (hx0 : 0≤x) (hx1 : x≤1)
    (hy0 : 0≤y) (hy1 : y≤1) :
    0≤halfHeadRemainder ((3/4)+(1/4)*x) (0+(1/4)*y) := by
  have hxc : 0≤1-x := by linarith
  have hyc : 0≤1-y := by linarith
  have he : halfHeadRemainder ((3/4)+(1/4)*x) (0+(1/4)*y)=
      (53/2)*x^0*(1-x)^4*y^0*(1-y)^3+
      (4879/64)*x^0*(1-x)^4*y^1*(1-y)^2+
      (71633/1024)*x^0*(1-x)^4*y^2*(1-y)^1+
      (19539/1024)*x^0*(1-x)^4*y^3*(1-y)^0+
      111*x^1*(1-x)^3*y^0*(1-y)^3+
      (20431/64)*x^1*(1-x)^3*y^1*(1-y)^2+
      (74525/256)*x^1*(1-x)^3*y^2*(1-y)^1+
      (39939/512)*x^1*(1-x)^3*y^3*(1-y)^0+
      (349/2)*x^2*(1-x)^2*y^0*(1-y)^3+
      (2007/4)*x^2*(1-x)^2*y^1*(1-y)^2+
      (14541/32)*x^2*(1-x)^2*y^2*(1-y)^1+
      (7637/64)*x^2*(1-x)^2*y^3*(1-y)^0+
      122*x^3*(1-x)^1*y^0*(1-y)^3+
      (1403/4)*x^3*(1-x)^1*y^1*(1-y)^2+
      (1261/4)*x^3*(1-x)^1*y^2*(1-y)^1+
      (2589/32)*x^3*(1-x)^1*y^3*(1-y)^0+
      32*x^4*(1-x)^0*y^0*(1-y)^3+
      92*x^4*(1-x)^0*y^1*(1-y)^2+
      82*x^4*(1-x)^0*y^2*(1-y)^1+
      (41/2)*x^4*(1-x)^0*y^3*(1-y)^0 := by
    unfold halfHeadRemainder
    ring
  rw [he]
  positivity

theorem halfHeadPolynomial_nonneg (r t : ℝ) (hr0 : 0≤r) (hr1 : r≤1)
    (ht0 : 0≤t) (ht1 : t≤1) : 0≤halfHeadPolynomial r t := by
  by_cases hr : r≤3/4
  · by_cases ht : t≤1/2
    · have hh := half_polynomial_box_0 (r/(3/4)) (t/(1/2)) (by positivity) (by norm_num;linarith) (by positivity) (by norm_num;linarith)
      convert hh using 1; congr 1 <;> ring
    · by_cases hr2 : r≤3/8
      · have hh := half_polynomial_box_1 (r/(3/8)) ((t-1/2)/(1/2)) (by positivity) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith)
        convert hh using 1; congr 1 <;> ring
      · by_cases ht2 : t≤3/4
        · have hh := half_polynomial_box_2 ((r-3/8)/(3/8)) ((t-1/2)/(1/4)) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith)
          convert hh using 1; congr 1 <;> ring
        · by_cases hr3 : r≤9/16
          · have hh := half_polynomial_box_3 ((r-3/8)/(3/16)) ((t-3/4)/(1/4)) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith)
            convert hh using 1; congr 1 <;> ring
          · have hh := half_polynomial_box_4 ((r-9/16)/(3/16)) ((t-3/4)/(1/4)) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith)
            convert hh using 1; congr 1 <;> ring
  · by_cases ht : 1/4≤t
    · have hh := half_polynomial_box_5 ((r-3/4)/(1/4)) ((t-1/4)/(3/4)) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith) (by norm_num;linarith)
      convert hh using 1; congr 1 <;> ring
    · have hh := half_polynomial_box_6 ((r-3/4)/(1/4)) (t/(1/4)) (by norm_num;linarith) (by norm_num;linarith) (by positivity) (by norm_num;linarith)
      have hR : 0≤halfHeadRemainder r t := by convert hh using 1; congr 1 <;> ring
      have he : halfHeadPolynomial r t=32*t^3+(1-r)*halfHeadRemainder r t := by unfold halfHeadPolynomial halfHeadRemainder;ring
      rw [he]
      exact add_nonneg (by positivity) (mul_nonneg (by linarith) hR)

end APPTSubunit
