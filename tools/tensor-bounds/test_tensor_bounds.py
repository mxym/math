from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import unittest
import tensor_bounds as t

HERE = Path(__file__).parent

class TestBounds(unittest.TestCase):
    def graph(self,name):
        return json.loads((HERE/(name+".json")).read_text())

    def test_c5(self):
        g=self.graph("c5")
        r=t.solve(g,2,512)
        self.assertEqual(r["max_cut"]["exponent"],"4")
        self.assertEqual(r["combined_lower_bound"]["exponent"],"49/12")
        self.assertTrue(r["combined_lower_bound"]["depends_on_rectangular_theorem"])
        self.assertEqual(r["search"]["visited"],16)
        self.assertEqual(t.verify(g,r["combined_lower_bound"]),r["combined_lower_bound"])

    def test_complete_and_rational(self):
        g=self.graph("k5")
        for a in g["edges"]:
            a[2]="1/2"
        r=t.solve(g,0)
        self.assertEqual(r["max_cut"]["exponent"],"3")
        self.assertEqual(r["combined_lower_bound"]["exponent"],"25/8")
        self.assertEqual(t.rectangle([0,2,1]),3)

    def test_splice_certificate_and_caps(self):
        g={"vertices":3,"edges":[[0,1,"1/2"],[1,2,1]]}
        n,es,ix,scale,w=t.load_graph(g)
        new=t.move(w,ix,0,1,2,1)
        c=t.cert(es,scale,new,(0,0,1),[[0,1,2,"1/2"]])
        self.assertEqual(t.verify(g,c),c)
        self.assertEqual(c["exponent"],"1")
        for field,replacement in [("exponent","17"),("splices",[[0,1,2,"1"]]),("partition",[0,0,0]),("crossing_weights",["99","0","0"])]:
            d=deepcopy(c); d[field]=replacement
            with self.assertRaises(ValueError):
                t.verify(g,d)
        self.assertTrue(t.solve(self.graph("c5"),2,1)["search"]["state_limit_hit"])

    def test_all_c5_cut_caps_on_half_grid(self):
        for x,y,z in [(Fraction(a,2),Fraction(b,2),Fraction(c,2))
                      for a in range(9) for b in range(9) for c in range(9)]:
            # x is the edge between nonsingleton groups in the first case,
            # and z the edge between singleton groups in the second.
            if x+y<=4 and x+z<=4 and y+z<=2:
                self.assertLessEqual(t.rectangle([x,y,z]),Fraction(49,12))
            if x+z<=2 and y+z<=2 and x+y<=4:
                self.assertLessEqual(t.rectangle([x,y,z]),4)

if __name__=="__main__":
    unittest.main()
