from fractions import Fraction as F
from itertools import product
import unittest
import soft_core as s

class Tests(unittest.TestCase):
    def test_bias_exact_with_shared_colors(self):
        d={"p":"2/3","epsilon":"1/2","m":2,"buckets":[["a","x",4],["a","y",3],["a","z",1],["b","x",7],["b","z",2]]}
        p,e,m,rows=s.parse(d)
        ans=F(0)
        for flags in product((0,1),repeat=3):
            active=dict(zip("xyz",flags))
            mass=0
            for row in rows.values():
                good=[w for c,w in row if active[c]]
                if len(good)>=m:mass+=sum(good)
            i=sum(flags);ans+=mass*p**i*(1-p)**(3-i)
        self.assertEqual(ans,s.expected_survivors(rows,dict.fromkeys("xyz",p),m))

    def test_hypergeometric_expectation(self):
        rows={"a":[("x",F(4)),("y",F(1))],"b":[("x",F(3)),("z",F(2))]}
        self.assertEqual(s.expected_fixed(rows,set(),set("xyz"),2,2),F(10,3))
        self.assertEqual(s.expected_fixed(rows,{"x"},set("yz"),1,2),F(5))
    def test_diffuse_and_conditional_expectation(self):
        d={"p":"3/4","epsilon":"3/4","m":2,"buckets":[[a,str(i),1] for a in ("a","b") for i in range(24)]}
        c=s.materialize(d)
        self.assertEqual(c["branch"],"sample")
        self.assertGreaterEqual(F(c["kept_mass"]),F(c["initial_expected_retained"]))
        self.assertEqual(len(c["selected_colors"]),18)
        self.assertEqual(c["kept_mass"],"36")

    def test_concentrated_has_bounded_support(self):
        d={"p":"1/2","epsilon":"1/2","m":2,"buckets":[["a","x",100]]+ [["a",str(i),1] for i in range(24)]}
        c=s.materialize(d)
        self.assertEqual(c["branch"],"restrict")
        self.assertEqual(len(c["kept_buckets"]),c["K"])
        self.assertGreater(F(c["kept_mass"]),F(c["head_threshold"]))

    def test_pathwise_bound_for_all_deletion_orders(self):
        rows={"a":[("x",F(3)),("y",F(2)),("z",F(1))], "b":[("y",F(5)),("z",F(1))]}
        for flags in product((0,1),repeat=3):
            active=dict(zip("xyz",flags))
            for row in rows.values():
                chosen=[w for c,w in row if active[c]]
                for state in product((0,1),repeat=len(chosen)):
                    if sum(state)<2:
                        self.assertLessEqual(sum(w*u for w,u in zip(chosen,state)),max(chosen,default=F(0)))

if __name__=='__main__':unittest.main()
