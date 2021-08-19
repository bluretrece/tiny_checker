use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;

#[derive(Debug, PartialEq, Clone)]
pub struct Polytype {
    pub vars: Vec<TypeVar>,
    pub ty: Type,
}

impl Polytype {
    pub fn ftv(&self) -> HashSet<TypeVar> {
        self.ty
            .ftv()
            .difference(&self.vars.iter().cloned().collect())
            .cloned()
            .collect()
    }

    pub fn instantiate(&self, tv: &mut TypeVarGen) -> Type {
        let newvars = self.vars.iter().map(|_| Type::TyVar(tv.next()));
        self.ty
            .subst_type(&Subst(self.vars.iter().cloned().zip(newvars).collect()))
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct TypeVar(usize);

pub struct TypeVarGen {
    supply: usize,
}

impl TypeVarGen {
    pub fn new() -> Self {
        Self { supply: 0 }
    }

    pub fn next(&mut self) -> TypeVar {
        let v = TypeVar(self.supply);
        self.supply += 1;
        v
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    TyVar(TypeVar),
    TyFun(Box<Type>, Box<Type>),
    TyBool,
    TyInt,
}

impl TypeVar {
    pub fn bind(&self, t: &Type) -> Subst {
        if let &Type::TyVar(ref u) = t {
            if u == self {
                return Subst::new();
            }
        }

        if occurs_in(t.clone(), self.0.to_string()) {
            String::from("Infinite type");
            unimplemented!()
        } else {
            let mut subst = Subst::new();
            subst.0.insert(self.clone(), t.clone());
            subst
        }
    }
}
pub fn occurs_in(t: Type, name: String) -> bool {
    match t {
        Type::TyBool => false,
        Type::TyInt => false,
        Type::TyVar(y) => return y.0.to_string() == name,
        Type::TyFun(t1, t2) => occurs_in(*t1, name.clone()) || occurs_in(*t2, name.clone()),
    }
}

impl Type {
    pub fn ftv(&self) -> HashSet<TypeVar> {
        match self {
            Type::TyBool | Type::TyInt => HashSet::new(),
            Type::TyVar(ref x) => [x.clone()].iter().cloned().collect(),
            Type::TyFun(ref x, ref y) => x.ftv().union(&y.ftv()).cloned().collect(),
        }
    }
    pub fn unify(&self, t2: &Type) -> Subst {
        match (self, t2) {
            (Type::TyBool, Type::TyBool) => Subst::new(),
            (t1, &Type::TyVar(ref x)) => x.bind(&t1),
            (&Type::TyVar(ref x), t2) => x.bind(&t2),
            (&Type::TyInt, Type::TyInt) => Subst::new(),
            (&Type::TyFun(ref in1, ref out1), Type::TyFun(ref in2, ref out2)) => {
                let s1 = in1.unify(&*in2);
                let s2 = out1.subst_type(&s1).unify(&out2.subst_type(&s1));

                s1.compose_subst(s2)
            }
            _ => unreachable!(), // Cannot unify!
        }
    }

    pub fn subst_type(&self, s: &Subst) -> Type {
        match self {
            Type::TyVar(ref x) => {
                s.0.get(&x).cloned().unwrap_or(self.clone())
                // if self.0.contains_key(x) {
                //     self.0.get(x).unwrap().clone()
                // } else {
                //     t.clone()
                // }
            }
            Type::TyFun(t1, t2) => {
                Type::TyFun(Box::new(t1.subst_type(s)), Box::new(t2.subst_type(s)))
            }
            Type::TyBool => self.clone(),
            Type::TyInt => self.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    TmTrue,
    TmFalse,
    TmInt(i32),
    TmVar(String),
    TmAbs(String, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmAdd(Box<Term>, Box<Term>),
    TmIf(Box<Term>, Box<Term>, Box<Term>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Context(std::collections::HashMap<String, Polytype>);

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TyBool => write!(f, "Bool"),
            Self::TyInt => write!(f, "Int"),
            Self::TyFun(a, b) => write!(f, "{} → {}", *a, *b),
            Self::TyVar(tv) => write!(f, "{}", tv.0),
        }
    }
}

impl Context {
    // pub fn check(&mut self, t: &Term) -> bool {
    //     let ty = self.type_of_term(t.clone()).unwrap();
    //     match ty {
    //         Type::TyInt => true,
    //         _ => false,
    //     }
    // }

    pub fn type_of_term(&mut self, t: Term, tvg: &mut TypeVarGen) -> Result<(Subst, Type), String> {
        match t {
            Term::TmTrue | Term::TmFalse => Ok((Subst::new(), Type::TyBool)),
            Term::TmInt(_) => Ok((Subst::new(), Type::TyInt)),

            Term::TmVar(ref x) => match self.0.get(x) {
                Some(s) => Ok((Subst::new(), s.instantiate(tvg))),
                None => Err(String::from("Unbound variable")),
            },

            Term::TmIf(ref t1, t2, t3) => {
                unimplemented!()
                // let ty1 = self.type_of_term(*t1.clone())?;
                // let type_of_t1 = ty1.clone();

                // assert_eq!(type_of_t1, Type::TyBool);

                // let ty2 = self.type_of_term(*t2)?;
                // let ty3 = self.type_of_term(*t3)?;

                // assert_eq!(ty2, ty3);

                // return Ok(ty2);
            }

            Term::TmApp(t1, t2) => {
                let (s1, t1) = self.type_of_term(*t1, tvg)?;
                let (s2, t2) = self.type_of_term(*t2, tvg)?;
                let tv = Type::TyVar(tvg.next());
                let s3 = t1
                    .subst_type(&s2)
                    .unify(&Type::TyFun(Box::new(t2), Box::new(tv.clone())));

                Ok((s3.compose_subst(s2.compose_subst(s1)), tv.subst_type(&s3)))
            }

            Term::TmAbs(ref x, t) => {
                let tv = Type::TyVar(tvg.next());
                let mut env = self.clone();
                env.0.remove(x);
                env.0.insert(
                    x.clone(),
                    Polytype {
                        vars: Vec::new(),
                        ty: tv.clone(),
                    },
                );

                let (s1, t1) = env.type_of_term(*t, tvg)?;
                Ok((
                    s1.clone(),
                    Type::TyFun(Box::new(tv.subst_type(&s1)), Box::new(t1)),
                ))
            }

            Term::TmAdd(t1, t2) => {
                unimplemented!()
                // let (s1, t1) = self.type_of_term(*t1, tvg)?;
                // let (s2, t2) = self.type_of_term(*t2, tvg)?;

                // let tt = t1.unify(&t2);

                // Ok((tt.compose_subst(s2), ))
            }
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Subst(HashMap<TypeVar, Type>);

trait Union {
    fn union(&self, other: &Self) -> Self;
}

impl<K, V> Union for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn union(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (key, value) in other {
            res.entry(key.clone()).or_insert(value.clone());
        }

        res
    }
}

impl Subst {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn compose_subst(&self, s2: Subst) -> Subst {
        Subst(
            self.0.union(
                &s2.0
                    .iter()
                    .map(|(k, v)| (k.clone(), v.subst_type(self)))
                    .collect(),
            ),
        )
    }
}

/// \forall X. X -> X
// pub fn ty_id() -> Polytype {
//     Polytype {
//         vars: vec![],
//         ty: Type::TyFun(
//             Box::new(Type::TyVar("X".to_owned())),
//             Box::new(Type::TyVar("X".to_owned())),
//         ),
//     }
// }

pub fn tm_id() -> Term {
    Term::TmAbs("x".to_owned(), Box::new(Term::TmVar("x".to_owned())))
}

fn main() {
    let termvar = app(
        app(Term::TmVar("+".to_string()), Term::TmInt(2)),
        Term::TmTrue,
    );
    let mut env = Context(HashMap::new());
    let mut tv = TypeVarGen::new();
    env.0.insert(
        "+".to_owned(),
        Polytype {
            vars: Vec::new(),
            ty: Type::TyFun(
                Box::new(Type::TyInt),
                Box::new(Type::TyFun(Box::new(Type::TyInt), Box::new(Type::TyInt))),
            ),
        },
    );

    let (_, type_check) = env.type_of_term(termvar, &mut tv).unwrap();
    println!("{:?}", type_check);
}

pub fn app(e1: Term, e2: Term) -> Term {
    Term::TmApp(Box::new(e1), Box::new(e2))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[ignore]
    #[test]
    fn boolean() {
        let termvar = Term::TmTrue;
        let mut env = Context(HashMap::new());
        let mut tv = TypeVarGen::new();

        let (_, type_check) = env.type_of_term(termvar, &mut tv).unwrap();
        println!("{:?}", type_check);
        assert_eq!(type_check, Type::TyBool);
    }

    #[test]
    fn add_fun() {
        let termvar = app(
            app(Term::TmVar("+".to_string()), Term::TmInt(2)),
            Term::TmInt(4),
        );
        let mut env = Context(HashMap::new());
        let mut tv = TypeVarGen::new();
        // env.insert("+".to_owned(),
        //        Polytype {
        //            vars: Vec::new(),
        //            ty: Type::TyFun(Box::new(Type::TyInt), Box::new(TyFun(Box::new(Type::TyInt), Box::new(Type::TyInt)))),
        //        });

        let (_, type_check) = env.type_of_term(termvar, &mut tv).unwrap();
        println!("{:?}", type_check);
        assert_eq!(type_check, Type::TyInt);
    }
    #[ignore]
    #[test]
    fn int() {
        let termvar = Term::TmInt(5);
        let mut env = Context(HashMap::new());
        let mut tv = TypeVarGen::new();

        let (_, type_check) = env.type_of_term(termvar, &mut tv).unwrap();
        println!("{:?}", type_check);
        assert_eq!(type_check, Type::TyInt);
    }
    #[ignore]
    #[test]
    fn term_is_unbounded() {
        let termvar = Term::TmVar("x".to_owned());
        let mut env = Context(HashMap::new());
        let mut tv = TypeVarGen::new();

        let type_check = env.type_of_term(termvar, &mut tv);
        println!("{:?}", type_check);
        assert_eq!(type_check, Err(String::from("Unbound variable")));
    }
}
