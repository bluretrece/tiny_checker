#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    TyFun(Box<Type>, Box<Type>),
    TyBool,
    TyInt,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    TmTrue,
    TmFalse,
    TmInt(i32),
    TmVar(String),
    TmAbs(String, Type, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmAdd(Box<Term>, Box<Term>),
    TmIf(Box<Term>, Box<Term>, Box<Term>),
}

#[derive(Debug, PartialEq, Clone)]
pub struct Context(std::collections::HashMap<String, Type>);

impl Context {
    pub fn check(&mut self, t: &Term) -> bool {
        let ty = self.type_of(t.clone()).unwrap();
        match ty {
            Type::TyInt => true,
            _ => false,
        }
    }

    pub fn type_of(&mut self, t: Term) -> Result<Type, String> {
        match t {
            Term::TmTrue => Ok(Type::TyBool),

            Term::TmFalse => Ok(Type::TyBool),

            Term::TmInt(_) => Ok(Type::TyInt),

            Term::TmVar(x) => {
                if let Some(v) = self.0.get(&x) {
                    return Ok(v.clone());
                } else {
                    Err(String::from("Unbounded variable"))
                }
            }

            Term::TmApp(t1, t2) => {
                let ty1 = self.type_of(*t1)?;
                let ty2 = self.type_of(*t2)?;

                match ty1 {
                    Type::TyFun(ty11, ty12) => {
                        if ty2 == *ty11 {
                            return Ok(*ty12);
                        }
                        Err(String::from("Wront argument type"))
                    }
                    _ => unreachable!(),
                }
            }

            Term::TmAbs(x, ref ty, t) => {
                self.0.insert(x, ty.clone());
                let tyy = self.type_of(*t)?;

                Ok(Type::TyFun(Box::new(ty.clone()), Box::new(tyy)))
            }

            Term::TmAdd(ref t1, ref t2) => {
                if self.check(t1) && self.check(t2) {
                    return Ok(Type::TyInt);
                }
                Err(String::from("Types do not match"))
            }
            _ => unreachable!(),
        }
    }
}

fn main() {
    let tmidbool = Term::TmAbs(
        "x".to_owned(),
        Type::TyBool,
        Box::new(Term::TmVar(String::from("x"))),
    );

    let tmadd = Term::TmAbs(
        "x".to_owned(),
        Type::TyInt,
        Box::new(Term::TmAbs(
            "y".to_owned(),
            Type::TyInt,
            Box::new(Term::TmAdd(
                Box::new(Term::TmVar("x".to_owned())),
                Box::new(Term::TmVar("y".to_owned())),
            )),
        )),
    );

    // let mut ctx = Context(std::collections::HashMap::new());
    let mut ctx = Context(std::collections::HashMap::new());

    let int_term = Term::TmVar("x".to_owned());
    println!("{:?}", ctx.type_of(tmadd));
}
