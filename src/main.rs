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

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TyBool => write!(f, "Bool"),
            Self::TyInt => write!(f, "Int"),
            Self::TyFun(a, b) => write!(f, "{} → {}", *a, *b),
        }
    }
}

impl Context {
    pub fn check(&mut self, t: &Term) -> bool {
        let ty = self.type_of_term(t.clone()).unwrap();
        match ty {
            Type::TyInt => true,
            _ => false,
        }
    }

    pub fn type_of_term(&mut self, t: Term) -> Result<Type, String> {
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

            Term::TmIf(ref t1, t2, t3) => {
                let ty1 = self.type_of_term(*t1.clone())?;
                let type_of_t1 = ty1.clone();

                assert_eq!(type_of_t1, Type::TyBool);

                let ty2 = self.type_of_term(*t2)?;
                let ty3 = self.type_of_term(*t3)?;

                assert_eq!(ty2, ty3);

                return Ok(ty2);
            }

            Term::TmApp(t1, t2) => {
                let ty1 = self.type_of_term(*t1)?;
                let ty2 = self.type_of_term(*t2)?;

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
                let tyy = self.type_of_term(*t)?;

                Ok(Type::TyFun(Box::new(ty.clone()), Box::new(tyy)))
            }

            Term::TmAdd(ref t1, ref t2) => {
                if self.check(t1) && self.check(t2) {
                    return Ok(Type::TyInt);
                }
                Err(String::from("Types do not match"))
            }
        }
    }
}

fn main() {
    let mut ctx = Context(std::collections::HashMap::new());
    let term = Term::TmAbs("f".to_owned(), 
        Type::TyFun(Box::new(Type::TyBool),Box::new(Type::TyInt)), 
        Box::new(Term::TmVar("f".to_owned())));
    let type_check = ctx.type_of_term(term).unwrap();
    println!("{}", type_check);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn term_is_unbounded() {
        let mut ctx = Context(std::collections::HashMap::new());
        let termvar = Term::TmVar("x".to_owned());

        let type_check = ctx.type_of_term(termvar);
        assert_eq!(type_check, Err(String::from("Unbounded variable")));
    }

    #[test]
    fn type_is_int() {
        let mut ctx = Context(std::collections::HashMap::new());
        let termvar = Term::TmVar("x".to_owned());
        ctx.0.insert("x".to_owned(), Type::TyInt);

        let type_check = ctx.type_of_term(termvar);
        assert_eq!(type_check, Ok(Type::TyInt));
    }

    #[test]
    fn add() {
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

        let mut ctx = Context(std::collections::HashMap::new());
        let ctx1 = ctx.type_of_term(tmadd);

        assert_eq!(
            ctx1,
            Ok(Type::TyFun(
                Box::new(Type::TyInt),
                Box::new(Type::TyFun(Box::new(Type::TyInt), Box::new(Type::TyInt)))
            ))
        );
    }

    #[test]
    fn identity() {
        let tmbool = Term::TmAbs(
            "x".to_owned(),
            Type::TyBool,
            Box::new(Term::TmVar(String::from("x"))),
        );
        let mut ctx = Context(std::collections::HashMap::new());
        let ctx1 = ctx.type_of_term(tmbool);

        assert_eq!(
            ctx1,
            Ok(Type::TyFun(Box::new(Type::TyBool), Box::new(Type::TyBool)))
        );
    }

    #[test]
    fn int() {
        let int = Term::TmInt(351);
        let mut ctx = Context(std::collections::HashMap::new());
        let ctx1 = ctx.type_of_term(int);

        assert_eq!(ctx1, Ok(Type::TyInt));
    }

    #[test]
    fn boolean() {
        let btrue = Term::TmTrue;
        let mut ctx = Context(std::collections::HashMap::new());
        let ctx1 = ctx.type_of_term(btrue);

        assert_eq!(ctx1, Ok(Type::TyBool));
    }

    #[test]
    fn boolean_false() {
        let bfalse = Term::TmFalse;
        let mut ctx = Context(std::collections::HashMap::new());
        let ctx1 = ctx.type_of_term(bfalse);

        assert_eq!(ctx1, Ok(Type::TyBool));
    }
}
