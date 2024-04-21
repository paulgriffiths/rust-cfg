use crate::errors::{Error, Result};
use rug::ops::Pow;
use rug::Integer;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

pub enum Value {
    Integer(Integer),
    Real(f64),
}

impl Clone for Value {
    /// Clones a value
    fn clone(&self) -> Value {
        match self {
            Value::Integer(n) => Value::Integer(n.clone()),
            Value::Real(r) => Value::Real(*r),
        }
    }
}

impl fmt::Debug for Value {
    /// Formats a value for debugging
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Integer(n) => write!(f, "(Integer) {}", n),
            Value::Real(r) => write!(f, "(Real) {}", r),
        }
    }
}

impl fmt::Display for Value {
    /// Formats a value as a string
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Value::Integer(n) => write!(f, "{}", n),
            Value::Real(r) => write!(f, "{}", r),
        }
    }
}

impl PartialEq for Value {
    /// Tests two Values for equality.
    fn eq(&self, other: &Value) -> bool {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => first == second,
                Value::Real(second) => first == second,
            },
            Value::Real(first) => match other {
                Value::Integer(second) => first == second,
                Value::Real(second) => first == second,
            },
        }
    }
}

impl Add for Value {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first + second),
                Value::Real(second) => Value::Real(first.to_f64() + second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first + second.to_f64()),
                Value::Real(second) => Value::Real(first + second),
            },
        }
    }
}

impl Sub for Value {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first - second),
                Value::Real(second) => Value::Real(first.to_f64() - second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first - second.to_f64()),
                Value::Real(second) => Value::Real(first - second),
            },
        }
    }
}

impl Mul for Value {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first * second),
                Value::Real(second) => Value::Real(first.to_f64() * second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first * second.to_f64()),
                Value::Real(second) => Value::Real(first * second),
            },
        }
    }
}

impl Div for Value {
    type Output = Self;

    fn div(self, other: Self) -> Self {
        match self {
            Value::Integer(first) => match other {
                Value::Integer(second) => Value::Integer(first / second),
                Value::Real(second) => Value::Real(first.to_f64() / second),
            },
            Value::Real(first) => match other {
                Value::Integer(second) => Value::Real(first / second.to_f64()),
                Value::Real(second) => Value::Real(first / second),
            },
        }
    }
}

impl Neg for Value {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Value::Integer(n) => Value::Integer(-n),
            Value::Real(r) => Value::Real(-r),
        }
    }
}

impl Value {
    /// Creates a new integer value from a decimal string representation
    pub fn new_integer(value: &str) -> Result<Value> {
        match Integer::from_str_radix(value, 10) {
            Err(_) => Err(Error::InvalidInteger(value.to_string())),
            Ok(n) => Ok(Value::Integer(n)),
        }
    }

    /// Creates a new real value from a decimal string representation
    pub fn new_real(value: &str) -> Result<Value> {
        match value.parse::<f64>() {
            Err(_) => Err(Error::InvalidReal(value.to_string())),
            Ok(f) => Ok(Value::Real(f)),
        }
    }

    /// Performs exponentiation on a value
    pub fn pow(self, exp: Value) -> Self {
        match self {
            Value::Integer(base) => match exp {
                Value::Integer(exp) => {
                    let Some(e) = exp.to_u32() else {
                        panic!("exponent out of range");
                    };
                    Value::Integer(base.pow(e))
                }
                Value::Real(exp) => Value::Real(base.to_f64().powf(exp)),
            },
            Value::Real(base) => match exp {
                Value::Integer(exp) => Value::Real(base.powf(exp.to_f64())),
                Value::Real(exp) => Value::Real(base.powf(exp)),
            },
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_display() -> Result<()> {
        assert_eq!(format!("{}", Value::new_integer("12")?), "12");
        assert_eq!(format!("{}", Value::new_real("42.5")?), "42.5");

        Ok(())
    }

    #[test]
    fn test_eq() -> Result<()> {
        let cases = &[
            Value::new_integer("12")?,
            Value::new_integer("12")?,
            Value::new_integer("42")?,
            Value::new_real("12.0")?,
            Value::new_real("12.0")?,
            Value::new_real("42.0")?,
        ];
        assert_eq!(cases[0], cases[1]);
        assert_ne!(cases[0], cases[2]);
        assert_eq!(cases[0], cases[3]);
        assert_ne!(cases[0], cases[5]);
        assert_eq!(cases[3], cases[4]);
        assert_ne!(cases[3], cases[5]);
        assert_eq!(cases[3], cases[0]);
        assert_ne!(cases[3], cases[2]);

        Ok(())
    }

    #[test]
    fn test_ops() -> Result<()> {
        let cases = &[
            Value::new_integer("12")?,
            Value::new_integer("3")?,
            Value::new_real("25.0")?,
            Value::new_real("2.0")?,
            Value::new_integer("10")?,
        ];

        assert_eq!(
            cases[0].clone() + cases[1].clone(),
            Value::new_integer("15")?
        );
        assert_eq!(
            cases[0].clone() - cases[1].clone(),
            Value::new_integer("9")?
        );
        assert_eq!(
            cases[0].clone() * cases[1].clone(),
            Value::new_integer("36")?
        );
        assert_eq!(
            cases[0].clone() / cases[1].clone(),
            Value::new_integer("4")?
        );
        assert_eq!(-cases[0].clone(), Value::new_integer("-12")?);
        assert_eq!(
            cases[0].clone().pow(cases[1].clone()),
            Value::new_integer("1728")?
        );

        assert_eq!(cases[2].clone() + cases[3].clone(), Value::new_real("27")?);
        assert_eq!(cases[2].clone() - cases[3].clone(), Value::new_real("23")?);
        assert_eq!(cases[2].clone() * cases[3].clone(), Value::new_real("50")?);
        assert_eq!(
            cases[2].clone() / cases[3].clone(),
            Value::new_real("12.5")?
        );
        assert_eq!(-cases[2].clone(), Value::new_real("-25")?);
        assert_eq!(
            cases[2].clone().pow(cases[3].clone()),
            Value::new_real("625")?
        );

        assert_eq!(cases[0].clone() + cases[2].clone(), Value::new_real("37")?);
        assert_eq!(cases[0].clone() - cases[2].clone(), Value::new_real("-13")?);
        assert_eq!(cases[0].clone() * cases[2].clone(), Value::new_real("300")?);
        assert_eq!(cases[0].clone() / cases[3].clone(), Value::new_real("6")?);
        assert_eq!(
            cases[0].clone().pow(cases[3].clone()),
            Value::new_real("144")?
        );

        assert_eq!(cases[2].clone() + cases[1].clone(), Value::new_real("28")?);
        assert_eq!(cases[2].clone() - cases[1].clone(), Value::new_real("22")?);
        assert_eq!(cases[2].clone() * cases[1].clone(), Value::new_real("75")?);
        assert_eq!(cases[2].clone() / cases[4].clone(), Value::new_real("2.5")?);
        assert_eq!(
            cases[2].clone().pow(cases[1].clone()),
            Value::new_real("15625")?
        );

        Ok(())
    }
}
