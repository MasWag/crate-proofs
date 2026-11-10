//! Explicit byte, cursor, and format flags outline release parse_sign!.
//! The returned cursor exposes the source iterator's mutation on every branch.
use lexical_util::error::Error;

pub fn parse_sign_state(
    byte: Option<u8>,
    cursor: usize,
    is_signed: bool,
    no_positive: bool,
    required: bool,
) -> (Result<bool, Error>, usize) {
    match byte {
        Some(b'+') if !no_positive => { (Ok(false), cursor + 1) },
        Some(b'+') if no_positive => (Err(Error::InvalidPositiveSign(cursor)), cursor),
        Some(b'-') if is_signed => { (Ok(true), cursor + 1) },
        Some(_) if required => (Err(Error::MissingSign(cursor)), cursor),
        _ if required => (Err(Error::MissingSign(cursor)), cursor),
        _ => (Ok(false), cursor),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_branches_and_cursor() {
        let at = 7;
        assert_eq!(parse_sign_state(Some(b'+'), at, false, false, true), (Ok(false), at + 1));
        assert_eq!(parse_sign_state(Some(b'+'), at, true, true, true), (Err(Error::InvalidPositiveSign(at)), at));
        assert_eq!(parse_sign_state(Some(b'-'), at, true, true, false), (Ok(true), at + 1));
        assert_eq!(parse_sign_state(Some(b'-'), at, false, false, true), (Err(Error::MissingSign(at)), at));
        assert_eq!(parse_sign_state(Some(b'2'), at, true, false, false), (Ok(false), at));
        assert_eq!(parse_sign_state(None, at, true, false, true), (Err(Error::MissingSign(at)), at));
    }
}
