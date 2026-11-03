use sha2::{Digest, Sha256};

fn main() {
    for cb58 in [false, true] {
        let label = if cb58 { "CB58" } else { "Base58Check" };
        let encoded = if cb58 {
            bs58::encode([]).as_cb58(None).into_string()
        } else {
            bs58::encode([]).with_check().into_string()
        };
        let raw = bs58::decode(&encoded).into_vec().unwrap();
        assert_eq!(raw.len(), 4);
        let result = if cb58 {
            bs58::decode(&encoded).as_cb58(Some(raw[0])).into_vec()
        } else {
            bs58::decode(&encoded).with_check(Some(raw[0])).into_vec()
        };
        assert_eq!(result, Ok(vec![]));
        println!("{label}: checksum-only {encoded:?} accepted expected version {}: {result:?}", raw[0]);

        let encoded = if cb58 {
            bs58::encode([42]).as_cb58(None).into_string()
        } else {
            bs58::encode([42]).with_check().into_string()
        };
        let mut output = [0xa5; 16];
        let len = if cb58 {
            bs58::decode(&encoded).as_cb58(None).onto(&mut output)
        } else {
            bs58::decode(&encoded).with_check(None).onto(&mut output)
        }.unwrap();
        assert_eq!(len, 1);
        assert_ne!(&output[len..len + 4], &[0xa5; 4]);
        assert_eq!(&output[len + 4..], &[0xa5; 11]);
        println!("{label}: onto returns {len}, but overwrites next 4 bytes: {:?}", &output[..len + 4]);
        let mut exact_output = [0xa5; 1];
        let exact_result = if cb58 {
            bs58::decode(&encoded).as_cb58(None).onto(&mut exact_output)
        } else {
            bs58::decode(&encoded).with_check(None).onto(&mut exact_output)
        };
        assert_eq!(exact_result, Err(bs58::decode::Error::BufferTooSmall));

        let first = Sha256::digest([42]);
        let computed: [u8; 4] = if cb58 {
            first[28..].try_into().unwrap()
        } else {
            Sha256::digest(first)[..4].try_into().unwrap()
        };
        let given = [0u8; 4];
        assert_ne!(computed, given);
        let malformed = bs58::encode([42, 0, 0, 0, 0]).into_string();
        let result = if cb58 {
            bs58::decode(malformed).as_cb58(None).into_vec()
        } else {
            bs58::decode(malformed).with_check(None).into_vec()
        };
        assert_eq!(result, Err(bs58::decode::Error::InvalidChecksum {
            checksum: computed,
            expected_checksum: given,
        }));
        println!("{label}: InvalidChecksum has checksum={computed:?} (computed), expected_checksum={given:?} (given)");
    }
}
