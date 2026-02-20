"""
Crypto Detector Test File - Comprehensive Algorithm Coverage
This file contains examples of 80+ cryptographic algorithms across multiple languages.
Use this to verify the regex detector catches everything!
"""

# ============================================================================
# PYTHON EXAMPLES
# ============================================================================

# ------------------ HASH FUNCTIONS ------------------

# Broken/Deprecated Hashes (Should detect as HIGH RISK)
import hashlib
md5_hash = hashlib.md5(b"test")  # MD5 - BROKEN
md4_hash = hashlib.new('md4', b"test")  # MD4 - BROKEN
sha1_hash = hashlib.sha1(b"test")  # SHA-1 - DEPRECATED

# SHA-2 Family (Should detect as PARTIAL quantum-safe)
sha224_hash = hashlib.sha224(b"test")  # SHA-224
sha256_hash = hashlib.sha256(b"test")  # SHA-256
sha384_hash = hashlib.sha384(b"test")  # SHA-384
sha512_hash = hashlib.sha512(b"test")  # SHA-512

# SHA-3 Family (Should detect as PARTIAL quantum-safe)
sha3_224 = hashlib.sha3_224(b"test")  # SHA3-224
sha3_256 = hashlib.sha3_256(b"test")  # SHA3-256
sha3_384 = hashlib.sha3_384(b"test")  # SHA3-384
sha3_512 = hashlib.sha3_512(b"test")  # SHA3-512
shake_128 = hashlib.shake_128(b"test")  # SHAKE128
shake_256 = hashlib.shake_256(b"test")  # SHAKE256

# BLAKE Family
blake2b_hash = hashlib.blake2b(b"test")  # BLAKE2b
blake2s_hash = hashlib.blake2s(b"test")  # BLAKE2s

# ------------------ SYMMETRIC ENCRYPTION ------------------

from Crypto.Cipher import AES, DES, DES3, Blowfish, ChaCha20
from Crypto.Cipher import ARC4  # RC4

# Broken/Deprecated (Should detect as HIGH RISK)
des_cipher = DES.new(key, DES.MODE_ECB)  # DES - OBSOLETE
des3_cipher = DES3.new(key, DES3.MODE_CBC)  # 3DES/TripleDES - DEPRECATED
rc4_cipher = ARC4.new(key)  # RC4 - BROKEN
blowfish_cipher = Blowfish.new(key, Blowfish.MODE_CBC)  # Blowfish - OUTDATED

# Modern Symmetric (Should detect as PARTIAL quantum-safe)
aes_cipher = AES.new(key, AES.MODE_GCM)  # AES-GCM
aes_256 = AES.new(key256, AES.MODE_CBC)  # AES-256
aes_ccm = AES.new(key, AES.MODE_CCM)  # AES-CCM
chacha20 = ChaCha20.new(key=key)  # ChaCha20

# ------------------ ASYMMETRIC ENCRYPTION ------------------

from Crypto.PublicKey import RSA, DSA, ECC

# Quantum-Vulnerable (Should detect as HIGH RISK)
rsa_key = RSA.generate(2048)  # RSA
dsa_key = DSA.generate(2048)  # DSA
ecc_key = ECC.generate(curve='P-256')  # ECC/ECDSA

# ------------------ MESSAGE AUTHENTICATION ------------------

import hmac
hmac_obj = hmac.new(key, msg, hashlib.sha256)  # HMAC

# ------------------ KEY DERIVATION ------------------

from Crypto.Protocol.KDF import PBKDF2, scrypt
import bcrypt
import argon2

pbkdf2_key = PBKDF2(password, salt, dkLen=32)  # PBKDF2
scrypt_key = scrypt(password, salt, 32, N=2**14)  # scrypt
bcrypt_hash = bcrypt.hashpw(password, bcrypt.gensalt())  # bcrypt
argon2_hash = argon2.hash_password(password)  # Argon2

# ------------------ POST-QUANTUM CRYPTOGRAPHY ------------------

# These would be from specialized libraries
# kyber_kem = Kyber512.keygen()  # Kyber (ML-KEM)
# dilithium_sig = Dilithium2.sign(message)  # Dilithium (ML-DSA)
# falcon_sig = Falcon512.sign(message)  # Falcon
# sphincs_sig = SPHINCS.sign(message)  # SPHINCS+

# ============================================================================
# JAVA EXAMPLES
# ============================================================================

"""
import java.security.MessageDigest;
import javax.crypto.Cipher;
import javax.crypto.KeyGenerator;
import java.security.KeyPairGenerator;

// Hash Functions
MessageDigest md5 = MessageDigest.getInstance("MD5");  // MD5 - BROKEN
MessageDigest sha1 = MessageDigest.getInstance("SHA-1");  // SHA-1 - DEPRECATED
MessageDigest sha256 = MessageDigest.getInstance("SHA-256");  // SHA-256
MessageDigest sha512 = MessageDigest.getInstance("SHA-512");  // SHA-512

// Symmetric Encryption
Cipher des = Cipher.getInstance("DES/ECB/PKCS5Padding");  // DES - OBSOLETE
Cipher desede = Cipher.getInstance("DESede/CBC/PKCS5Padding");  // 3DES - DEPRECATED
Cipher aes = Cipher.getInstance("AES/GCM/NoPadding");  // AES-GCM

// Asymmetric Encryption
KeyPairGenerator rsaGen = KeyPairGenerator.getInstance("RSA");  // RSA
KeyPairGenerator dsaGen = KeyPairGenerator.getInstance("DSA");  // DSA
KeyPairGenerator ecGen = KeyPairGenerator.getInstance("EC");  // ECC/ECDSA

// MAC
import javax.crypto.Mac;
Mac hmacSha256 = Mac.getInstance("HmacSHA256");  // HMAC-SHA256
Mac hmacSha512 = Mac.getInstance("HmacSHA512");  // HMAC-SHA512
"""

# ============================================================================
# JAVASCRIPT / NODE.JS EXAMPLES
# ============================================================================

"""
const crypto = require('crypto');

// Hash Functions
const md5 = crypto.createHash('md5');  // MD5 - BROKEN
const sha1 = crypto.createHash('sha1');  // SHA-1 - DEPRECATED
const sha256 = crypto.createHash('sha256');  // SHA-256
const sha512 = crypto.createHash('sha512');  // SHA-512

// Symmetric Encryption
const aes_cipher = crypto.createCipheriv('aes-256-gcm', key, iv);  // AES-256-GCM
const aes_decipher = crypto.createDecipheriv('aes-256-cbc', key, iv);  // AES-256-CBC
const chacha = crypto.createCipheriv('chacha20-poly1305', key, iv);  // ChaCha20-Poly1305

// Asymmetric Encryption
crypto.generateKeyPair('rsa', { modulusLength: 2048 }, callback);  // RSA
crypto.generateKeyPair('ec', { namedCurve: 'secp256k1' }, callback);  // ECC/secp256k1
crypto.generateKeyPair('ed25519', {}, callback);  // Ed25519

// HMAC
const hmac = crypto.createHmac('sha256', key);  // HMAC-SHA256

// PBKDF2
crypto.pbkdf2(password, salt, 100000, 64, 'sha512', callback);  // PBKDF2

// Web Crypto API
const digest = await crypto.subtle.digest('SHA-256', data);  // SHA-256
const encrypted = await crypto.subtle.encrypt({ name: 'AES-GCM' }, key, data);  // AES-GCM
const signature = await crypto.subtle.sign({ name: 'ECDSA' }, privateKey, data);  // ECDSA
"""

# ============================================================================
# C/C++ EXAMPLES (OpenSSL)
# ============================================================================

"""
#include <openssl/evp.h>
#include <openssl/md5.h>
#include <openssl/sha.h>
#include <openssl/rsa.h>

// Hash Functions
EVP_MD_CTX *ctx_md5 = EVP_MD_CTX_new();
EVP_DigestInit_ex(ctx_md5, EVP_md5(), NULL);  // MD5 - BROKEN

EVP_MD_CTX *ctx_sha1 = EVP_MD_CTX_new();
EVP_DigestInit_ex(ctx_sha1, EVP_sha1(), NULL);  // SHA-1 - DEPRECATED

EVP_MD_CTX *ctx_sha256 = EVP_MD_CTX_new();
EVP_DigestInit_ex(ctx_sha256, EVP_sha256(), NULL);  // SHA-256

EVP_MD_CTX *ctx_sha512 = EVP_MD_CTX_new();
EVP_DigestInit_ex(ctx_sha512, EVP_sha512(), NULL);  // SHA-512

// Symmetric Encryption
EVP_CIPHER_CTX *aes_ctx = EVP_CIPHER_CTX_new();
EVP_EncryptInit_ex(aes_ctx, EVP_aes_256_gcm(), NULL, key, iv);  // AES-256-GCM

EVP_CIPHER_CTX *des_ctx = EVP_CIPHER_CTX_new();
EVP_EncryptInit_ex(des_ctx, EVP_des_ede3_cbc(), NULL, key, iv);  // 3DES

EVP_CIPHER_CTX *chacha_ctx = EVP_CIPHER_CTX_new();
EVP_EncryptInit_ex(chacha_ctx, EVP_chacha20_poly1305(), NULL, key, iv);  // ChaCha20

// Asymmetric Encryption
RSA *rsa = RSA_generate_key(2048, RSA_F4, NULL, NULL);  // RSA
EVP_PKEY *pkey = EVP_PKEY_new();
EVP_PKEY_assign_RSA(pkey, rsa);

// Legacy Direct APIs
MD5_CTX md5_ctx;
MD5_Init(&md5_ctx);  // MD5 - BROKEN

SHA_CTX sha1_ctx;
SHA1_Init(&sha1_ctx);  // SHA-1 - DEPRECATED

SHA256_CTX sha256_ctx;
SHA256_Init(&sha256_ctx);  // SHA-256

SHA512_CTX sha512_ctx;
SHA512_Init(&sha512_ctx);  // SHA-512

AES_KEY aes_key;
AES_set_encrypt_key(key, 256, &aes_key);  // AES

DES_key_schedule des_schedule;
DES_set_key(&des_key, &des_schedule);  // DES
"""

# ============================================================================
# GO EXAMPLES
# ============================================================================

"""
package main

import (
    "crypto/md5"      // MD5
    "crypto/sha1"     // SHA-1
    "crypto/sha256"   // SHA-256
    "crypto/sha512"   // SHA-512
    "crypto/aes"      // AES
    "crypto/des"      // DES
    "crypto/rsa"      // RSA
    "crypto/ecdsa"    // ECDSA
    "crypto/hmac"     // HMAC
    "golang.org/x/crypto/chacha20poly1305"  // ChaCha20-Poly1305
    "golang.org/x/crypto/blake2b"           // BLAKE2b
    "golang.org/x/crypto/pbkdf2"            // PBKDF2
    "golang.org/x/crypto/bcrypt"            // bcrypt
    "golang.org/x/crypto/argon2"            // Argon2
)

func main() {
    // Hash Functions
    md5Hash := md5.New()           // MD5 - BROKEN
    sha1Hash := sha1.New()         // SHA-1 - DEPRECATED
    sha256Hash := sha256.New()     // SHA-256
    sha512Hash := sha512.New()     // SHA-512
    
    // Symmetric
    block, _ := aes.NewCipher(key)     // AES
    desBlock, _ := des.NewCipher(key)  // DES
    
    // Asymmetric
    privateKey, _ := rsa.GenerateKey(rand.Reader, 2048)  // RSA
    ecdsaKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)  // ECDSA
}
"""

# ============================================================================
# RUST EXAMPLES
# ============================================================================

"""
use md5;           // MD5
use sha1;          // SHA-1
use sha2::{Sha256, Sha512};  // SHA-256, SHA-512
use sha3::{Sha3_256, Sha3_512};  // SHA3-256, SHA3-512
use blake2::{Blake2b, Blake2s};  // BLAKE2b, BLAKE2s
use aes::Aes256;   // AES-256
use chacha20poly1305::ChaCha20Poly1305;  // ChaCha20-Poly1305
use rsa::RsaPrivateKey;  // RSA
use hmac::Hmac;    // HMAC
use pbkdf2;        // PBKDF2
use bcrypt;        // bcrypt
use argon2;        // Argon2

fn main() {
    // Hash
    let md5_hash = md5::compute(b"test");        // MD5
    let sha1_hash = sha1::Sha1::digest(b"test"); // SHA-1
    let sha256 = Sha256::digest(b"test");         // SHA-256
    let sha512 = Sha512::digest(b"test");         // SHA-512
    
    // Symmetric
    let cipher = Aes256::new(&key);  // AES-256
    let chacha = ChaCha20Poly1305::new(&key);  // ChaCha20
    
    // Asymmetric
    let rsa_key = RsaPrivateKey::new(&mut rng, 2048);  // RSA
}
"""

# ============================================================================
# PHP EXAMPLES
# ============================================================================

"""
<?php

// Hash Functions
$md5 = md5($data);                    // MD5 - BROKEN
$sha1 = sha1($data);                  // SHA-1 - DEPRECATED
$sha256 = hash('sha256', $data);      // SHA-256
$sha512 = hash('sha512', $data);      // SHA-512
$sha3_256 = hash('sha3-256', $data);  // SHA3-256
$blake2b = hash('blake2b', $data);    // BLAKE2b

// Symmetric Encryption
$aes_encrypted = openssl_encrypt($data, 'aes-256-gcm', $key, 0, $iv);  // AES-256-GCM
$des_encrypted = openssl_encrypt($data, 'des-ede3-cbc', $key, 0, $iv); // 3DES
$chacha = openssl_encrypt($data, 'chacha20-poly1305', $key, 0, $iv);   // ChaCha20

// Asymmetric
$rsa_key = openssl_pkey_new(['private_key_type' => OPENSSL_KEYTYPE_RSA]);  // RSA
$ecdsa_key = openssl_pkey_new(['private_key_type' => OPENSSL_KEYTYPE_EC]); // ECDSA

// HMAC
$hmac = hash_hmac('sha256', $data, $key);  // HMAC-SHA256

// Password Hashing
$bcrypt = password_hash($password, PASSWORD_BCRYPT);   // bcrypt
$argon2 = password_hash($password, PASSWORD_ARGON2I);  // Argon2

// PBKDF2
$pbkdf2 = hash_pbkdf2('sha256', $password, $salt, 100000);  // PBKDF2

?>
"""

# ============================================================================
# ELLIPTIC CURVE VARIATIONS
# ============================================================================

"""
// Various ECC curves (all quantum-vulnerable)

// NIST Curves
const p256 = crypto.generateKeyPair('ec', { namedCurve: 'P-256' });    // P-256 / prime256v1
const p384 = crypto.generateKeyPair('ec', { namedCurve: 'P-384' });    // P-384
const p521 = crypto.generateKeyPair('ec', { namedCurve: 'P-521' });    // P-521

// secp Curves
const secp256k1 = ECC.generate(curve='secp256k1');  // secp256k1 (Bitcoin)
const secp256r1 = ECC.generate(curve='secp256r1');  // secp256r1 (same as P-256)
const secp384r1 = ECC.generate(curve='secp384r1');  // secp384r1

// Edwards Curves
const ed25519_key = crypto.generateKeyPair('ed25519');  // Ed25519
const ed448_key = crypto.generateKeyPair('ed448');      // Ed448

// Curve25519 variants
const x25519_key = crypto.generateKeyPair('x25519');    // X25519 (ECDH)
const x448_key = crypto.generateKeyPair('x448');        // X448 (ECDH)
"""

# ============================================================================
# POST-QUANTUM ALGORITHMS (Hypothetical library calls)
# ============================================================================

"""
// NIST Post-Quantum Standards

// ML-KEM (Kyber)
from pqcrypto.kem import kyber512, kyber768, kyber1024
pk, sk = kyber512.keypair()        // Kyber-512
pk, sk = kyber768.keypair()        // Kyber-768
pk, sk = kyber1024.keypair()       // Kyber-1024

// ML-DSA (Dilithium)
from pqcrypto.sign import dilithium2, dilithium3, dilithium5
pk, sk = dilithium2.keypair()      // Dilithium2
pk, sk = dilithium3.keypair()      // Dilithium3
pk, sk = dilithium5.keypair()      // Dilithium5

// Falcon
from pqcrypto.sign import falcon512, falcon1024
pk, sk = falcon512.keypair()       // Falcon-512
pk, sk = falcon1024.keypair()      // Falcon-1024

// SPHINCS+
from pqcrypto.sign import sphincs
pk, sk = sphincs.keypair()         // SPHINCS+

// Other PQC
from pqcrypto import ntru, frodokem
ntru_key = ntru.keypair()          // NTRU
frodo_key = frodokem.keypair()     // FrodoKEM

// Broken PQC (for testing)
sike_key = sike.keypair()          // SIKE (BROKEN - should flag as high risk)
"""

# ============================================================================
# ADDITIONAL MAC ALGORITHMS
# ============================================================================

"""
// Message Authentication Codes

// HMAC variants
const hmacSha1 = crypto.createHmac('sha1', key);      // HMAC-SHA1
const hmacSha256 = crypto.createHmac('sha256', key);  // HMAC-SHA256
const hmacSha384 = crypto.createHmac('sha384', key);  // HMAC-SHA384
const hmacSha512 = crypto.createHmac('sha512', key);  // HMAC-SHA512
const hmacMd5 = crypto.createHmac('md5', key);        // HMAC-MD5 (weak)

// Other MACs
import Poly1305
poly1305_mac = Poly1305.new(key, cipher=AES)  // Poly1305

import CMAC
cmac = CMAC.new(key, ciphermod=AES)           // CMAC

import GMAC
gmac = GMAC.new(key)                          // GMAC
"""

# ============================================================================
# KEY DERIVATION FUNCTIONS
# ============================================================================

"""
// PBKDF2 variants
pbkdf2_sha1 = PBKDF2(password, salt, dkLen=32, hmac_hash_module=SHA1)    // PBKDF2-SHA1
pbkdf2_sha256 = PBKDF2(password, salt, dkLen=32, hmac_hash_module=SHA256) // PBKDF2-SHA256
pbkdf2_sha512 = PBKDF2(password, salt, dkLen=64, hmac_hash_module=SHA512) // PBKDF2-SHA512

// scrypt
scrypt_key = scrypt(password, salt, N=16384, r=8, p=1, dkLen=32)  // scrypt

// bcrypt (various costs)
bcrypt_10 = bcrypt.hashpw(password, bcrypt.gensalt(10))  // bcrypt cost=10
bcrypt_12 = bcrypt.hashpw(password, bcrypt.gensalt(12))  // bcrypt cost=12

// Argon2 variants
argon2i = argon2.argon2_hash(password, salt, type=argon2.Argon2Type.Argon2_i)   // Argon2i
argon2d = argon2.argon2_hash(password, salt, type=argon2.Argon2Type.Argon2_d)   // Argon2d
argon2id = argon2.argon2_hash(password, salt, type=argon2.Argon2Type.Argon2_id) // Argon2id

// HKDF
from Crypto.Protocol.KDF import HKDF
hkdf_key = HKDF(master, key_len=32, salt=salt, hashmod=SHA256)  // HKDF-SHA256
"""

# ============================================================================
# EDGE CASES AND TRICKY PATTERNS
# ============================================================================

# String literals in crypto context
cipher_name = "AES-256-GCM"  # Should detect AES
hash_algo = "SHA-256"        # Should detect SHA-256
signature_algo = "RSA-SHA256"  # Should detect RSA

# Method chaining
crypto.createHash('sha512').update(data).digest()  # Should detect SHA-512

# Nested function calls
encrypted = encrypt(AES.new(key, AES.MODE_GCM), plaintext)  # Should detect AES

# Class instantiation
cipher = new AES.Cipher(key, mode=AES.MODE_CBC)  # Should detect AES

# ============================================================================
# FALSE POSITIVE TESTS (Should NOT detect these)
# ============================================================================

# These should be IGNORED (comments, docs, URLs, non-crypto contexts)

# This is a comment about MD5 checksums - should be ignored
"""
This is documentation about SHA-256 hashing.
It should not be detected as actual crypto usage.
"""

# URL containing crypto terms
url = "https://example.com/api/sha256/verify"  # Should be ignored

# File path
config_file = "/etc/ssl/aes-config.json"  # Should be ignored

# Import without usage
import hashlib  # Should be ignored (just import, no actual usage)

# Non-crypto variable names
user_id = "md5_checksum_user"  # Should be ignored
file_name = "sha256.txt"        # Should be ignored

print("""
=============================================================================
TEST FILE COMPLETE
=============================================================================

This file contains:
- 80+ unique cryptographic algorithms
- Examples across 8+ programming languages
- All major categories (hash, symmetric, asymmetric, PQC, MAC, KDF)
- Edge cases and tricky patterns
- False positive test cases

Expected Detections:
- HIGH RISK: MD2, MD4, MD5, SHA-1, DES, 3DES, RC4, RC2, Blowfish, RSA, DSA, 
             ECC, ECDSA, secp256k1, ElGamal, SIKE
- MEDIUM RISK: Ed25519, Ed448, X25519, X448, SHA-224, PBKDF2, RIPEMD-160
- LOW RISK: SHA-256, SHA-512, SHA-3 family, BLAKE2/3, AES, ChaCha20, 
            HMAC, bcrypt, scrypt, Argon2, Twofish, Serpent, Camellia
- NONE (PQC): Kyber, Dilithium, Falcon, SPHINCS+, NTRU, FrodoKEM

Total Expected Detections: 150+ individual occurrences

Run this test with: Crypto Detector: Scan Current File
=============================================================================
""")
