#include <libff/common/default_types/ec_pp.hpp>
#include <libsnark/common/default_types/r1cs_gg_ppzksnark_pp.hpp>
#include <libsnark/relations/constraint_satisfaction_problems/r1cs/examples/r1cs_examples.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_gg_ppzksnark/r1cs_gg_ppzksnark.hpp>
#include "libsnark/common/default_types/r1cs_ppzksnark_pp.hpp"
#include "libsnark/gadgetlib1/gadgets/basic_gadgets.hpp"
#include "libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"

#include <string.h>
#include <iostream>
#include <stdlib.h>
#include <stdio.h>
#include <vector>
#include <cmath>
#include <ctime>
#include <openssl/aes.h>
#include <openssl/sha.h>


#include <unistd.h>

using namespace libsnark;
using namespace std;
const size_t KEYSIZE = 16;
const int PLAIN_LENGTH = 140;  
const int TABLE_WIDTH = 1 << 5;
const int TABLE_HEIGHT = 1 << 10;
const int BOX_OVERHEAD = 16;
const int WALLET_LENGTH = 128;
//plaintext length plus 2 public keys and 2 message digests
const int SLOT_LENGTH = PLAIN_LENGTH + 2*(KEYSIZE + BOX_OVERHEAD);


typedef unsigned char byte;
typedef byte BitMatrixRow[TABLE_WIDTH*SLOT_LENGTH];


struct serverInfo{
    int serverCount = 1;
};

template<size_t N>
class ByteArray{
    private:
        byte data[N];

    public:
        //constructor
        ByteArray(){
            memset(data,0,sizeof(data));
        }
        ByteArray(const ByteArray<N> & other){
            memmove(data,other.data,sizeof(data));
        }
        ByteArray(bool rand){
            if(rand){
                memset(data,0,sizeof(data));
                random();
            }
        }

        byte & operator[](size_t i){
            if(i>=N)
                throw out_of_range("ByteArray::[] out of range");
            return data[i];
        }

        static const size_t size = N;

        //initialize random ByteArray
        void random(){
            int r = rand()%10;
            memset(data, 0, sizeof(data));
            memcpy(data, (char*)&r, sizeof(short));
        }

        void printArray(){
            cout << "printArray:" << endl;
            for(int i=0; i<N; i++){
                cout << data[i];
            }
            cout << "\n";
        }

        byte* getData(){
            return data;
        }

        size_t getSize(){
            return N;
        }

        long toLong(){
            return (long)(*(short*)data);
        }

        void setWithLong(long i){
            memset(data, 0, sizeof(data));
            memcpy(data, (char*)&i, sizeof(short));
        }
};

byte* newKey(){
    ByteArray<KEYSIZE> k;
    k.random();
    return k.getData();
}

class Prf{
    private:
        AES_KEY enc_key;
        AES_KEY dec_key;
    public:
        Prf(){
            //byte randkey[KEYSIZE] = newKey();
            byte* k = newKey();
            AES_set_encrypt_key(k,128, &enc_key);
            AES_set_decrypt_key(k,128, &dec_key);
        }

        Prf( byte k[KEYSIZE]){
            AES_set_encrypt_key(k,128, &enc_key);
            AES_set_decrypt_key(k,128, &dec_key);
        }

        void encrypt(byte * msg, byte* enc_out){
            //byte enc_out[80];
            AES_encrypt(msg, enc_out, &enc_key);
            //return 
        }

        void decrypt(byte * enc_out, byte* dec_out){
            AES_decrypt(enc_out, dec_out, &dec_key);
        }
};
// ByteArray<KEYSIZE> * randomVectorKeys(){
//     ByteArray<KEYSIZE> s[TABLE_HEIGHT];
    
// }

struct plainQuery{
    BitMatrixRow v;

    //Array of booleans
    //bool b[TABLE_HEIGHT];
    int b[TABLE_HEIGHT];

    //Array of random keys
    ByteArray<KEYSIZE> s[TABLE_HEIGHT];
};

struct location{
    int x =0;
    int y =0;
};

location calculateLocation(ByteArray<KEYSIZE> Kab, int Nab){
    location l;
    //p1 = PRF_Kab
    byte* chars;
    byte enc_out[256];

    int nab = Nab;
    chars = (byte*) &nab;
    //memcpy(chars,(char*)&Nab,sizeof(int));
    Prf p1(Kab.getData());

    p1.encrypt(chars,enc_out);
    //cout<<"encout: \n"<<enc_out<<endl;
    uint n = *(uint*)enc_out %(TABLE_HEIGHT*TABLE_WIDTH);//atoi((char*)enc_out);

    l.y = n/TABLE_WIDTH;
    l.x = n %TABLE_WIDTH;
    cout<<"LOCATION:"<<l.x<<" , "<<l.y<<endl;

    return l;
}


vector<plainQuery> genShare( location l, string msg, serverInfo si){
    cout<<"in genShare"<<endl;
    //TODO: 1. encrypt slot === encrypt msg
    //initialize 2 server
    plainQuery q1;

    //initialize v and s to random values
    for(int i =0; i<TABLE_HEIGHT;i++){
        q1.s[i] = ByteArray<KEYSIZE>();
        q1.s[i].random();
        q1.b[i] = (rand()%2 == 0);
    }

    ByteArray<KEYSIZE> s_star[TABLE_HEIGHT] = ByteArray<KEYSIZE>(true);
    //s_star.random();

    plainQuery q2 = q1;
    //2 server method
    //reset q2's v and s to only differ at row Index , y
    //q2.b[l.y] =  !q1.b[l.y];
    //q2.s[l.y] = ByteArray<KEYSIZE>(true);

    //N-server method:
    //sum of bi = elx
    //sum of si = s* * elx
    for(int i=0;i<TABLE_HEIGHT;i++){
        if(i==l.y){
            q2.b[i] = 1-q1.b[l.y];
            q2.s[i].setWithLong(s_star[i].toLong() - q1.s[l.y].toLong());
        }else{
            q2.b[i] = 0-q1.b[i];
            q2.s[i].setWithLong(0 - q1.s[i].toLong());
            // if(q1.b[i]+q2.b[i]!=0){
            //     cout<<"something wrong at index "<<i<<endl;
            //     cout<<"q1.b[i] "<<q1.b[i]<<endl;
            // }
            // if(q1.s[i].toLong()+q2.s[i].toLong()!=0){
            //     cout<<"something wrong at index "<<i<<endl;
            //     cout<<"q1.s[i] "<<q1.s[i].toLong()<<endl;
            // }
            //cout<<"should be 0:"<<(q1.b[i]+q2.b[i]);
        }
    }

    cout<<"l.y: "<<l.y<<endl;
    cout<<"==========================="<<endl;
    vector<plainQuery> queries;
    queries.push_back(q1);
    queries.push_back(q2);
    return queries;
}

/**
 * The code below provides an example of all stages of running a R1CS GG-ppzkSNARK.
 *
 * Of course, in a real-life scenario, we would have three distinct entities,
 * mangled into one in the demonstration below. The three entities are as follows.
 * (1) The "generator", which runs the ppzkSNARK generator on input a given
 *     constraint system CS to create a proving and a verification key for CS.
 * (2) The "prover", which runs the ppzkSNARK prover on input the proving key,
 *     a primary input for CS, and an auxiliary input for CS.
 * (3) The "verifier", which runs the ppzkSNARK verifier on input the verification key,
 *     a primary input for CS, and a proof.
 */
template<typename ppT>
bool run_r1cs_gg_ppzksnark(const r1cs_example<libff::Fr<ppT> > &example) {
    libff::print_header("R1CS GG-ppzkSNARK Generator");
    r1cs_gg_ppzksnark_keypair<ppT> keypair = r1cs_gg_ppzksnark_generator<ppT>(example.constraint_system);
    printf("\n"); libff::print_indent(); libff::print_mem("after generator");

    libff::print_header("Preprocess verification key");
    r1cs_gg_ppzksnark_processed_verification_key<ppT> pvk = r1cs_gg_ppzksnark_verifier_process_vk<ppT>(keypair.vk);

    libff::print_header("R1CS GG-ppzkSNARK Prover");
    r1cs_gg_ppzksnark_proof<ppT> proof = r1cs_gg_ppzksnark_prover<ppT>(keypair.pk, example.primary_input, example.auxiliary_input);
    printf("\n"); libff::print_indent(); libff::print_mem("after prover");

    libff::print_header("R1CS GG-ppzkSNARK Verifier");
    const bool ans = r1cs_gg_ppzksnark_verifier_strong_IC<ppT>(keypair.vk, example.primary_input, proof);
    printf("\n"); libff::print_indent(); libff::print_mem("after verifier");
    printf("* The verification result is: %s\n", (ans ? "PASS" : "FAIL"));

    libff::print_header("R1CS GG-ppzkSNARK Online Verifier");
    const bool ans2 = r1cs_gg_ppzksnark_online_verifier_strong_IC<ppT>(pvk, example.primary_input, proof);
    assert(ans == ans2);

    return ans;
}

template<typename ppT>
void test_r1cs_gg_ppzksnark(size_t num_constraints, size_t input_size) {
    r1cs_example<libff::Fr<ppT> > example = generate_r1cs_example_with_binary_input<libff::Fr<ppT> >(num_constraints, input_size);
    const bool bit = run_r1cs_gg_ppzksnark<ppT>(example);
    assert(bit);
}


struct wallet {
    char* id = new char[65];
    int balance;    
};
const int CLIENT_ID_LENGTH = WALLET_LENGTH/2;
//typedef ByteArray<CLIENT_ID_LENGTH> clientId;


void sha256(char *string, char outputBuffer[65]) {
    unsigned char hash[SHA256_DIGEST_LENGTH];
    SHA256_CTX sha256;
    SHA256_Init(&sha256);
    SHA256_Update(&sha256, string, strlen(string));
    SHA256_Final(hash, &sha256);
    int i = 0;
    for(i = 0; i < SHA256_DIGEST_LENGTH; i++)
    {
        sprintf(outputBuffer + (i * 2), "%02x", hash[i]);
    }
    outputBuffer[64] = 0;
}

//This should use a trusted 3rd party to issue credential
wallet regWallet(char* id) {
    wallet w;
    sha256(id,w.id);
    w.balance=1;
    return w;
}

bool verifyWallet(char* hash1, char* hash2) {
    return strcmp(hash1, hash2) == 0;
}
//This signing process should be implemented with zk
//Here is just a simple demo without zk
bool signWallet(wallet w) {
    char* client_ip = "127.0.0.1";
    char* hash = new char[65];
    sha256(client_ip,hash);

    bool result = verifyWallet(w.id, hash);

    delete[] hash;
    //reject or process
    return result;

}

struct commitments {
    vector<vector<long long>> ss;
    //vector<long> c2;
    vector<vector<long long>> bs;

    //vector<long> c3,c4;
};

long long computeCommitment(long g, long x, long h, long r, long p){
	if(x<0)
	    return fmod((double)pow(g,x)*(double)pow(h,r),(double)p)*100000;
    	return (long long)((long long)pow(g,x) * (long long)pow(h,r))%p * 100000;
}



//Generate Pedersen Commitment
commitments Pedersen(vector<plainQuery> & query, vector<long>&Bsum, vector<long>&Ssum){
    ByteArray<KEYSIZE> s1[TABLE_HEIGHT] = query[0].s;
    ByteArray<KEYSIZE> s2[TABLE_HEIGHT] = query[1].s;

    auto b1 = query[0].b;
    auto b2 = query[1].b;

    //primes
    // long p  = 1301081;
    // long g,h = 1300051, 1299743;
    // long r = 1299721;

    long p  = 3547;
    long q = 197;

    int g = 3;
    int h = 7;
    int r = 2;
   

    //TODO: x should loop through s and b
    //long x = 30;
    commitments c;
    vector<long long> c1,c2,c3,c4;
    c.ss.push_back(c1);
    c.ss.push_back(c2);
    c.bs.push_back(c3);
    c.bs.push_back(c4);
    for(int i=0; i<TABLE_HEIGHT; i++){
        long x = s1[i].toLong();
        long x2 = s2[i].toLong();
	
        long long cc1=computeCommitment(g, x, h, r, p);
        long long cc2 = computeCommitment(g, x2, h, r, p);

        c.ss[0].push_back(cc1); 
        c.ss[1].push_back(cc2);

        /*if(x+x2 == 0){
	    cout << "s1:" << x << ", s2:" << x2 << endl;
            cout << "at i=" << i << ": s1+s2=" << x+x2 << endl;
            cout << "sumB: cc1*cc2 = "<<((long)(ceil(cc1/100000.0*cc2/100000.0)))%p << endl;
            cout << "commitment of 0: " << computeCommitment(g,0,h,r+r,p)/100000 << endl;
        }
        else{
	    cout << "s1:" << x << ", s2:" << x2 << endl;
            cout << "at i=" << i << ": s1+s2=" << x+x2 << endl;
            cout << "sumB: cc1*cc2 = " << ((long)(ceil(cc1/100000.0*cc2/100000.0)))%p << endl;
            cout << "commitment of not 0: " << computeCommitment(g,0,h,r+r,p)/100000 << endl;
        }*/

        long x3 = (long) b1[i];
        long x4 = (long) b2[i];

        
        long long cc3 = computeCommitment(g, x3, h, r, p);
        long long cc4 = computeCommitment(g, x4, h, r, p);
        /*if(x3+x4 == 1){
            cout << "b1:" << x3 << ", b2:" << x4 << endl;
            cout << "at i=" << i << ": b1+b2=" << x3+x4 << endl;
            cout << "sumB: cc3*cc4 = " << ((long)(ceil(cc3/100000.0*cc4/100000.0)))%p << endl;
            cout << "commitment of 1: " << computeCommitment(g,1,h,r+r,p)/100000 << endl;
        }
        else{
            cout << "b1:" << x3 << ", b2:" << x4 << endl;
            cout << "at " << i << " : b1+b2=" << x3+x4 << endl;
            cout << "sumB: cc3*cc4 = " << ((long)(ceil(cc3/100000.0*cc4/100000.0)))%p << endl;
            cout << "commitment of 0: " << computeCommitment(g,0,h,r+r,p)/100000 << endl;
        }*/
        c.bs[0].push_back(cc3); 
        c.bs[1].push_back(cc4);

        if(Bsum.size()==i){
          // cout << "Bsum pushed: " << ((long)(ceil(cc3/100000.0*cc4/100000.0)))%p << endl;
          Bsum.push_back(((long)(ceil(cc3/100000.0*cc4/100000.0)))%p);
          Ssum.push_back(((long)(ceil(cc1/100000.0*cc2/100000.0)))%p);
        }

    }

    //long c = ((long)pow(g,x) * (long)pow(h,r)) % p;
    //commitment m = g^r * h^m
    //vector<long>
    return c;
}

bool verifyPederson(commitments & cc, plainQuery & query, int server_idx){
    long p  = 3547;
    long q = 197;

    long g = 3;
    long h = 7;
    long r = 2;

    //vector<long> Bsum, Ssum;
    ByteArray<KEYSIZE> s[TABLE_HEIGHT] = query.s;
    auto b = query.b;
    //verify it's correct commitment to server_idx
    for(size_t i=0;i<TABLE_HEIGHT;i++){
        long x = s[i].toLong();
        long x3 = (long) b[i];

        if(cc.ss[server_idx][i]!=computeCommitment(g,x,h,r,p)){
            //cout<<"inputs: "<<g<<" "<<x<<" "<<h<<" "<<r<<" "<<p<<" "<<s[i]<<endl;
            cout<<"commitment not equal!!!!!\n"<<"i:"<<i<<";\n values:\n ss[idx][i]:"<<cc.ss[server_idx][i]<<"\ncomputed:"<<computeCommitment(g,x,h,r,p)<<endl;
            //cout<<"inputs: "<<g<<" "<<x<<" "<<h<<" "<<r<<" "<<p<<" "<<s[i]<<endl;
            return false;
        }
        if(cc.bs[server_idx][i]!=computeCommitment(g,x3,h,r,p)){
            cout<<"commitment not equal!!!!!\n"<<"i:"<<i<<";\n values:\nbs[idx][i]:"<<cc.bs[server_idx][i]<<"\ncomputed:"<<computeCommitment(g,x,h,r,p)<<endl;
            return false;
        }
    }

    return true;
}


int main() {
    ByteArray<KEYSIZE> a;// = new ByteArray<KEYSIZE>();
    a.random();
    a.printArray();
    cout<<"main"<<endl;
    serverInfo s;


    location l = calculateLocation(a,1);
    vector<plainQuery> queries = genShare(l,"msg",s);


    //AES encrypt/decrypt
    unsigned char text[] = "hello world";
    byte enc_out[80];
    byte dec_out[80];

    //test prf encode decode
    Prf f;
    Prf f2(a.getData());

    f2.encrypt(text, enc_out);
    f2.decrypt(enc_out, dec_out);
    cout << dec_out << endl;

    f.encrypt(text, enc_out);
    f.decrypt(enc_out, dec_out);
    cout << dec_out << endl;



    char* id = "127.0.0.1";
    wallet w = regWallet(id);

    cout << w.balance << ", " << w.id << endl;
    bool r = signWallet(w);
    cout << "signwallet: " << r << endl;

    //long commitment = Pedersen(queries);
    vector<long> Bsum, Ssum;
    commitments c = Pedersen(queries, Bsum, Ssum);
    bool r2 = verifyPederson(c, queries[0],0);
    cout << r2 << endl;

    bool r3 = verifyPederson(c, queries[1],1);
    cout << r3 << endl;

   //commitment to 0:2401, 1: 109

    
  constexpr size_t dimension = TABLE_HEIGHT; // Dimension of the vector
    // using ppT = default_r1cs_ppzksnark_pp; // Use the default public parameters
  // using FieldT = ppT::Fp_type; // ppT is a specification for a collection of types, among which Fp_type is the base field
  typedef libff::default_ec_pp ppT;
  typedef libff::Fr<libff::default_ec_pp> FieldT;
  ppT::init_public_params(); // Initialize the libsnark

  const auto one = FieldT::one();//*109; // constant
  const auto zero = FieldT::zero();//*2401; // constant
//std::vector<FieldT> public_input{one,one,one,one,one,one,one,one,one,one}; // x = (1,1,1,1,1,1,1,1,1,1)
//  std::vector<FieldT> secret_input{one,-one,one,-one,one,-one,two,-one,one,-one}; // our secret a such that <x,a> = 0
  std::vector< std::vector<FieldT> > public_input;
  std::vector<FieldT> secret_input; // our secret a such that <x,a> = 0
  vector<FieldT> helper{one,one};//(TABLE_HEIGHT,FieldT::one());

  for(int i=0; i<TABLE_HEIGHT; i++){
    if(Bsum[i] == 2401){
	    secret_input.push_back(FieldT::zero());
    }
    else{ 
      secret_input.push_back(FieldT::one());
    }
    vector<FieldT> pcur(TABLE_HEIGHT,FieldT::one());
    pcur[i] = FieldT::zero();
    public_input.push_back(pcur);
    helper.push_back(FieldT::one());
  }
  

  /*********************************/
  /* Everybody: Design the circuit */
  /*********************************/
  protoboard<FieldT> pb; // The board to allocate gadgets
  pb_variable_array<FieldT> B; // The input wires (anchor) for x
  vector<pb_variable_array<FieldT>> A; // The input wires (anchor) for a
  pb_variable<FieldT> res; // The output wire (anchor)
  pb_variable_array<FieldT >temp;
  
  pb_variable_array<FieldT> H;
  /* Allocate the anchors on the protoboard.
   * Note: all the public input anchors must be allocated first before
   * any other anchors. The reason is that libsnark simply treats the first
   * num_inputs() number of anchors as primary_input for the r1cs, and the
   * rest as auxiliary_input. */
  B.allocate(pb, dimension, "B");
  H.allocate(pb, dimension, "H");
  temp.allocate(pb, dimension, "temp");
  for(int i=0; i<TABLE_HEIGHT; i++){
    pb_variable_array<FieldT>aaa;
    aaa.allocate(pb,dimension, "A" + to_string(i));
    A.push_back(aaa);
    //pb_variable<FieldT> ttt;
    //ttt.allocate(pb, "temp"+to_string(i));
    //temp.push_back(ttt);
  }
  //B.allocate(pb, dimension, "B");
  res.allocate(pb, "res");
  
  /* Connect the anchors by a inner_product computing gadget, specifying the
   * relationship for the anchors (A,B and res) to satisfy.
   * Note that this gadget introduces a lot more (to be accurate, 9) anchors
   * on the protoboard. Now there are 30 anchors in total. */
  vector<inner_product_gadget<FieldT>> gadgets;
  for(int i=0;i<TABLE_HEIGHT;i++){

    inner_product_gadget<FieldT> compute_inner_product(pb, B, A[i], temp[i], "compute_inner_product"+to_string(i));
    gadgets.push_back(compute_inner_product);
  }
  inner_product_gadget<FieldT> compute_inner_product2(pb, temp, H, res, "compute_inner_product_last");
  gadgets.push_back(compute_inner_product2);

  /* Set the first **dimension** number of anchors as public inputs. */
  pb.set_input_sizes(dimension);
  /* Compute R1CS constraints resulted from the inner product gadget. */
  for(int i=0;i<gadgets.size();i++){
    gadgets[i].generate_r1cs_constraints();
    //sleep(1);
  }
  //compute_inner_product.generate_r1cs_constraints();
  /* Don't forget another constraint that the output must be zero */

  generate_r1cs_equals_const_constraint(pb,pb_linear_combination<FieldT>(res),FieldT::zero());
  /* Finally, extract the resulting R1CS constraint system */
  auto cs = pb.get_constraint_system();

// The start of Zero Knowledge Proof
  std::clock_t c_start = std::clock();
  cout << "*************** Start Time: " << c_start << " ***************" << endl;
  /***************************************/
  /* Trusted Third Party: Key generation */
  /***************************************/
  auto keypair = r1cs_ppzksnark_generator<ppT>(cs);

  /**************************************************/
  /* Prover: Fill in both inputs and generate proof */
  /**************************************************/
  for (size_t i = 0; i < dimension; i++)
  {
    pb.val(B[i]) = secret_input[i];//public_input[i];
    for (size_t j = 0; j < dimension; j++)
    	pb.val(A[i][j]) = public_input[i][j];//secret_input[i];
  }

  /* We just set the value of the input anchors,
   * now execute this function to function the gadget and fill in the other
   * anchors */
  //compute_inner_product.generate_r1cs_witness();
  for(int i=0;i<gadgets.size();i++){
    gadgets[i].generate_r1cs_witness();
    //sleep(1);
  }

  auto pi = pb.primary_input();
  auto ai = pb.auxiliary_input();
  /* If res is not zero, this function will crash complaining that
   * the R1CS constraint system is not satisfied. */
  auto proof = r1cs_ppzksnark_prover<ppT>(keypair.pk,pi,ai);

  /********************************************/
  /* Verifier: fill in only the public inputs */
  /********************************************/
  //for (size_t i = 0; i < dimension; i++)  // Actually, primary_input is a std::vector<FieldT>,
  //  pb.val(A[i]) = public_input[i];       // we can just cast or copy the public_input to get primary input,
  for (size_t i = 0; i < dimension; i++){
	  for (size_t j = 0; j < dimension; j++){
	    	pb.val(A[i][j]) = public_input[i][j];//secret_input[i];
	  }
  }
  pi = pb.primary_input();                // but let's pretend that we don't know the implementation details

  // pb_linear_combination_array<FieldT> tttt = pb_linear_combination_array<FieldT>(temp);
  // cout<<"temp!!!!!0:"<<tttt[0] <<"\n1:"<<tttt[1]<<endl;
  // cout<<"res!!!!!"<<pb_linear_combination<FieldT>(res)<<endl;
  // cout<<"ONE!!!"<<FieldT::one()<<endl;

  

  if(r1cs_ppzksnark_verifier_strong_IC<ppT>(keypair.vk,pi,proof)) {
    cout << "Verified! Congratulation!" << endl;
    
  } else {
    cout << "Failed to verify!" << endl;
  }

  // End of Zero Knowledge Proof
  std::clock_t c_end = std::clock();
  cout << "*************** End Time: " << c_end << " ***************" << endl;

  cout << "\nTABLE_HEIGHT: " << TABLE_HEIGHT << endl;
  cout << fixed << setprecision(2) << "CPU time used for zkSNARK: "
         <<  (c_end - c_start) / (float)CLOCKS_PER_SEC << " s" << endl;
  // cout << "CLOCKS_PER_SEC: " << CLOCKS_PER_SEC << endl;

  return 0;
}
