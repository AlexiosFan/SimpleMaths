import java.util.Arrays;
import java.util.Scanner;

public class HammingCodes {
    //this is an implementation of encryption and decryption of (7, 4) Hamming-Codes
    public static void main(String[] args) {
        System.out.println("Welcome to Hamming decryption of (7, 4) with one error correcting function!\n" +
                "Please input your 4 codes in form of num,num,num...");

        Scanner in = new Scanner(System.in);
        HammingCodes decryptor = new HammingCodes();

        System.out.println("Please choose your mode\n 1 for the homework conversion\n 2 for normal encrytion\n" +
                " 3 for normal decryption");

        int mode = in.nextInt();

        if(mode == 1) {
            int[][] codes = new int[4][7];

            for (int i = 0; i < 4; i++) {
                codes[i] = Arrays.stream(in.nextLine().split(",")).mapToInt(e -> Integer.parseInt(e)).toArray();
            }

            for (int i = 0; i < 4; i++) {
                int checkResult = decryptor.parityCheck(codes[i]);
                if (checkResult == -1) {
                    continue;
                }
                codes[i][checkResult - 1] = 1 - codes[i][checkResult - 1];
            }

            for (int i = 0; i < 4; i++) {
                System.out.println("The following is the decrypted number.");
                Arrays.stream(decryptor.decrypt(codes[i])).forEach(System.out::print);
                System.out.println();
            }
        }

        if(mode == 2) {
            System.out.println("Please input the number to encrypt in form of num,num,num...");
            int[] code =  Arrays.stream(in.nextLine().split(",")).mapToInt(e -> Integer.parseInt(e)).toArray();

            System.out.println("Your encrypted result is:");
            Arrays.stream(decryptor.matrixMultiVector(decryptor.generatingMatrix(), code)).forEach(System.out::print);
        }

        if(mode == 3) {
            System.out.println("Please input the number to frcrypt in form of num,num,num...");
            int[] code =  Arrays.stream(in.nextLine().split(",")).mapToInt(e -> Integer.parseInt(e)).toArray();
            int checkResult = decryptor.parityCheck(code);

            if(checkResult != -1) {
                code[checkResult - 1] = 1 - code[checkResult - 1];
            }

            Arrays.stream(decryptor.matrixMultiVector(decryptor.generatingMatrix(), code)).forEach(System.out::print);
        }

    }

    public int parityCheck(int[] catchedCode)  {
        int[] checkResult = matrixMultiVector(getParityCheckMatrix(), catchedCode);
        int errorPos = -1;

        if(checkResult[0] == 1) {
            if(checkResult[1] == 1) {
                if(checkResult[2] == 1) {
                    errorPos = 4;
                } else {
                    errorPos = 3;
                }
            }else {
                errorPos = 5;
            }
        } else if(checkResult[1] == 1) {
            if(checkResult[2] == 1) {
                errorPos = 1;
            } else {
                errorPos = 6;
            }
        } else if(checkResult[2] == 1){
            errorPos = 7;
        }

        return errorPos;
    }


    private byte[][] generatingMatrix() {
        return new byte[][] {
                {1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1},{0,1,1,1},{1,0,1,1},{1,1,0,1}
        };
    }

    private byte[][] getParityCheckMatrix() {
        return new byte[][] {
                {0,1,1,1,1,0,0}, {1,0,1,1,0,1,0}, {1,1,0,1,0,0,1}
        };
    }

    private int[] matrixMultiVector(byte[][] matrix, int[] vector) {
        int[] result = new int[matrix.length];
        for(int i = 0; i < matrix.length; i++) {
            for(int j = 0; j < matrix[0].length; j++) {
                result[i] += vector[j] * matrix[i][j];
            }
        }

        for(int i : result) {
            i %= 2;
        }
        return result;
    }

    private int[] decrypt(int[] code) {
        byte[][] decrypter = new byte[][]{
            {1,0,0,0,0,0,0}, {0,1,0,0,0,0,0},{0,0,1,0,0,0,0},{0,0,0,1,0,0,0}
        };
        return matrixMultiVector(decrypter, code);
    }

    private int hammingWeight(int[] vector) {
        return Arrays.stream(vector).sum();
    }

    private int hammingDistance(byte[] vector0, byte[] vector1) {
        int result[] = new int[vector0.length];
        for(int i = 0; i < vector0.length; i++) {
            result[i] = Math.abs(vector1[i] - vector0[i]);
        }
        return hammingWeight(result);
    }
}
