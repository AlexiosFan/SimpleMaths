import java.io.InputStream;
import java.util.Arrays;
import java.util.Scanner;

public class Main {
    private static int length = 0;
    private static int height = 0;
    private static double[][] matrix;
    private static Scanner in = new Scanner(System.in);

    public static void main(String[] args) {
        System.out.println("This is a cheating program for calculating Gauss-elimination" +
                ", solution of Matrix formulae in form of Ax = b and Ax = 0");
        System.out.println("Please choose your needed calculation type\n" + "1 for Gauss-elminiation\n" +
                "2 for Formulae in form of Ax = b\n3 for Formulae in form of Ax = 0");
        int choice = 0;

        while (true) {
            try {
                choice = Integer.parseInt(in.nextLine());
                if (choice > 3 || choice <= 0) {
                    System.err.println("Please input a correct number.");
                } else {
                    break;
                }
            } catch (NumberFormatException exception) {
                System.err.println("Please input a correct number.");
            }
        }

        if (choice == 1) {
            initialize();
            matrix = Gauss.eliminate(matrix);
            printResult();
        }


        if (choice == 2) {
            initialize();
            double[] b = new double[height];
            System.out.println("Please input the vector b");
            try {
                String[] stringForm = in.nextLine().split(",");
                for (int j = 0; j < height; j++) {
                    b[j] = Integer.parseInt(stringForm[j]);
                }
            } catch (NumberFormatException exception) {
                System.err.println("Please rerun the programm and input a correct number");
            }

            b = Gauss.solve(matrix, b);
            printVector(b);
        }

        if(choice == 3) {
            System.out.println("You've chosen 3, for any matrix there exists a simple solution of 0 vector" +
                    ", this process can calculate a non-null vector.\n" +
                    "However, there are infinite many non-null vectors if there is one");
            initialize();
            double[] b = Gauss.solveSing(matrix);
            printVector(b);
        }
    }

    private static void initialize() {
        while (true) {
            try {
                System.out.println("Please input the number of lines of the Matrix");
                length = Integer.parseInt(in.nextLine());
                System.out.println("Please input the number of columns of the Matrix");
                height = Integer.parseInt(in.nextLine());
                break;
            } catch (NumberFormatException exception) {
                System.err.println("Please input a correct number.");
            }
        }

        System.out.println("Please input your Matrix in form of num,num,num... " +
                "according to the number of lines you have give");

        matrix = new double[length][height];

        try {
            for (int i = 0; i < length; i++) {
                String[] stringForm = in.nextLine().split(",");
                for (int j = 0; j < height; j++) {
                    matrix[i][j] = Integer.parseInt(stringForm[j]);
                }
            }
        } catch (NumberFormatException exception) {
            System.err.println("Please rerun the programm and input a correct number");
        }
    }

    private static void printResult() {
        System.out.println("The result comes as following in form of double");
        for (int i = 0; i < length; i++) {
            System.out.print("[" + matrix[i][0]);
            for (int j = 1; j < height; j++) {
                System.out.print(", " + matrix[i][j]);
            }
            System.out.println("]");

        }
    }

    private static void printVector(double[] vector) {
        System.out.println("The result comes as following in form of double");
        System.out.print("[" + vector[0]);
        for (int j = 1; j < height; j++) {
            System.out.print(", " + vector[j]);
        }
        System.out.println("]");
    }

}
