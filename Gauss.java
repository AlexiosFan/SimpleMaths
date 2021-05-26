import java.util.Arrays;

public class Gauss {

    public static double[] backSubst(double[][] R, double[] b) {
       int length = b.length;
       double[] result = new double[length];
       double sum = 0;
       // die Summe von unteren Zeilen

       for(int i = length - 1; i >= 0; i--) {

           for(int j = i + 1; j < length; j++) {
               sum += result[j] * R[i][j];
           }
           //die Berechnung der Summe

           result[i] = (b[i] - sum)/R[i][i];
           sum = 0;
       }

       return result;
    }

    public static double[][] eliminate(double[][] input) {
        double[][] A = new double[input.length][input[0].length];
        int length = A.length;
        int height = A[0].length;

        for(int i = 0; i < input.length; i++) {
            for(int j = 0; j < input[0].length; j++) {
                A[i][j] = input[i][j];
            }
        }

        for(int i = 0; i < height; i++) {
            double[] temp = new double[length];
            int pos = -1;
            for (int j = i; j < length; j++) {
                if (Math.abs(temp[i]) < Math.abs(A[j][i])) {
                    temp = A[j];
                    pos = j;
                }
            }

            if (pos != -1) {
                temp = Arrays.copyOf(temp, length);
                for (int j = 0; j < length; j++) {
                    A[pos][j] = A[i][j];
                }
                for (int j = 0; j < length; j++) {
                    A[i][j] = temp[j];
                }
            }

            for (int j = i + 1; j < length; j++) {
                double multi = A[j][i] / A[i][i];
                for (int k = i; k < height; k++) {
                    A[j][k] -= A[i][k] * multi;
                }
            }
        }

        return A;
    }

    public static double[] solve(double[][] input, double[] inputR) {
        double[][] A = new double[input.length][input[0].length];
        int length = A.length;
        int height = A[0].length;
        double [] b = new double[inputR.length];

        for(int i = 0; i < input.length; i++) {
            for(int j = 0; j < input[0].length; j++) {
                A[i][j] = input[i][j];
            }
        }


        for(int i = 0; i < inputR.length; i++) {
            b[i] = inputR[i];
        }// kopiere die originale Matrix

        for(int i = 0; i < height; i++) {
            double[] temp = new double[length];
            int pos = -1;
            for (int j = i; j < length; j++) {
                if (Math.abs(temp[i]) < Math.abs(A[j][i])) {
                    temp = A[j];
                    pos = j;
                }
            }

            if (pos != -1) {
                temp = Arrays.copyOf(temp, length);
                for (int j = 0; j < length; j++) {
                    A[pos][j] = A[i][j];
                }
                for (int j = 0; j < length; j++) {
                    A[i][j] = temp[j];
                }
                double temp1 = b[i];
                b[i] = b[pos];
                b[pos] = temp1;

            }

            for (int j = i + 1; j < length; j++) {
                double multi = A[j][i] / A[i][i];
                for (int k = i; k < height; k++) {
                    A[j][k] -= A[i][k] * multi;
                }
                b[j] -= b[i] * multi;
            }
        }

        return backSubst(A, b);
    }

    public static double[] solveSing(double[][] input) {
        double[][] A = new double[input.length][input.length];

        int length = A.length;
        double[] result = new double[length];

        for(int i = 0; i < input.length; i++) {
            for(int j = 0; j < input.length; j++) {
                A[i][j] = input[i][j];
            }
        }

        for(int i = 0; i < length; i++) {
            double[] temp = new double[length];
            int pos = -1;
            for (int j = i; j < length; j++) {
                if(Math.abs(A[j][i]) < Math.pow(10, -9)) {
                    A[j][i] = 0;
                }

                if (Math.abs(temp[i]) < Math.abs(A[j][i])) {
                    temp = A[j];
                    pos = j;
                }
            }

            if (pos != -1) {
                temp = Arrays.copyOf(temp, length);
                for(int j = 0; j < length; j++) {
                    A[pos][j] = A[i][j];
                }
                for(int j = 0; j < length; j++) {
                    A[i][j] = temp[j];
                }
            }else {
                double [][] invertiervareTeilMatrix = new double[i][i];
                double[] v = new double[i];

                for(int k = 0; k < i; k++) {
                    for(int l = 0; l < i; l++) {
                        invertiervareTeilMatrix[k][l] = A[k][l];
                    }
                    v[k] = -A[k][i];
                }

                double[] subresult = solve(invertiervareTeilMatrix, v);

                for(int j = 0; j < subresult.length; j++) {
                    result[j] = subresult[j];
                }

                result[subresult.length] = 1;
                break;

            }

            for(int j = i + 1; j < length; j++) {
                double multi = A[j][i]/A[i][i];
                for(int k = i; k < length; k++) {
                    A[j][k] -= A[i][k] * multi;
                }
            }

        }

        return result;
    }

    public static double[] matrixVectorMult(double[][] A, double[] x) {
        int n = A.length;
        int m = x.length;

        double[] y = new double[n];

        for (int i = 0; i < n; i++) {
            y[i] = 0;
            for (int j = 0; j < m; j++) {
                y[i] += A[i][j] * x[j];
            }
        }

        return y;
    }
}
