import java.util.ArrayList;
class MyClass{
    float x = 5;
}

class SimpleDouble{

    void testDouble(double x, MyClass myClass){
        float y;
        long z;
        x = x * 2.0;
        if(x > 200.0){
            y = (float)1.0;
            z = -1;
        }else{
            y = -(float)1.0;
            z = 1;
        }
        myClass.x = (float)(y * (int)z);

    }
}