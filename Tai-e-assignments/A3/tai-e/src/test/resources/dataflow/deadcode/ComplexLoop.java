
class ComplexLoop{
    Myclass myclass;
    int unreachableSwitchBranch() {
        int x = 2, y = 1, z = 1;
        int s = 0;
        while(x >= z){
            switch (x) {
                case 1: y = 100; break; // unreachable branch
                case 2: y = 200;
                case 3: y = 300; break; // fall through
                default: y = 666; // unreachable branch
            }
            myclass.x = notDead() + 1;
//            x = x % 3 + 1;
//            if(z > 0)
//                s = y;
//            else
//                s = -y;
        }
        return s;
    }

    int notDead(){
        return 1;
    }
}

class Myclass{
    int x;
}