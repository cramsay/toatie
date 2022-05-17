library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity hetero_adders_tb is
  generic (NX1 : integer := 3;
           NX2 : integer := 2;
           NY1 : integer := 5;
           NY2 : integer := 2
           );
end entity;

architecture behavioural of hetero_adders_tb is

  component hetero_adders is
      port (
          x : in std_logic_vector (4 downto 0);
          y : in std_logic_vector (6 downto 0);
          res : out std_logic_vector (8 downto 0)
      );
  end component;

  function MAX (a : integer; b : integer) return integer is
    variable ans : integer;
  begin
    if a > b then
      ans := a;
    else
      ans := b;
    end if;
    return ans;
  end function MAX;

  signal xs : std_logic_vector (NX1+NX2-1 downto 0);
  signal ys : std_logic_vector (NY1+NY2-1 downto 0);
  signal res : std_logic_vector (MAX(NX1,NY1)+MAX(NX2, NY2)+1 downto 0);

  signal x1 : signed (NX1-1 downto 0);
  signal x2 : signed (NX2-1 downto 0);
  signal y1 : signed (NY1-1 downto 0);
  signal y2 : signed (NY2-1 downto 0);
  signal res1 : signed (MAX(NX1,NY1) downto 0);
  signal res2 : signed (MAX(NX2,NY2) downto 0);

begin

  uut : hetero_adders port map(
    x => xs,
    y => ys,
    res => res);

  xs <= std_logic_vector(x1 & x2);
  ys <= std_logic_vector(y1 & y2);
  res1 <= signed(res(MAX(NX1,NY1) + MAX(NX2, NY2)+1 downto MAX(NX2, NY2)+1));
  res2 <= signed(res(MAX(NX2, NY2) downto 0));

  process is
  begin
    for i in -2**(x1'length-1) to 2**(x1'length-1)-1 loop
      for j in -2**(x2'length-1) to 2**(x2'length-1)-1 loop
        for k in -2**(y1'length-1) to 2**(y1'length-1)-1 loop
          for l in -2**(y2'length-1) to 2**(y2'length-1)-1 loop
            x1 <= to_signed(i,x1'length);
            x2 <= to_signed(j,x2'length);
            y1 <= to_signed(k,y1'length);
            y2 <= to_signed(l,y2'length);
            wait for 2 ns;
            assert (std_logic_vector(res1) = std_logic_vector(to_signed(i+k,res1'length)))
              report "error" severity failure;
            assert (std_logic_vector(res2) = std_logic_vector(to_signed(j+l,res2'length)))
              report "error" severity failure;
          end loop;
        end loop;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
